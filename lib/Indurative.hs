{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Indurative where

import Control.Lens
import Control.Monad (void)
import Crypto.Hash (Digest, HashAlgorithm, hashlazy)
import Data.Binary (Binary, encode)
import Data.ByteArray (Bytes, convert)
import Data.List (sortBy)
import Data.Ord (comparing)
import Data.Proxy (Proxy(..))
import GHC.TypeLits

import qualified Crypto.Hash as H (hash)

-- Crypto.Hash instances are kinda restrictive, so we redefine here to be more general
hash :: (Binary v, HashAlgorithm a) => v -> Digest a
hash = hashlazy . encode

-- Class Definition
-- {{{

class Authenticate t where
  type HashFor  t :: *
  type ProofFor t :: *
  type Access   t :: * -> *

  retrieve :: Index t -> t -> (Access t (IxValue t), ProofFor t)
  digest :: t -> HashFor t
  verify :: Proxy t -> Index t -> HashFor t -> Access t (IxValue t) -> ProofFor t -> Bool

retrieved :: Authenticate t => Proxy t -> Index t -> HashFor t -> Access t (IxValue t) -> ProofFor t -> Bool
retrieved = verify

-- Writes aren't authenticated because you just read before/after and make sure the same proof holds
-- for both
replaced :: Authenticate t
         => Proxy t
         -> Index t
         -> (HashFor t, Access t (IxValue t))
         -> (HashFor t, Access t (IxValue t))
         -> ProofFor t
         -> Bool
replaced t k old new p = let check x = uncurry (verify t k) x p in check old && check new

--}}}

-- Dependently typed Merkle trees and paths through them
-- {{{

data MerkleTree (d :: Nat) a v where
  Root :: v                                                            -> MerkleTree 0 a v
  Fork :: MerkleTree (d - 1) a v -> MerkleTree (d - 1) a v -> Digest a -> MerkleTree d a v

deriving instance Eq v => Eq (MerkleTree n a v)
deriving instance Functor (MerkleTree n a)
deriving instance Show v => Show (MerkleTree n a v)

type instance IxValue (MerkleTree d a v) = v

type MT = MerkleTree

{-# COMPLETE Fork #-}
{-# COMPLETE Root #-}

topHash :: (Binary v, HashAlgorithm a) => MerkleTree n a v -> Digest a
topHash (Root (hash -> h)) = h
topHash (Fork _ _      h)  = h

hashCons :: HashAlgorithm a => Digest a -> Digest a -> Digest a
hashCons x y = H.hash (convert x <> convert y :: Bytes)

mkFork :: (Binary v, HashAlgorithm a) => MT (d - 1) a v -> MT (d - 1) a v -> MT d a v
mkFork l r = Fork l r $ hashCons (topHash l) (topHash r)

data MerklePath (d :: Nat) a where
  Z ::                              MerklePath 0 a
  L :: a -> MerklePath (n - 1) a -> MerklePath n a
  R :: a -> MerklePath (n - 1) a -> MerklePath n a

deriving instance Eq a => Eq (MerklePath n a)
deriving instance Functor (MerklePath n)

type instance Index (MerkleTree d a v) = MerklePath d ()

type MP = MerklePath

{-# COMPLETE Z #-}
{-# COMPLETE L, R #-}

instance (Binary v, HashAlgorithm a) => Authenticate (MerkleTree 0 a v) where
  type HashFor  (MT 0 a v) = Digest a
  type ProofFor (MT 0 a v) = MP 0 (Digest a)
  type Access   (MT 0 a v) = Identity

  retrieve Z (Root v) = (Identity v, Z)
  digest = topHash
  verify _ _ h v _ = h == hash v

foldPath :: (a -> a -> a) -> a -> MerklePath n a -> a
foldPath _ i Z       = i
foldPath f i (L a n) = f (foldPath f i n) a
foldPath f i (R a n) = f a                (foldPath f i n)

instance (Binary v, HashAlgorithm a, n ~ (m + 1), m ~ (n - 1), Authenticate (MerkleTree m a v)) =>
  Authenticate (MerkleTree n a v) where
    type HashFor  (MerkleTree n a v) = Digest a
    type ProofFor (MerkleTree n a v) = MP n (Digest a)
    type Access   (MerkleTree n a v) = Identity
  
    retrieve (L _ n)   (Fork l r _) = L (topHash r) <$> retrieve n l
    retrieve (R _ n)   (Fork l r _) = R (topHash l) <$> retrieve n r
    digest = topHash
    verify _ mp d v p = d == foldPath hashCons (hash v) p && void p == mp

-- }}}

-- Right now, I can't figure out polymorphism over Merkle tree depth in instance defintions. Hence,
-- the below is a quick "blinded"/non-dependently-typed Merkle tree impl. I think perhaps
-- Data.Reflection could work instead? Regardless, this is works for the time being (:\)
-- {{{

data BlindMP a = BZ | BL a (BMP a) | BR a (BMP a) deriving (Eq, Functor, Show)

data BlindMT a x = BRoot x | BFork (BMT a x) (BMT a x) (Digest a) deriving Show

type BMP a = BlindMP a
type BMT = BlindMT

btopHash :: (Binary x, HashAlgorithm a) => BlindMT a x -> Digest a
btopHash (BRoot (hash -> h)) = h
btopHash (BFork _ _      h)  = h

nextPower2 :: Integral a => a -> a
nextPower2 n = if n == 0 then 1 else 2 ^ (ceiling (logBase 2 $ fromIntegral n :: Float) :: Int)

{-
bmtOf :: Provable a t v => t v -> BlindMT a (Maybe (Index (t v), IxValue (t v)))
bmtOf t = go . fmap Just . sortBy (comparing fst) $ itoList t where
  go []  = BRoot Nothing
  go [x] = BRoot x
  go l   = let padTo = div (nextPower2 $ length l) 2
               rf    = go $ drop padTo l ++ replicate (2 * padTo - length l) Nothing
               lf    = go $ take padTo l in BFork lf rf $ hashCons (btopHash lf) (btopHash rf)

bmpOf :: Int -> Int -> Maybe (BMP ())
bmpOf = go . nextPower2 where go l i | l <= i           = Nothing
                                     | (l, i) == (1, 0) = Just BZ
                                     | otherwise        = let l' = l `div` 2 in
                                         if i < l' then BL () <$> go l' i else BR () <$> go l' (i - l')

bfoldPath :: (a -> a -> a) -> a -> BMP a -> a
bfoldPath _ i BZ       = i
bfoldPath f i (BL a n) = f (bfoldPath f i n) a
bfoldPath f i (BR a n) = f a                 (bfoldPath f i n)

-- }}}

-- Machinery for DerivingVia
-- {{{

newtype Auth a t v = Auth (t v) deriving Functor

type instance Index   (Auth a t v) = Index (t v)
type instance IxValue (Auth a t v) = IxValue (t v)

type Provable a t v = ( Binary (Index (t v)), Binary v, HashAlgorithm a, Ord (Index (t v))
                      , Ixed (t v), FoldableWithIndex (Index (t v)) t, v ~ IxValue (t v))

instance Provable a t v => Authenticate (Auth a t v) where
  -- Right now, our digest includes a list of keys, since otherwise we can't verify when the prover
  -- says a key doesn't have a value. This is kinda ugly and I'd like to not do it, but idk how.
  -- W2B efficient exclusion proofs? Currently though, HashFor keeps a rule for key inclusion around.
  -- This can be omitted trivially (_1 .~ const True) in settings where we aren't worried about fake
  -- negative results
  type HashFor  (Auth a t v) = (Index (t v) -> Bool, Digest a)
  type ProofFor (Auth a t v) = (Int, Int, BMP (Digest a))
  type Access   (Auth a t v) = Maybe

  retrieve k (Auth t) = let (l, il) = (length t, lengthOf (ifolded . indices (< k)) t) in
    fmap (l, il,) <$> maybe (Nothing, BZ) (go $ bmtOf @a t) $ bmpOf l il where
      go m p = case (m, p) of (BRoot v    , BZ)     -> (snd <$> v, BZ)
                              (BFork l r _, BL _ n) -> BL (btopHash r) <$> go l n
                              (BFork l r _, BR _ n) -> BR (btopHash l) <$> go r n
                              _                     -> (Nothing, BZ)
  digest (Auth t) = (flip has t . ix, btopHash $ bmtOf t)
  verify _ k (p, d) v (l, i, t) = bmpOf l i == Just (void t)
                               && d == bfoldPath hashCons (hash $ (k,) <$> v) t || not (p k)

-- I don't want to actually ship all these instances, but they should compile!
deriving via Auth SHA3_256 (HashMap k) v instance (Hashable k, Ord k, Binary k, Binary v) => Authenticate (HashMap k v)
deriving via Auth SHA3_256 (Map     k) v instance (Ord k, Binary k, Binary v) =>             Authenticate (Map     k v)
deriving via Auth SHA3_256 IntMap      v instance Binary v =>                                Authenticate (IntMap    v)
deriving via Auth SHA3_256 Maybe       v instance Binary v =>                                Authenticate (Maybe     v)
deriving via Auth SHA3_256 []          v instance Binary v =>                                Authenticate           [v]
deriving via Auth SHA3_256 (Array i)   v instance (Binary i, Binary v, Ix i) =>              Authenticate (Array   i v)
deriving via Auth SHA3_256 Seq         v instance Binary v =>                                Authenticate (Seq       v)
deriving via Auth SHA3_256 Tree        v instance Binary v =>                                Authenticate (Tree      v)
deriving via Auth SHA3_256 V.Vector    v instance Binary v =>                                Authenticate (V.Vector  v)
-}

-- }}}
