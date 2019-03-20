{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
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
import Control.Monad (join, liftM2)
import Crypto.Hash (Digest, HashAlgorithm, hashlazy)
import Crypto.Hash.Algorithms (SHA3_256)
import Data.Bifunctor (Bifunctor(..))
import Data.Binary (Binary, encode)
import Data.ByteArray (convert)
import Data.ByteString.Char8 (ByteString)
import Data.Finite (Finite, packFinite, separateSum, weakenN)
import Data.Foldable (Foldable(..))
import Data.Functor.Identity (Identity(..))
import Data.List (sortBy)
import Data.Maybe (isJust)
import Data.Ord (comparing)
import Data.Proxy (Proxy(..))
-- import Data.Reflection (Reifies(..), reifyNat)
import Data.Type.Bool
import Data.Vector.Sized (Vector)
import GHC.TypeLits

import qualified Crypto.Hash as H (hash)
import qualified Data.Vector as V
import qualified Data.Vector.Sized as S

import Data.Array (Array, Ix)
import Data.Hashable (Hashable)
import Data.HashMap.Strict (HashMap)
import Data.IntMap (IntMap)
import Data.Map (Map)
import Data.Sequence (Seq)
import Data.Tree (Tree)

-- Crypto.Hash instances are kinda restrictive, so we redefine here to be more general
hash :: (Binary v, HashAlgorithm a) => v -> Digest a
hash = hashlazy . encode

-- Class Definition
-- {{{

class Binary (IxValue t) => Authenticate t where
  type HashFor  t :: *
  type ProofFor t :: *
  type Access   t :: * -> *

  retrieve :: Index t -> t -> (Access t (IxValue t), ProofFor t)
  digest :: t -> HashFor t
  verify :: Proxy t -> HashFor t -> Access t (IxValue t) -> ProofFor t -> Bool

retrieved :: Authenticate t => Proxy t -> HashFor t -> Access t (IxValue t) -> ProofFor t -> Bool
retrieved = verify

-- Writes aren't authenticated because you just read before/after and make sure the same proof holds
-- for both
replaced :: Authenticate t => Proxy t -> (HashFor t, Access t (IxValue t))
                                      -> (HashFor t, Access t (IxValue t)) -> ProofFor t -> Bool
replaced t old new p = let check x = uncurry (verify t) x p in check old && check new

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

topHash :: (Binary v, HashAlgorithm a) => MT n a v -> Digest a
topHash (Root (hash -> h)) = h
topHash (Fork _ _      h)  = h

hashCons :: HashAlgorithm a => Digest a -> Digest a -> Digest a
hashCons x y = H.hash (convert x <> convert y :: ByteString)

mkFork :: (Binary v, HashAlgorithm a) => MT (d - 1) a v -> MT (d - 1) a v -> MT d a v
mkFork l r = Fork l r $ hashCons (topHash l) (topHash r)

data MerklePath (d :: Nat) a where
  Z ::                              MerklePath 0 a
  L :: a -> MerklePath (n - 1) a -> MerklePath n a
  R :: a -> MerklePath (n - 1) a -> MerklePath n a

deriving instance Eq a => Eq (MerklePath n a)
deriving instance Functor (MerklePath n)

type instance Index    (MerkleTree d a v) = MerklePath d ()

type MP = MerklePath

{-# COMPLETE Z #-}
{-# COMPLETE L, R #-}

instance (Binary v, HashAlgorithm a) => Authenticate (MT 0 a v) where
  type HashFor  (MT 0 a v) = Digest a
  type ProofFor (MT 0 a v) = MP 0 (Digest a)
  type Access   (MT 0 a v) = Identity

  retrieve Z (Root v) = (Identity v, Z)
  digest = topHash
  verify _ h v _ = h == hash v

foldPath :: (a -> a -> a) -> a -> MerklePath n a -> a
foldPath _ i Z       = i
foldPath f i (L a n) = f (foldPath f i n) a
foldPath f i (R a n) = f a                (foldPath f i n)

type Succ n m = (n ~ (m - 1), 1 <= m)

instance (Binary v, HashAlgorithm a, Succ n m, Authenticate (MT n a v)) => Authenticate (MT m a v) where
  type HashFor  (MT m a v) = Digest a
  type ProofFor (MT m a v) = MP m (Digest a)
  type Access   (MT m a v) = Identity

  retrieve (L _ n)   (Fork l r _) = L (topHash r) <$> retrieve n l
  retrieve (R _ n)   (Fork l r _) = R (topHash l) <$> retrieve n r
  digest = topHash
  verify _ d v = (== d) . foldPath hashCons (hash v)

-- }}}

-- Right now, I can't figure out polymorphism over Merkle tree depth in instance defintions. Hence,
-- the below is a quick "blinded"/non-dependently-typed Merkle tree impl. I think perhaps
-- Data.Reflection could work instead? Regardless, this is works for the time being (:\)
-- {{{

data BlindMP a = BZ | BL a (BMP a) | BR a (BMP a) deriving Show

type BMP a = BlindMP a

data BlindMT a x = BRoot x | BFork (BMT a x) (BMT a x) (Digest a)

type BMT = BlindMT

btopHash :: (Binary x, HashAlgorithm a) => BMT a x -> Digest a
btopHash (BRoot x)     = hash x
btopHash (BFork _ _ h) = h

bmtOf :: Provable a t v => t v -> BMT a (Maybe (Index (t v), IxValue (t v)))
bmtOf t = go . fmap Just . sortBy (comparing fst) $ t ^@.. ifolded where
  go []  = BRoot Nothing
  go [x] = BRoot x
  go l  = BFork lf rf $ hashCons (btopHash lf) (btopHash rf) where
    padTo = 2 ^ (ceiling (logBase 2 . fromIntegral $ length l :: Float) - 1 :: Int)
    lf  = go $ take padTo l 
    rf  = go $ drop padTo l ++ replicate (2 * padTo - length l) Nothing

bmpOf :: (FoldableWithIndex (Index (t v)) t, Ord (Index (t v)))
      => Index (t v) -> t v -> Maybe (BMP ())
bmpOf k t = ifind (const . (k ==)) t *> go (length t) (length $ t ^@.. ifolded . indices (< k)) where
  go l i | l <= i           = Nothing
         | (l, i) == (1, 0) = Just BZ
         | otherwise = let l' = (l + 1) `div` 2; n = go l' in if i < l' then BL () <$> n i
                                                                        else BR () <$> n (i - l')

bfoldPath :: (a -> a -> a) -> a -> BMP a -> a
bfoldPath _ i BZ       = i
bfoldPath f i (BL a n) = f (bfoldPath f i n) a
bfoldPath f i (BR a n) = f a                 (bfoldPath f i n)

-- }}}

-- Machinery for DerivingVia
-- {{{

newtype Auth a t v = Auth (t v) deriving Functor

type instance Index    (Auth a t v) = Index (t v)
type instance IxValue  (Auth a t v) = v

data AtIndex i v = AtIndex i (Maybe v) deriving Show

type Provable a t v = ( Binary (Index (t v)), Binary v, HashAlgorithm a, Ord (Index (t v))
                      , Ixed (t v), FoldableWithIndex (Index (t v)) t, v ~ IxValue (t v))

instance Provable a t v => Authenticate (Auth a t v) where
  -- Right now, our digest includes a list of keys, since otherwise we can't verify when the prover
  -- says a key doesn't have a value. This is kinda ugly and I'd like to not do it, but idk how.
  -- W2B efficient exclusion proofs? Currently though, HashFor keeps a rule for key inclusion around.
  -- This can be omitted trivially (_1 .~ const True) in settings where we aren't worried about fake
  -- negative results
  type HashFor  (Auth a t v) = (Index (t v) -> Bool, Digest a)
  type ProofFor (Auth a t v) = BMP (Digest a)
  type Access   (Auth a t v) = AtIndex (Index (t v))

  retrieve k (Auth t) = first (AtIndex k) $ case bmpOf k t of Nothing  -> (Nothing, BZ)
                                                              (Just p) -> go p $ bmtOf @a t
    where go p m = case (p, m) of ( BZ,      BRoot v)     -> (snd <$> v, BZ)
                                  ((BL _ n), BFork l r _) -> BL (btopHash r) <$> go n l
                                  ((BR _ n), BFork l r _) -> BR (btopHash l) <$> go n r
                                  _                       -> (Nothing, BZ)
  digest (Auth t) = (\k -> isJust $ t ^? ifolded . index k, btopHash $ bmtOf t)
  verify _ (p, d) (AtIndex i m) t = d == bfoldPath hashCons (hash $ fmap (i,) m) t || not (p i)

deriving via Auth SHA3_256 (HashMap k) v instance (Hashable k, Ord k, Binary k, Binary v) => Authenticate (HashMap k v)
deriving via Auth SHA3_256 (Map     k) v instance (Ord k, Binary k, Binary v) =>             Authenticate (Map     k v)
deriving via Auth SHA3_256 IntMap      v instance Binary v =>                                Authenticate (IntMap    v)
deriving via Auth SHA3_256 Maybe       v instance Binary v =>                                Authenticate (Maybe     v)
deriving via Auth SHA3_256 []          v instance Binary v =>                                Authenticate           [v]
deriving via Auth SHA3_256 (Array i)   v instance (Binary i, Binary v, Ix i) =>              Authenticate (Array   i v)
deriving via Auth SHA3_256 Seq         v instance Binary v =>                                Authenticate (Seq       v)
deriving via Auth SHA3_256 Tree        v instance Binary v =>                                Authenticate (Tree      v)
deriving via Auth SHA3_256 V.Vector    v instance Binary v =>                                Authenticate (V.Vector  v)

-- }}}

-- /interesting stuff. Below is mostly experiments and miscellania

-- Blinding and unblinding

blindMT :: MerkleTree d a x -> BMT a x
blindMT (Root a) = BRoot a
blindMT (Fork l r h) = BFork (blindMT l) (blindMT r) h

class UnblindMT n where
  unblindMT :: BMT a x -> Maybe (MT n a x)

instance UnblindMT 0 where
  unblindMT (BRoot a) = Just $ Root a
  unblindMT _         = Nothing

instance (n ~ (m - 1), UnblindMT n) => UnblindMT m where
  unblindMT (BFork l r h) = liftM2 (\x y -> Fork x y h) (unblindMT l) (unblindMT r)
  unblindMT _             = Nothing

blindMP :: MerklePath n a -> BMP a
blindMP  Z      = BZ
blindMP (L a n) = BL a $ blindMP n
blindMP (R a n) = BR a $ blindMP n

class UnblindMP n where
  unblindMP :: BMP a -> Maybe (MP n a)

instance UnblindMP 0 where
  unblindMP BZ = Just Z
  unblindMP _  = Nothing

instance (n ~ (m - 1), UnblindMP n) => UnblindMP m where
  unblindMP (BL a n) = Just . L a =<< unblindMP n
  unblindMP (BR a n) = Just . R a =<< unblindMP n
  unblindMP  BZ      = Nothing

-- Attempts to get dependently-typed Merkle trees to work in my Authenticated Auth instance

type LeafLen l = 2 ^ (MTDepth l - 1)
type MTDepth l = If (2 <=? l) (Log2 (l - 1) + 1) 0

type LL l = LeafLen l
type MD l = MTDepth l
type Split k l = ( KnownNat k, KnownNat (LL l), (LL l + LL l) ~ (l + k)
                 , MD (LL l) ~ (MD l - 1), (l <=? l + k) ~ 'True)

class Merkleize (l :: Nat) where
  merkleizeV :: (Binary x, HashAlgorithm a) => Vector l x -> MerkleTree (MTDepth l) a (Maybe x)
  merkleizeI :: Finite l -> MerklePath (MTDepth l) ()

instance Merkleize 0 where
  merkleizeV = const $ Root Nothing
  merkleizeI = const Z

instance {-# OVERLAPPING #-} Merkleize 1 where
  merkleizeV = Root . Just . S.head
  merkleizeI = const Z

instance (Split k m, Merkleize (LeafLen m), m ~ (n + 2)) => Merkleize m where
  merkleizeV = uncurry mkFork . join bimap (fmap join . merkleizeV) . halves where
    halves :: Split k l => Vector l x -> (Vector (LL l) (Maybe x), Vector (LL l) (Maybe x))
    halves v = S.splitAt $ fmap Just v S.++ S.replicate Nothing
  merkleizeI = either (L ()) (R ()) . join bimap merkleizeI . halves where
    halves :: Split k l => Finite l -> Either (Finite (LeafLen l)) (Finite (LeafLen l))
    halves = separateSum . weakenN

asMerkleF :: forall x a i t m. (Binary x, HashAlgorithm a, FoldableWithIndex i t, KnownNat m, Merkleize m, Ord i)
          => Proxy m -> t x -> Maybe (MerkleTree (MTDepth m) a (Maybe x))
asMerkleF _ v = fmap merkleizeV (S.fromList $ toList inorder :: Maybe (Vector m x)) where
  inorder = fmap snd . sortBy (comparing fst) $ v ^@.. ifolded

asMerkleI :: forall i t l x. (FoldableWithIndex i t, KnownNat l, Merkleize l, Ord i)
          => Proxy l -> t x -> i -> Maybe (MerklePath (MTDepth l) ())
asMerkleI _ t i = ifind (const . (i ==)) t *> fmap merkleizeI
  (packFinite . fromIntegral . length $ t ^@.. ifolded . indices (< i) :: Maybe (Finite l))
