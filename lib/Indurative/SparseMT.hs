{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Indurative.SparseMT where

import Indurative

import Control.Lens
import Control.Monad (join)
import Crypto.Hash (Digest, HashAlgorithm)
import Data.Bifunctor (Bifunctor(..))
import Data.Binary (Binary)
import Data.Bits (Bits(..))
import Data.Bits.ByteString ()
import Data.ByteString (ByteString)
import Data.Proxy (Proxy(..))
import Data.List (find, foldl', sortBy)
import Data.Maybe (fromMaybe)
import Data.Ord (comparing)
import GHC.Generics (Generic)

import qualified Data.ByteArray  as BA
import qualified Data.ByteString as BS

data EmptyNode = EmptyNode deriving (Binary, Generic)

nullHashes :: HashAlgorithm a => [Digest a]
nullHashes = iterate (join hashCons) $ hash EmptyNode

hLen :: forall a. HashAlgorithm a => Proxy a -> Int
hLen = const . (8 *) . BA.length $ head (nullHashes @a)

hOne :: HashAlgorithm a => Proxy a -> ByteString
hOne p = BS.pack $ replicate (hLen p `div` 8 - 1) 0 |> 1

bsHash :: forall a x. (Binary x, HashAlgorithm a) => Proxy a -> x -> ByteString
bsHash = const $ BS.pack . BA.unpack . hash @_ @a

-- First arg is ix, then ixed hash, then not-ixed hash
debranch :: HashAlgorithm a => ByteString -> Digest a -> Digest a -> Digest a
debranch i = if testBit i 0 then flip hashCons else hashCons

type SparseNode a = (ByteString, Digest a)
type SparsePath a = [(Int, Digest a)]

up :: forall a. HashAlgorithm a => [SparseNode a] -> Digest a -> [SparseNode a]
up []                  _ = []
up [(i, x)]            h = [(shiftR i 1, debranch i x h)]
-- NOTE: we should be able to just check if @setBit i 0 == j@, but the bits-bytestring instance
-- is broken there, and truncates the output to one @Char8@. Dunno why.
up ((i,x) : (j,y) : l) h = if i `xor` j == hOne (Proxy @a) then (shiftR i 1, hashCons x y) : up l h
                                                           else up [(i,x)] h ++ up ((j,y) : l) h

climb :: forall a. HashAlgorithm a => [SparseNode a] -> Digest a
climb [] = nullHashes !! hLen (Proxy @a)
climb l  = snd . head . foldl' up l $ take (hLen $ Proxy @a) nullHashes

zig :: forall a. HashAlgorithm a => [SparseNode a] -> SparseNode a -> SparsePath a
zig = go 0 where 
  go :: Int -> [SparseNode a] -> SparseNode a -> SparsePath a
  go h l (i, x) = let nullHash = nullHashes !! h in if h == hLen (Proxy @a) then [] else
    let next = go (h + 1) (up l nullHash) . (shiftR i 1,) . debranch i x in
    case find ((== i) . xor (hOne $ Proxy @a) . fst) l of
      Nothing       ->            next nullHash
      Just (_, res) -> (h, res) : next res

-- Reference first, then test
check :: forall a. HashAlgorithm a => Digest a -> SparseNode a -> SparsePath a -> Bool
check t = go 0 where
  go n x      [] = (t ==) . snd . head . foldl' up [x] . drop n $ take (hLen $ Proxy @a) nullHashes
  go n (i, r) l@((h, x) : hs) = go (n + 1) (shiftR i 1, debranch i r h') l' where
     (h', l') = if n == h then (x, hs) else (nullHashes !! n, l)

baseLayer :: forall a k t v. (Binary k, Binary v, FoldableWithIndex k t, HashAlgorithm a)
          => t v -> [SparseNode a]
baseLayer = sortBy (comparing fst) . fmap (bimap (bsHash $ Proxy @a) hash) . itoList

sparseHash :: (Binary k, Binary v, FoldableWithIndex k t, HashAlgorithm a) => t v -> Digest a
sparseHash = climb . baseLayer

sparseGet :: forall a k t v. (Binary k, Binary v, Eq k, FoldableWithIndex k t, HashAlgorithm a)
          => k -> t v -> (Maybe v, SparsePath a)
sparseGet i l = let res = snd <$> ifind (\j _ -> j == i) l in
  (res,) . zig (baseLayer l) . (bsHash (Proxy @a) i,) . fromMaybe (head nullHashes) $ hash <$> res

sparseCheck :: forall a k v. (Binary k, Binary v, HashAlgorithm a)
            => k -> Digest a -> Maybe v -> SparsePath a -> Bool
sparseCheck i h = check h . (bsHash (Proxy @a) i,) . maybe (head nullHashes) (hash @_ @a)

newtype Auth a t v = Auth (t v) deriving Functor
type instance Index   (Auth a t v) = Index (t v)
type instance IxValue (Auth a t v) = IxValue (t v)

type Provable a t v = ( Binary (Index (t v)), Binary v, HashAlgorithm a, Eq (Index (t v))
                      , Ixed (t v), FoldableWithIndex (Index (t v)) t, v ~ IxValue (t v))

instance Provable a t v => Authenticate (Auth a t v) where
  type HashFor  (Auth a t v) = Digest a
  type ProofFor (Auth a t v) = SparsePath a
  type Access   (Auth a t v) = Maybe

  retrieve k (Auth t) = sparseGet k t
  digest (Auth t) = sparseHash t
  verify _ = sparseCheck
