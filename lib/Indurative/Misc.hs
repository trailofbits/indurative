{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Indurative.Misc where

import Indurative

import Control.Lens
import Control.Monad (join)
import Crypto.Hash (HashAlgorithm)
import Data.Binary
import Data.Finite (Finite, packFinite, separateSum, weakenN)
import Data.Foldable (toList)
import Data.List (sortBy)
import Data.Ord (comparing)
import Data.Proxy (Proxy)
import Data.Type.Bool
import Data.Vector.Sized (Vector)
import GHC.TypeLits

import qualified Data.Vector.Sized as S

blindMT :: MerkleTree d a x -> BMT a x
blindMT (Root a) = BRoot a
blindMT (Fork l r h) = BFork (blindMT l) (blindMT r) h

class UnblindMT n where
  unblindMT :: BMT a x -> Maybe (MT n a x)

instance UnblindMT 0 where
  unblindMT (BRoot a) = Just $ Root a
  unblindMT _         = Nothing

instance (n ~ (m - 1), UnblindMT n) => UnblindMT m where
  unblindMT (BFork l r h) = (\x y -> Fork x y h) <$> unblindMT l <*> unblindMT r
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

type LeafLen l = 2 ^ (MTDepth l - 1)
type MTDepth l = If (2 <=? l) (Log2 (l - 1) + 1) 0

type LL l = LeafLen l
type MD l = MTDepth l
type Split k l = ( KnownNat k, KnownNat (LL l), (LL l + LL l) ~ (l + k)
                 , MD (LL l) ~ (MD l - 1), (l <=? l + k) ~ 'True)

class KnownNat l => Merkleize (l :: Nat) where
  merkleizeV :: (Binary x, HashAlgorithm a) => Vector l x -> MerkleTree (MTDepth l) a (Maybe x)
  merkleizeI :: Finite l -> MerklePath (MTDepth l) ()

instance Merkleize 0 where
  merkleizeV = const $ Root Nothing
  merkleizeI = const Z

instance Merkleize 1 where
  merkleizeV = Root . Just . S.head
  merkleizeI = const Z

instance (Split k m, KnownNat m, Merkleize (LeafLen m), 2 <= m) => Merkleize m where
  merkleizeV = uncurry mkFork . join bimap (fmap join . merkleizeV) . halves where
    halves :: Split k l => Vector l x -> (Vector (LL l) (Maybe x), Vector (LL l) (Maybe x))
    halves v = S.splitAt $ fmap Just v S.++ S.replicate Nothing
  merkleizeI = either (L ()) (R ()) . join bimap merkleizeI . halves where
    halves :: Split k l => Finite l -> Either (Finite (LeafLen l)) (Finite (LeafLen l))
    halves = separateSum . weakenN

asMerkleF :: forall x a i t m. (Binary x, HashAlgorithm a, FoldableWithIndex i t, Merkleize m, Ord i)
          => Proxy m -> t x -> Maybe (MerkleTree (MTDepth m) a (Maybe x))
asMerkleF _ v = merkleizeV <$> (S.fromList $ toList inorder :: Maybe (Vector m x)) where
  inorder = fmap snd . sortBy (comparing fst) $ v ^@.. ifolded

asMerkleI :: forall i t l x. (FoldableWithIndex i t, KnownNat l, Merkleize l, Ord i)
          => Proxy l -> t x -> i -> Maybe (MerklePath (MTDepth l) ())
asMerkleI _ t i = ifind (const . (i ==)) t *> fmap merkleizeI
  (packFinite . fromIntegral $ lengthOf (ifolded . indices (< i)) t :: Maybe (Finite l))
