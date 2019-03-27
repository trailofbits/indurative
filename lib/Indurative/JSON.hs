{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Indurative.JSON where

import Control.Lens
import Control.Monad (join)
import Crypto.Hash (Digest, HashAlgorithm, SHA3_256)
import Data.Aeson
import Data.Aeson.Lens
import Data.List (sortBy)
import Data.Maybe (isJust)
import Data.Ord (comparing)
import Data.Text (Text)
import Indurative

data JSONPath a = Here | AtKey Text a (JSONPath a) | AtIx Int a (JSONPath a) deriving (Eq, Functor, Ord, Show)

tOf :: JSONPath a -> Traversal' Value Value
tOf Here          = ignored
tOf (AtKey k _ _) = key k
tOf (AtIx  i _ _) = nth i

nextPath :: JSONPath a -> JSONPath a
nextPath Here          = Here
nextPath (AtKey _ _ m) = m
nextPath (AtIx  _ _ m) = m

withStartOf :: JSONPath a -> b -> JSONPath b -> JSONPath b
withStartOf Here          _ _ = Here
withStartOf (AtKey k _ _) b p = AtKey k b p
withStartOf (AtIx  k _ _) b p = AtIx  k b p

jhash :: HashAlgorithm a => Value -> Digest a
jhash = hash . encode

jTopHash :: HashAlgorithm a => Value -> Digest a
jTopHash v@(Object (null -> empty)) = if empty then hash ("empty object" :: Text) else
  foldr1 hashCons $ jTopHash . snd <$> sortBy (comparing fst) (v ^@.. members)
jTopHash v@(Array (null -> empty)) = if empty then hash ("empty array" :: Text) else
  foldr1 hashCons $ jTopHash . snd <$> sortBy (comparing fst) (v ^@.. values)
jTopHash v = jhash v

jFoldPath :: (a -> a -> a) -> a -> JSONPath ([a], [a]) -> a
jFoldPath _ i Here               = i
jFoldPath f i (AtKey _ (l, r) n) = foldr1 f (l ++ [jFoldPath f i n] ++ r)
jFoldPath f i (AtIx  _ (l, r) n) = foldr1 f (l ++ [jFoldPath f i n] ++ r)

data IxedJSON a = IxedJSON Value deriving Show

ijMap :: (Value -> Value) -> IxedJSON a -> IxedJSON a
ijMap f (IxedJSON a) = IxedJSON $ f a

type instance Index   (IxedJSON a) = JSONPath ()
type instance IxValue (IxedJSON a) = a

others :: JSONPath a -> Value -> ([Value], [Value])
others p v = let othersWith :: Ord i => IndexedTraversal' i Value Value -> i -> ([Value], [Value])
                 othersWith l i = (those l (< i), those l (> i))
                 those :: Ord i => IndexedTraversal' i Value Value -> (i -> Bool) -> [Value]
                 those l f = fmap snd . sortBy (comparing fst) $ v ^@.. l . indices f in
  case p of Here -> mempty
            (AtKey k _ _) -> othersWith members k
            (AtIx  i _ _) -> othersWith values i

instance (FromJSON a, ToJSON a) => Ixed (IxedJSON a) where
  ix Here f ij@(IxedJSON j) = case fromJSON j of
    Error _   -> pure ij
    Success v -> IxedJSON . toJSON <$> f v
  ix i f ij@(IxedJSON j) = let inJ = ijMap $ \v -> j & tOf i .~ v in
    maybe (pure ij) (fmap inJ) $ ix (nextPath i) f . IxedJSON <$> j ^? tOf i

instance (FromJSON a, ToJSON a) => Authenticate (IxedJSON a) where
  type HashFor  (IxedJSON a)  = (JSONPath () -> Bool, Digest SHA3_256)
  type ProofFor (IxedJSON a) = JSONPath ([Digest SHA3_256], [Digest SHA3_256])
  type Access   (IxedJSON a) = Maybe
  retrieve Here j = (j ^? ix Here, Here)
  retrieve p (IxedJSON j) = case retrieve (nextPath p) . IxedJSON <$> j ^? tOf p of
    Just (Just v, p') -> (Just v, withStartOf p (join bimap (fmap jTopHash) $ others p j) p')
    _                 -> (Nothing, Here)
  digest (IxedJSON j) = (\p -> isJust $ j ^? tOf p, jTopHash j)
  verify _ jp (f, d) m p = Just False /= fmap (\v -> d == jFoldPath hashCons (jhash $ toJSON v) p) m
                        || not (f jp) && jp == fmap (const ()) p
