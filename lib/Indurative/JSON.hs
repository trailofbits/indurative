{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}

module Indurative.JSON where

import Control.Lens
import Control.Monad (join, void)
import Crypto.Hash (Digest, HashAlgorithm, SHA3_256)
import Data.Aeson
import Data.Aeson.Lens
import Data.List (sortBy)
import Data.Ord (comparing)
import Data.Text (Text)
import Indurative

data JSONPath a = Here | AtKey Text a (JSONPath a) | AtIx Int a (JSONPath a)
  deriving (Eq, Functor, Ord, Show)

tOf :: JSONPath a -> Traversal' Value Value
tOf = \case Here -> ignored; AtKey k _ _ -> key k; AtIx i _ _ -> nth i

topVal :: JSONPath a -> Maybe a
topVal = \case Here -> Nothing; AtKey _ a _ -> Just a; AtIx _ a _ -> Just a

nextPath :: JSONPath a -> JSONPath a
nextPath = \case Here -> Here; AtKey _ _ m -> m; AtIx _ _ m -> m

withStartOf :: JSONPath a -> b -> JSONPath b -> JSONPath b
withStartOf a b p = case a of Here -> Here; AtKey k _ _ -> AtKey k b p; AtIx i _ _ -> AtIx i b p

jTopHash :: HashAlgorithm a => Value -> Digest a
jTopHash v = let go t j = foldr1 hashCons $ jTopHash . snd <$> sortBy (comparing fst) (j ^@.. t) in
  case v of Array  a | not $ null a -> go values v
            Object o | not $ null o -> go members v
            _                       -> hash $ encode v

jFoldPath :: (a -> a -> a) -> a -> JSONPath ([a], [a]) -> a
jFoldPath f i v = case topVal v of Nothing     -> i
                                   Just (l, r) -> foldr1 f (l ++ [jFoldPath f i $ nextPath v] ++ r)

newtype IxedJSON a = IxedJSON Value deriving Show

type instance Index   (IxedJSON a) = JSONPath ()
type instance IxValue (IxedJSON a) = a

others :: Value -> JSONPath a -> ([Value], [Value])
others v = let other l i j = (those l (< i) j, those l (> i) j)
               those l f j = fmap snd . sortBy (comparing fst) $ j ^@.. l . indices f in
  \case Here -> mempty; (AtKey k _ _) -> other members k v; (AtIx  i _ _) -> other values i v

instance (FromJSON a, ToJSON a) => Ixed (IxedJSON a) where
  ix Here f ij@(IxedJSON j) = maybe (pure ij) (fmap (IxedJSON . toJSON) . f) $ j ^? _JSON
  ix i f ij@(IxedJSON j) = let inJ (IxedJSON v) = IxedJSON $ j & tOf i .~ v in
    maybe (pure ij) (fmap inJ) $ ix (nextPath i) f . IxedJSON <$> j ^? tOf i

instance (FromJSON a, ToJSON a) => Authenticate (IxedJSON a) where
  type HashFor  (IxedJSON a) = (JSONPath () -> Bool, Digest SHA3_256)
  type ProofFor (IxedJSON a) = JSONPath ([Digest SHA3_256], [Digest SHA3_256])
  type Access   (IxedJSON a) = Maybe
  retrieve Here j = (j ^? ix Here, Here)
  retrieve p (IxedJSON j) = case retrieve (nextPath p) . IxedJSON <$> j ^? tOf p of
    Just (Just v, p') -> (Just v, withStartOf p (join bimap (fmap jTopHash) $ others j p) p')
    _                 -> (Nothing, Here)
  digest (IxedJSON j) = (flip has j . tOf, jTopHash j)
  verify _ jp (f, d) m p = not (f jp) && jp == void p ||
    maybe True (\v -> d == jFoldPath hashCons (hash . encode $ toJSON v) p) m
