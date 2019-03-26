{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Indurative.Test where

import Control.Lens hiding (elements)
import Control.Monad (ap)
import Crypto.Hash (SHA3_256)
import Data.Aeson (Value(..))
import Data.Aeson.Lens (_Integral, key, members, nth, values)
import Data.Bifunctor (Bifunctor(..))
import Data.Binary (Binary)
import Data.Proxy (Proxy(..))
import Data.Text (pack)
import Type.Reflection (Typeable, someTypeRep)
import Test.QuickCheck hiding (reason)
import Test.QuickCheck.Property

import qualified Data.HashMap.Strict as H (fromList)
import qualified Data.Vector         as V (fromList)

import Data.Array (Array, Ix)
import Data.IntMap (IntMap)
import Data.Map (Map)
import Data.Sequence (Seq)

import Indurative
import Indurative.JSON

deriving via Auth SHA3_256 (Map   k) v instance (Ord k, Binary k, Binary v) => Authenticate (Map   k v)
deriving via Auth SHA3_256 IntMap    v instance Binary v =>                    Authenticate (IntMap  v)
deriving via Auth SHA3_256 Maybe     v instance Binary v =>                    Authenticate (Maybe   v)
deriving via Auth SHA3_256 []        v instance Binary v =>                    Authenticate         [v]
deriving via Auth SHA3_256 (Array i) v instance (Binary i, Binary v, Ix i) =>  Authenticate (Array i v)
deriving via Auth SHA3_256 Seq       v instance Binary v =>                    Authenticate (Seq     v)
{- Add when quickcheck instances are available import Data.Hashable (Hashable)
import Data.HashMap.Strict (HashMap)
import Data.Tree (Tree)
import Data.Vector (Vector)
deriving via Auth SHA3_256 (HashMap k) v instance (Hashable k, Ord k, Binary k, Binary v) => Authenticate (HashMap k v)
deriving via Auth SHA3_256 Tree        v instance Binary v =>                                Authenticate (Tree      v)
deriving via Auth SHA3_256 Vector      v instance Binary v =>                                Authenticate (Vector    v)
-}

type Tested t x = ( Authenticate (t x), Arbitrary (t x), Access (t x) ~ AtIndex (Index (t x))
                  , Eq (IxValue (t x)), Show (t x), Show (Index (t x)), Show (IxValue (t x))
                  , FoldableWithIndex (Index (t x)) t, Ixed (t x), x ~ IxValue (t x), Typeable (t x))

faithful :: forall t x. Tested t x => Proxy t -> Proxy x -> (String, Property)
faithful _ _ = let ty = Proxy :: Proxy (t x) in (show $ someTypeRep ty,) . property $ do
  (t, is) <- suchThat (ap (,) (fmap fst . itoListOf ifolded) <$>
                               arbitrary :: Gen (t x, [Index (t x)]))
                      (not . null . snd)
  i <- elements is
  let (res, p) = retrieve i t
  let got      = snd $ runAI res
  let real     = t ^? ix i
  let mismatch = "asked for " ++ show i   ++ " from " ++ show t
              ++ " but got "  ++ show got ++ " instead of " ++ show real
  let badProof = "asked for  "++ show i   ++ " from " ++ show t ++" but proof failed!"
  return $ if | got /= real -> failed {reason = mismatch}
              | not $ verify ty (digest t) res p -> failed {reason = badProof}
              | otherwise -> succeeded where

testJson :: (String, Property)
testJson = let genJSON 0 = (_Integral #) <$> (arbitrary :: Gen Int)
               genJSON n = frequency [ (1, (_Integral #) <$> (arbitrary :: Gen Int))
                                     , (5, Array  . V.fromList                    <$> listOf (genJSON $ n - 1))
                                     , (5, Object . H.fromList . map (first pack) <$> ps n)
                                     ]
               ps n = zip <$> infiniteListOf arbitrary <*> listOf (genJSON $ n - 1)
               genPath :: Value -> Gen (JSONPath ())
               genPath a@(Array v)  = if null v then pure Here else
                 elements (fst <$> a ^@.. values)  >>= \k -> AtIx  k () <$> genPath (a ^?! nth k)
               genPath a@(Object v) = if null v then pure Here else
                 elements (fst <$> a ^@.. members) >>= \k -> AtKey k () <$> genPath (a ^?! key k)
               genPath _            = pure Here in
  ("IxedJSON Int",) . property $ do
    j <- genJSON (3 :: Integer)
    p <- genPath j
    let (res, r) = retrieve p (IxedJSON j)
    let real     = IxedJSON j ^? ix p
    let mismatch = "asked for " ++ show p   ++ " from " ++ show j
                ++ " but got "  ++ show res ++ " instead of " ++ show real
    let badProof = "asked for  "++ show p   ++ " from " ++ show j ++" but proof failed!"
    return $ if | res /= real -> failed {reason = mismatch}
                | not $ verify (Proxy :: Proxy (IxedJSON Int)) (digest (IxedJSON j :: IxedJSON Int))
                               res r -> failed {reason = badProof}
                | otherwise -> succeeded where


onTs :: forall (t :: * -> *) r.
       (forall x. (Arbitrary x, Binary x, Eq x, Show x, Typeable x) => Proxy t -> Proxy x -> r)
     -> Proxy t
     -> [r]
onTs f p = [ f p (Proxy :: Proxy Int)
           , f p (Proxy :: Proxy String)
           , f p (Proxy :: Proxy (Maybe [Bool]))
           , f p (Proxy :: Proxy (Either Float ()))
           , f p (Proxy :: Proxy ([Integer], Double))
           ]

props :: [(String, Property)]
props = [testJson] 
     ++ onTs faithful (Proxy :: Proxy IntMap)
     ++ onTs faithful (Proxy :: Proxy Maybe)
     ++ onTs faithful (Proxy :: Proxy [])
     ++ onTs faithful (Proxy :: Proxy Seq)
     ++ onTs faithful (Proxy :: Proxy (Map Int))
     ++ onTs faithful (Proxy :: Proxy (Map String))
{- Add when quickcheck instances are available
     ++ onTs faithful (Proxy :: Proxy (HashMap Int))
     ++ onTs faithful (Proxy :: Proxy (HashMap String))
     ++ onTs faithful (Proxy :: Proxy Tree)
     ++ onTs faithful (Proxy :: Proxy Vector)
-}

main :: IO ()
main = mapM_ (\(n, p) -> putStrLn n >> quickCheck p) props
