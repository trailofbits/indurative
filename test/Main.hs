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

module Main where

import Control.Lens hiding (elements)
import Control.Monad (ap)
import Crypto.Hash (SHA3_256)
import Data.Aeson (Value(..))
import Data.Aeson.Lens (_Integral, key, members, nth, values)
import Data.Binary (Binary)
import Data.Proxy (Proxy(..))
import Data.Text (pack)
import Type.Reflection (Typeable, someTypeRep)
import Test.QuickCheck hiding (Result, reason)
import Test.QuickCheck.Property (Result, failed, reason, succeeded)

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

type Tested t x = ( Authenticate (t x), Arbitrary (t x), Access (t x) ~ Maybe
                  , Eq (IxValue (t x)), Show (t x), Show (Index (t x)), Show (IxValue (t x))
                  , FoldableWithIndex (Index (t x)) t, Ixed (t x), x ~ IxValue (t x), Typeable (t x))

testAuth :: forall t. ( Authenticate t, Eq (IxValue t), Ixed t
                      , Show t, Show (Index t), Show (IxValue t), Access t ~ Maybe)
         => t -> Index t -> Result
testAuth t i = let (got, p) = retrieve i t
                   real     = t ^? ix i
                   mismatch = "asked for " ++ show i   ++ " from " ++ show t
                           ++ " but got "  ++ show got ++ " instead of " ++ show real
                   badProof = "asked for  "++ show i   ++ " from " ++ show t ++" but proof failed!" in
                   if | got /= real -> failed {reason = mismatch}
                      | not $ verify (Proxy :: Proxy t) i (digest t) got p -> failed {reason = badProof}
                      | otherwise -> succeeded

testDerived :: forall t x. Tested t x => Proxy t -> Proxy x -> (String, Property)
testDerived _ _ = let ty = Proxy :: Proxy (t x) in (show $ someTypeRep ty,) . property $ do
  (t, is) <- suchThat (ap (,) (fmap fst . itoListOf ifolded) <$>
                               arbitrary :: Gen (t x, [Index (t x)]))
                      (not . null . snd)
  i <- elements is
  return $ testAuth t i

testJson :: (String, Property)
testJson = let genJSON 0 = (_Integral #) <$> (arbitrary :: Gen Int)
               genJSON n = frequency [ (1, genJSON 0)
                                     , (5, Array  . V.fromList <$> listOf (genJSON $ n - 1))
                                     , (2, Object . H.fromList <$> ps n)
                                     ]
               ps n = zip <$> (map pack <$> infiniteListOf arbitrary) <*> listOf (genJSON $ n - 1)
               genPath a@(Array v)  = if null v then pure Here else
                 elements (fst <$> a ^@.. values)  >>= \k -> AtIx  k () <$> genPath (a ^?! nth k)
               genPath a@(Object v) = if null v then pure Here else
                 elements (fst <$> a ^@.. members) >>= \k -> AtKey k () <$> genPath (a ^?! key k)
               genPath _            = pure Here in
  ("IxedJSON Int",) . property $ do
    j <- genJSON (3 :: Integer) -- TODO: Stop killing heap
    p <- genPath j
    return $ testAuth (IxedJSON j :: IxedJSON Int) p

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
     ++ onTs testDerived (Proxy :: Proxy IntMap)
     ++ onTs testDerived (Proxy :: Proxy Maybe)
     ++ onTs testDerived (Proxy :: Proxy [])
     ++ onTs testDerived (Proxy :: Proxy Seq)
     ++ onTs testDerived (Proxy :: Proxy (Map Int))
     ++ onTs testDerived (Proxy :: Proxy (Map String))
{- Add when quickcheck instances are available
     ++ onTs testDerived (Proxy :: Proxy (HashMap Int))
     ++ onTs testDerived (Proxy :: Proxy (HashMap String))
     ++ onTs testDerived (Proxy :: Proxy Tree)
     ++ onTs testDerived (Proxy :: Proxy Vector)
-}

main :: IO ()
main = mapM_ (\(n, p) -> putStrLn n >> quickCheck p) props
