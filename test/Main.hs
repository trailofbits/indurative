{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

import Control.Lens hiding (elements)
import Control.Monad (liftM2)
import Crypto.Hash (SHA3_256)
import Data.Aeson (Value(..), FromJSON, ToJSON(..))
import Data.Aeson.Lens (key, members, nth, values)
import Data.Binary (Binary)
import Data.Proxy (Proxy(..))
import Data.Text (Text)
import Indurative
import Indurative.SparseMT
import Indurative.JSON
import Type.Reflection (Typeable, typeRep)
import Test.QuickCheck hiding (Result(..))
import Test.QuickCheck.Instances.Text ()
import Test.QuickCheck.Property (Result, failed, reason, succeeded)

import Data.IntMap (IntMap)
import Data.Map (Map)
import Data.Sequence (Seq)

deriving via Auth SHA3_256 (Map k) v instance (Ord k, Binary k, Binary v) => Authenticate (Map  k v)
deriving via Auth SHA3_256 IntMap  v instance Binary v =>                    Authenticate (IntMap v)
deriving via Auth SHA3_256 Maybe   v instance Binary v =>                    Authenticate (Maybe  v)
deriving via Auth SHA3_256 []      v instance Binary v =>                    Authenticate        [v]
deriving via Auth SHA3_256 Seq     v instance Binary v =>                    Authenticate (Seq    v)

type Authed t = ( Authenticate t, Access t ~ Maybe, Eq (IxValue t), Ixed t
                , Show t, Show (Index t), Show (IxValue t), Typeable t)
type Basic x = (Arbitrary x, Binary x, Eq x, FromJSON x, Show x, ToJSON x, Typeable x)
type Derived t x = (FoldableWithIndex (Index (t x)) t, Arbitrary (t x), Authed (t x), Basic x)

testAuth :: forall t. Authed t => t -> Index t -> Result
testAuth t i = let (got, p) = retrieve i t
                   describe = concat ["asked for ", show i, " from ", show t]
                   mismatch = concat [" but got ", show got, " instead of ", show $ t ^? ix i] in if
  | got /= t ^? ix i                         -> failed {reason = describe ++ mismatch}
  | not $ verify @t Proxy i (digest t) got p -> failed {reason = describe ++ " but proof failed!"}
  | otherwise                                -> succeeded

testDerived :: forall t x. Derived t x => Proxy t -> Proxy x -> (String, Property)
testDerived _ _ = (show $ typeRep @(t x),) . property $ uncurry fmap . fmap elements <$>
  (arbitrary <&> \l -> (testAuth @(t x) l, fst <$> itoList l)) `suchThat` (not . null . snd)

genVal :: forall x. Basic x => Proxy x -> Int -> Gen Value
genVal _ 0 = toJSON <$> arbitrary @x
genVal p n = let l = listOf . genVal p $ (n - 1) in oneof [genVal p 0, toJSON <$> l, obj l] where
  obj = fmap toJSON . liftM2 zip (listOf $ arbitrary @Text)

genPath :: Value -> Gen (JSONPath ())
genPath v = let go t c i j = elements (fst <$> j ^@.. t) >>= \k -> c k () <$> genPath (j ^?! i k) in
  case v of (Array  a) | not $ null a -> go values  AtIx  nth v
            (Object o) | not $ null o -> go members AtKey key v
            _                         -> pure Here

testJson :: forall x. Basic x => Proxy x -> (String, Property)
testJson p = (show $ typeRep @(IxedJSON x),) . property $ genVal p 3 >>=
  \j -> testAuth (IxedJSON @x j) <$> genPath j

main :: IO ()
main = mapM_ (\(n, p) -> putStrLn n >> quickCheck p) (matrix testDerived ++ row testJson) where
  matrix :: (forall t x. Derived t x => Proxy t -> Proxy x -> r) -> [r]
  matrix f = row (f $ Proxy @IntMap) ++ row (f $ Proxy @Maybe)     ++ row (f $ Proxy @[])
          ++ row (f $ Proxy @Seq)    ++ row (f $ Proxy @(Map Int)) ++ row (f $ Proxy @(Map String))
  row :: (forall x. Basic x => Proxy x -> r) -> [r]
  row f = [ f (Proxy @Int),               f (Proxy @String),              f (Proxy @(Maybe [Bool]))
          , f (Proxy @(Either Float ())), f (Proxy @([Integer], Double))                          ]
