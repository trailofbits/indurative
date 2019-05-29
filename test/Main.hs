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

import Indurative

import Control.Lens hiding (elements)
import Crypto.Hash (SHA3_256)
import Data.Binary (Binary)
import Data.Proxy (Proxy(..))
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
type Basic x = (Arbitrary x, Binary x, Eq x, Show x, Typeable x)
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

main :: IO ()
main = mapM_ (\(n, p) -> putStrLn n >> quickCheck @Property p) $ matrix testDerived where
  matrix :: (forall t x. Derived t x => Proxy t -> Proxy x -> r) -> [r]
  matrix f = row (f $ Proxy @IntMap) ++ row (f $ Proxy @Maybe)     ++ row (f $ Proxy @[])
          ++ row (f $ Proxy @Seq)    ++ row (f $ Proxy @(Map Int)) ++ row (f $ Proxy @(Map String))
  row :: (forall x. Basic x => Proxy x -> r) -> [r]
  row f = [ f (Proxy @Int),               f (Proxy @String),              f (Proxy @(Maybe [Bool]))
          , f (Proxy @(Either Float ())), f (Proxy @([Integer], Double))                          ]
