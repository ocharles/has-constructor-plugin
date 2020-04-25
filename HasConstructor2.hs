{-# language PolyKinds #-}

module HasConstructor2 where

import Data.Functor.Compose ( Compose(..) )
import GHC.Generics
import Data.Kind ( Type )
import GHC.TypeLits ( Symbol )

class HasConstructor (k :: Type) (constructor :: k) where
  constructor :: constructor

-- instance HasConstructor "Just" (Maybe a) (a -> Maybe a) where
--   constructor = Just

-- instance HasConstructor "Nothing" (Maybe a) (Maybe a) where
--   constructor = Nothing

-- test1 :: Maybe Bool
-- test1 = constructor @"Just" @(Maybe Bool) True

-- test2 :: Maybe Bool
-- test2 = constructor @"Nothing" @(Maybe Bool)

-- data Record = Record { x, y, z :: Bool }
--   deriving (Generic)

-- instance HasConstructor "Record" Record (Bool -> Bool -> Bool -> Record) where
--   constructor = Record

-- record :: Record
-- record = constructor @"Record" @Record True False True

-- newtype Lifted (f :: Type -> Type) (a :: Type) =
--   Lifted (Wrap f (Rep a) ())

-- type family Wrap (f :: Type -> Type) (rep :: Type -> Type) :: Type -> Type where
--   Wrap f (M1 i c x) = M1 i c (Wrap f x)
--   Wrap f (l :*: r) = Wrap f l :*: Wrap f r
--   Wrap f (K1 i a) = K1 i (f a)
--   Wrap f (l :+: r) = Wrap f l :*: Wrap f r

-- class Functor f => Mk (rep :: Type -> Type) (f :: Type -> Type) | rep -> f where
--   mk :: f (rep a)

-- instance Mk (K1 i a) ((->) a) where
--   mk = K1

-- instance (Mk l fl, Mk r fr) => Mk (l :*: r) (Compose fl fr) where
--   mk = Compose (fmap (\l -> fmap (\r -> (l :*:) r) mk) mk)

-- instance Mk rep f => Mk (M1 i c rep) f where
--   mk = M1 <$> mk

-- class Functor f => Apply f a b | f a -> b where
--   apply :: f a -> b

-- instance Apply ((->) x) y (x -> y) where
--   apply = id

-- instance (Apply g a b, Apply f b c) => Apply (Compose f g) a c where
--   apply (Compose f) = apply (fmap apply f)

-- instance (Apply g (Lifted f t) constructor, Mk (Wrap f (Rep t)) g) => HasConstructor name (Lifted f t) constructor where
--   constructor =
--     apply @_ @(Lifted f t) (Lifted <$> mk)

-- liftedRecord :: Lifted Maybe Record
-- liftedRecord =
--   constructor
--     @"Record"
--     @(Lifted Maybe Record)
--     (Just True)
--     (Just False)
--     Nothing


-- data SumType = C1 Bool | C2 Bool


-- liftedSumC1 :: Lifted Maybe SumType
-- liftedSumC1 =
--   constructor
--     @"C1"
--     @(Lifted Maybe SumType)
--     (Just True)
