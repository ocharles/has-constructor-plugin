{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language RankNTypes #-}
{-# language TypeFamilies #-}

import Data.Functor.Identity
import Data.Kind
import Data.Type.Equality

class HFunctor f where
  hmap :: (forall x. g x -> h x) -> f g -> f h

class HFunctor f => Representable1 f where
  type Rep1 f :: Type -> Type
  index :: f a -> (forall x. Rep1 f x -> a x)
  tabulate :: (forall x. Rep1 f x -> a x) -> f a

newtype Const1 (a :: Type) (g :: Type -> Type) = Const1 a

instance HFunctor (Const1 a) where
  hmap _ (Const1 x) = Const1 x

newtype Identity1 (f :: Type -> Type) =
  Identity1 (forall x. f x)

instance HFunctor Identity1 where
  hmap f (Identity1 x) = Identity1 (f x)

instance Representable1 Identity1 where
  type Rep1 Identity1 = Identity
  index (Identity1 x) (Identity y) = x
  tabulate f = Identity1 (f undefined)

data Identity2 (f :: Type -> Type) where
  Identity2 :: f x -> Identity2 f

instance HFunctor Identity2 where
  hmap f (Identity2 x) = Identity2 (f x)

instance Representable1 Identity2 where
  type Rep1 Identity2 = Identity
  index (Identity2 x) (Identity y) = undefined
  tabulate f = Identity2 (f (Identity ()))

newtype Identity3 (a :: Type) (f :: Type -> Type) =
  Identity3 (f a)

instance HFunctor (Identity3 a) where
  hmap f (Identity3 x) = Identity3 (f x)

instance Representable1 (Identity3 a) where
  type Rep1 (Identity3 a) = (:~:) a
  index (Identity3 x) Refl = x
  tabulate f = Identity3 (f Refl)
