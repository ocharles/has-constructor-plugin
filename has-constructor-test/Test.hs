{-# language AllowAmbiguousTypes #-}
{-# language RecordWildCards #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language DataKinds #-}
{-# language DeriveGeneric #-}
{-# language FunctionalDependencies #-}
{-# language NamedFieldPuns #-}
{-# language ScopedTypeVariables #-}
{-# language TypeApplications #-}
{-# language TypeFamilyDependencies #-}
{-# language TypeOperators #-}
{-# language UndecidableInstances #-}

{-# options -fplugin=Plugin #-}

module Test where

import Data.Bifunctor ( first )
import Data.Functor.Compose ( Compose(..) )
import GHC.Generics
import Data.Kind ( Type )
import GHC.TypeLits ( Symbol )
import HasConstructor
import Data.Proxy

data Record = Record { x, y, z :: Bool }
  deriving (Generic, Show)

record :: Record
record =
  Record False True True

newtype Lifted (f :: Type -> Type) (a :: Type) =
  Lifted (Wrap1 f (Rep a) ())

type family FindConstructor (name :: Symbol) (rep :: Type -> Type) :: Type -> Type where
  FindConstructor name (M1 D c f) = FindConstructor name f
  FindConstructor name (M1 C (MetaCons name x y) f) = f

-- >>> plainRecord
-- Record {x = True, y = False, z = False}
plainRecord :: Record
plainRecord = Record True False False

-- >>> unlift liftedRecord1
-- Nothing
liftedRecord1 :: Lifted Maybe Record
liftedRecord1 =
  Record (Just True) Nothing (Just False)

-- >>> unlift liftedRecord2
-- Just (Record {x = True, y = False, z = False})
liftedRecord2 :: Lifted Maybe Record
liftedRecord2 =
  Record (Just True) (Just False) (Just False)

-- >>> unlift liftedRecord3
-- Just (Record {x = True, y = False, z = False})
liftedRecord3 :: Lifted Maybe Record
liftedRecord3 =
  Record { x = Just True, y = Just True, z = Just False }

-- >>> unlift liftedRecord4
-- Just (Record {x = True, y = False, z = True})
liftedRecord4 :: Lifted Maybe Record
liftedRecord4 =
  let y = Just False
      z = Just True
  in Record { x = Just True, y, z }

liftedRecord5 :: Lifted Maybe Record
liftedRecord5 =
  let y = Just False
      z = Just True
  in Record { x = Just True, .. }

type family Wrap1 (f :: Type -> Type) (a :: Type -> Type) :: Type -> Type where
  Wrap1 f (M1 i c a) = M1 i c (Wrap1 f a)
  Wrap1 f (l :*: r) = Wrap1 f l :*: Wrap1 f r
  Wrap1 f (K1 i a) = K1 i (f a)
  Wrap1 f (l :+: r) = Wrap1 f l :+: Wrap1 f r

class Functor f => Mk rep f | rep -> f where
  mk :: f (rep a)

instance Mk (K1 i c) ((->) c) where
  mk = \x -> K1 x

instance (Mk l fl, Mk r fr) => Mk (l :*: r) (Compose fl fr) where
  mk = Compose (fmap (\l -> fmap (\r -> l :*: r) mk) mk)

instance (Mk f f') => Mk (M1 i c f) f' where
  mk = M1 <$> mk

class Functor f => Apply f a b | f a -> b where
  apply :: f a -> b

instance Apply ((->) a) b (a -> b) where
  apply = id

instance (Apply g a b, Apply f b c) => Apply (Compose f g) a c where
  apply (Compose x) = apply (fmap apply x)

instance
  ( Constructs liftedConstructor ~ Lifted f a
  , HasConstructor name a constructor
  , Apply x ( Lifted f a ) liftedConstructor
  , Mk ( Wrap1 f ( FindConstructor name ( Rep a ) ) ) x
  , Inject name (Wrap1 f (FindConstructor name (Rep a))) (Wrap1 f (Rep a))
  ) => HasConstructor name (Lifted f a) liftedConstructor where
  constructor =
    apply @x @(Lifted f a) (fmap (Lifted . inject @name) $ mk @(Wrap1 f (FindConstructor name (Rep a))) @x @() )

class Inject (name :: Symbol) rep f | f name -> rep where
  inject :: rep x -> f x

instance Inject name rep f => Inject name rep (M1 D c f) where
  inject = M1 . inject @name

instance (name ~ name', f ~ rep) => Inject name rep (M1 C (MetaCons name' x y) f) where
  inject = M1

unlift :: forall f a. (Generic a, Applicative f, Distribute (Wrap1 f (Rep a)) f (Rep a)) => Lifted f a -> f a
unlift (Lifted a) = to <$> distribute a

class Distribute f m g | f m -> g where
  distribute :: Applicative m => f x -> m (g x)

instance (Distribute f m f', i ~ i', c ~ c') => Distribute (M1 i c f) m (M1 i' c' f') where
  distribute (M1 x) = M1 <$> distribute x

instance (Distribute f m f', Distribute g m g') => Distribute (f :*: g) m (f' :*: g') where
  distribute (x :*: y) = (:*:) <$> distribute x <*> distribute y

instance (i ~ i', a ~ m a') => Distribute (K1 i a) m (K1 i' a') where
  distribute (K1 m) = K1 <$> m

----

instance (i ~ i', c ~ c', a ~ a') => HasConstructor "K1" (K1 i c a) (c' -> K1 i' c' a') where
  constructor = K1

instance (g ~ g', g' ~ g'', f ~ f', f' ~ f'', a ~ a', a' ~ a'') => HasConstructor "Compose" (Compose g f a) (g' (f' a') -> Compose g'' f'' a'') where
  constructor = Compose

instance HasConstructor "Just" (Maybe a) (a -> Maybe a) where
  constructor = Just
