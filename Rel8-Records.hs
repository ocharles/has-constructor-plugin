{-# language AllowAmbiguousTypes #-}
{-# language BlockArguments #-}
{-# language DataKinds #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language FunctionalDependencies #-}
{-# language GADTs #-}
{-# language NamedFieldPuns #-}
{-# language RecordWildCards #-}
{-# language RankNTypes #-}
{-# language PolyKinds #-}
{-# language ScopedTypeVariables #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
{-# language TypeFamilyDependencies #-}
{-# language TypeOperators #-}
{-# language UndecidableInstances #-}

{-# options -fplugin=RecordDotPreprocessor #-}

import Control.Applicative
import Data.Coerce
import Data.Functor.Compose
import Data.Functor.Classes
import Data.Functor.Identity
import Data.Functor.Product
import Data.Distributive
import Data.Functor.Rep
import Data.Functor.Sum
import Data.Kind
import Data.Type.Equality
import GHC.TypeLits
import GHC.Records.Extra


newtype Tagged (a :: k) x = Tagged x


instance Functor (Tagged a) where
  fmap f (Tagged x) = Tagged (f x)


instance Distributive (Tagged a) where
  distribute y = Tagged (fmap (\(Tagged x) -> x) y)


instance Representable (Tagged a) where
  type Rep (Tagged a) = ()

  index (Tagged x) () = x
  tabulate f = Tagged (f ())


class HFunctor (f :: (Type -> Type) -> Type) where
  hmap :: (forall x. g x -> h x) -> f g -> f h


class HFunctor f => HRepresentable (f :: (Type -> Type) -> Type) where
  type HRep f :: Type -> Type
  hindex :: f x -> (forall y. HRep f y -> x y)
  htabulate :: (forall y. HRep f y -> x y) -> f x


newtype HIdentity (a :: Type) (g :: Type -> Type) =
  HIdentity (g a)


instance HFunctor (HIdentity a) where
  hmap f (HIdentity x) = HIdentity (f x)


instance HRepresentable (HIdentity a) where
  type HRep (HIdentity a) = (:~:) a
  hindex (HIdentity x) Refl = x
  htabulate f = HIdentity (f Refl)


data HProduct (f :: (Type -> Type) -> Type) (g :: (Type -> Type) -> Type) (h :: Type -> Type) =
  HProduct (f h) (g h)


instance (HFunctor f, HFunctor g) => HFunctor (HProduct f g) where
  hmap f (HProduct x y) = HProduct (hmap f x) (hmap f y)


instance (HRepresentable f, HRepresentable g) => HRepresentable (HProduct f g) where
  type HRep (HProduct f g) = Sum (HRep f) (HRep g)

  hindex (HProduct x _y) (InL rep) = hindex x rep
  hindex (HProduct _x y) (InR rep) = hindex y rep

  htabulate f = HProduct (htabulate (f . InL)) (htabulate (f . InR))


instance (Representable f, HRepresentable g) => HRepresentable (Compose f g) where
  type HRep (Compose f g) = Product (Const (Rep f)) (HRep g)

  hindex (Compose x) (Pair (Const i) j) = hindex (index x i) j
  htabulate f = Compose (tabulate (\i -> htabulate (f . Pair (Const i))))


instance (Functor f, HFunctor g) => HFunctor (Compose f g) where
  hmap f (Compose x) = Compose (fmap (hmap f) x)


-- | The class of "table-like" things.
class HRepresentable (Pattern a) => Table a where
  -- | A higher-kinded pattern functor for this table.
  --
  -- This is a bit like a generic encoding of 'a', but lifted to higher-kinded
  -- data.
  --
  -- This is an injective type family rather than a data family to aid
  -- generic deriving.
  type Pattern a = (r :: (Type -> Type) -> Type) | r -> a

  -- | We can move from the actual data type into our generic encoding.
  from :: a -> Pattern a Identity

  -- | We can move from the generic encoding back into the data type, provided
  -- we're instantiating the Pattern at Identity.
  to :: Pattern a Identity -> a


-- | Typed expressions.
newtype Expr a =
  Expr (Pattern a Expr)


type family FindName k (name :: Symbol) f :: k where
  FindName (Product _ f r) name (Compose (Tagged (t :: *)) g) = 'Pair ('Const '()) (FindName (f r) name g)
  FindName _ name (Compose (Tagged name) (HIdentity r)) = 'Pair ('Const '()) 'Refl
  FindName (Sum _ _ r) name (HProduct (Compose (Tagged name) (HIdentity r)) _) = 'InL ('Pair ('Const '()) 'Refl)
  FindName (Sum _ f r) name (HProduct _ g) = 'InR (FindName (f r) name g)


class SPath (a :: k) where
  spath :: k

instance (SPath l, SPath r) => SPath ('Pair l r) where
  spath = Pair (spath @_ @l) (spath @_ @r)

instance SPath l => SPath ('InL l) where
  spath = InL (spath @_ @l)

instance SPath r => SPath ('InR r) where
  spath = InR (spath @_ @r)

instance SPath a => SPath ('Const a) where
  spath = Const (spath @_ @a)

instance SPath 'Refl where
  spath = Refl

instance SPath '() where
  spath = ()


instance (SPath (FindName (HRep (Pattern a) r) name (Pattern a)), HasField name a r, Table a, TestEquality (HRep (Pattern a))) => HasField (name :: Symbol) (Expr a) (Expr r) where
  hasField (Expr x) = (setter, getter) where
    i :: HRep (Pattern a) r
    i = spath @_ @(FindName (HRep (Pattern a) r) name (Pattern a))

    setter :: Expr r -> Expr a
    setter y = Expr $ htabulate \j ->
      case testEquality i j of
        Just Refl -> y
        Nothing -> hindex x j

    getter = hindex @(Pattern a) x i


instance TestEquality g => TestEquality (Product f g) where
  testEquality (Pair a b) (Pair x y) =
    testEquality b y


instance (TestEquality f, TestEquality g) => TestEquality (Sum f g) where
  testEquality (InL a) (InL b) = testEquality a b
  testEquality (InR a) (InR b) = testEquality a b
  testEquality _       _       = Nothing


-- TESTING


-- | We define our table as normal Haskell
data MyTable = MyTable { foo :: Bool, bar :: Int, pair :: (Bool, Bool) }


-- (We will ultimately derive this generically)
instance Table MyTable where
  type Pattern MyTable =
    -- We stick 'Compose (Tagged MyTable)' here so we are injective. Otherwise,
    -- if we had another type isomorphic to MyTable, it would have the same
    -- Pattern and thus the pattern would no longer be injective.
    Compose
      ( Tagged MyTable )
      ( HProduct
          ( Compose (Tagged "foo") (HIdentity Bool) )
          ( HProduct
              ( Compose ( Tagged "bar" ) ( HIdentity Int ) )
              ( Compose ( Tagged "pair" ) ( HIdentity (Bool, Bool) ) )
          )
      )

  from MyTable{ foo, bar, pair } =
    Compose . Tagged
      $ HProduct (Compose $ Tagged $ HIdentity $ pure foo)
      $ HProduct (Compose $ Tagged $ HIdentity $ pure bar)
      $ Compose $ Tagged $ HIdentity $ pure pair

  to (Compose (Tagged (HProduct (Compose (Tagged (HIdentity (Identity foo)))) (HProduct (Compose (Tagged (HIdentity (Identity bar)))) (Compose (Tagged (HIdentity (Identity pair)))))))) =
    MyTable{..}


-- Base types are one column tables.

instance Table Bool where
  type Pattern Bool = HIdentity Bool
  from = coerce
  to = coerce


instance Table Int where
  type Pattern Int = HIdentity Int
  from = coerce
  to = coerce


-- Pairs are tables, but interestingly don't actually need their elements to be
-- tables. Table constraints will be added when we need them.
instance Table (a, b) where
  type Pattern (a, b) = Compose (Tagged (a, b)) (HProduct (HIdentity a) (HIdentity b))
  from (a, b) = Compose $ Tagged $ HProduct (HIdentity $ pure a) (HIdentity $ pure b)
  to (Compose (Tagged (HProduct (HIdentity (Identity a)) (HIdentity (Identity b))))) = (a, b)


-- Assume we have...
myTable :: Expr MyTable
myTable = undefined


-- We can project out foo with dot:
myTableFoo :: Expr Bool
myTableFoo = myTable.foo


-- We can also project out a pair
myTablePair :: Expr MyTable -> Expr (Bool, Bool)
myTablePair x = x.pair


-- And we can project out elements of a pair:
fst_ :: Expr (a, b) -> Expr a
fst_ (Expr x) = hindex x $ Pair (Const ()) $ InL Refl


-- And this all composes as you'd expect
-- myTableFstPair :: Expr MyTable -> Expr Bool
-- myTableFstPair = fst_ . myTablePair
