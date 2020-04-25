{-# language AllowAmbiguousTypes #-}
{-# language DataKinds #-}
{-# language FunctionalDependencies #-}
{-# language KindSignatures #-}
{-# language TypeFamilyDependencies #-}
{-# language TypeOperators #-}

module HasConstructor where

import Data.Kind ( Type )
import GHC.TypeLits ( Symbol )

type family Constructs (f :: Type) = (a :: Type) where
  Constructs (a -> b) = Constructs b
  Constructs a = a

class Constructs f ~ t => HasConstructor (name :: Symbol) (t :: Type) (f :: Type) | t name -> f where
  constructor :: f
