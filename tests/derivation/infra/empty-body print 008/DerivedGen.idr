module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

import Data.Vect

%default total

%language ElabReflection

%runElab deriveGenPrinter @{EmptyBody} $ Fuel -> Gen MaybeEmpty (n : Nat ** a : Type ** Vect n a)
