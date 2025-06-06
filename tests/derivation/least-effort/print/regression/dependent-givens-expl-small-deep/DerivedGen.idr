module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

data X : (n : Nat) -> Fin n -> Type where
  MkX : (n : _) -> (f : _) -> X (S (S n)) (FS (FS f))

%language ElabReflection

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (n : Nat) -> (f : Fin n) -> Gen MaybeEmpty $ X n f
