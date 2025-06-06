module ValidateInput

import Deriving.DepTyCheck.Gen

%language ElabReflection

%default total

data Y : Type -> Type -> Type where
  MkY : Y Int String

--- Not all arguments are named ---

genY_unnamed_argument : Fuel -> (a, b : Type) -> Nat -> Gen MaybeEmpty $ Y a b
genY_unnamed_argument = deriveGen

gen_unnamed_fun : Fuel -> ((a : Nat) -> Nat) -> Gen MaybeEmpty Nat
gen_unnamed_fun = deriveGen

--- Arguments shadowing ---

genY_shadowed_by_auto_argument : DecEq a => Fuel -> (a : Type) -> (b : Type) -> Gen MaybeEmpty $ Y a b
genY_shadowed_by_auto_argument = deriveGen

genY_shadowed_by_other_argument : Fuel -> (a : Type) -> (b : Type) -> (a : Type) -> Gen MaybeEmpty $ Y a b
genY_shadowed_by_other_argument = deriveGen
