module ValidateInput

import Test.DepTyCheck.Gen.Auto

%language ElabReflection

%default total

-----------------------
--- Data structures ---
-----------------------

data X = MkX

data X' = MkX'

data Y : Type -> Type -> Type where
  MkY : Y Int String

------------------------------------
--- Compiling, but bad signature ---
------------------------------------

--- Non-Gen type ---

list : List Int
list = deriveGen

y : Y Int String
y = deriveGen

--- No fuel argument ---

genY_noFuel_given : (a, b : Type) -> Gen $ Y a b
genY_noFuel_given = deriveGen

genY_noFuel_mid : (b : Type) -> Gen (a ** Y a b)
genY_noFuel_mid = deriveGen

genY_noFuel_mid' : (b : Type) -> Gen $ DPair {a = Type, p = \a => Y a b}
genY_noFuel_mid' = deriveGen

genY_noFuel_gened : Gen (a ** b ** Y a b)
genY_noFuel_gened = deriveGen

--- Misplaced fuel argument ---

genY_missplFuel_aft : (a, b : Type) -> {fuel : Fuel} -> Gen $ Y a b
genY_missplFuel_aft = deriveGen

genY_missplFuel_mid : (a : Type) -> {fuel : Fuel} -> (b : Type) -> Gen $ Y a b
genY_missplFuel_mid = deriveGen

genY_missplFuel_aft_autoimpl : Gen X => {fuel : Fuel} -> (a, b : Type) -> Gen $ Y a b
genY_missplFuel_aft_autoimpl = deriveGen

genY_missplFuel_aft_exp : (a, b : Type) -> Fuel -> Gen $ Y a b
genY_missplFuel_aft_exp = deriveGen

genY_missplFuel_mid_exp : (a : Type) -> Fuel -> (b : Type) -> Gen $ Y a b
genY_missplFuel_mid_exp = deriveGen

genY_missplFuel_aft_autoimpl_exp : Gen X => Fuel -> (a, b : Type) -> Gen $ Y a b
genY_missplFuel_aft_autoimpl_exp = deriveGen

--- Unnamed or badly named fuel argument ---

genY_unnamed_fuel : {_ : Fuel} -> (a, b : Type) -> Gen $ Y a b
genY_unnamed_fuel = deriveGen

genY_badly_named_fuel : {f : Fuel} -> (a, b : Type) -> Gen $ Y a b
genY_badly_named_fuel = deriveGen

--- Badly parameterised fuel argument ---

genY_defaulted_fuel : {default Dry fuel : Fuel} -> (a, b : Type) -> Gen $ Y a b
genY_defaulted_fuel = deriveGen

genY_defaulted_fuel' : {default (limit 120) fuel : Fuel} -> (a, b : Type) -> Gen $ Y a b
genY_defaulted_fuel' = deriveGen

genY_exp_fuel : (fuel : Fuel) -> (a, b : Type) -> Gen $ Y a b
genY_exp_fuel = deriveGen

--- Unrelated stuff in the resulting dpair ---

genY_with_unrelated : {fuel : Fuel} -> (a : Type) -> Gen (b : Type ** n : Nat ** Y a b)
genY_with_unrelated = deriveGen

--- Gen of strange things ---

genOfGens : {fuel : Fuel} -> Gen $ Gen X
genOfGens = deriveGen

genOfLazies : {fuel : Fuel} -> Gen $ Lazy X
genOfLazies = deriveGen

genOfInfs : {fuel : Fuel} -> Gen $ Inf X
genOfInfs = deriveGen

genOfDPair : {fuel : Fuel} -> (a ** b ** Gen $ Y a b)
genOfDPair = deriveGen

genOfFuns_pur : {fuel : Fuel} -> Gen $ (a : Type) -> (b : Type) -> Y a b
genOfFuns_pur = deriveGen

genOfFuns_pur0s : {fuel : Fuel} -> Gen $ (0 a : Type) -> (0 b : Type) -> Y a b
genOfFuns_pur0s = deriveGen

genOfFuns_pur1s : {fuel : Fuel} -> Gen $ (1 a : Type) -> (1 b : Type) -> Y a b
genOfFuns_pur1s = deriveGen

genOfFuns_ins_pair : {fuel : Fuel} -> Gen (a ** ((b : Type) -> Y a b))
genOfFuns_ins_pair = deriveGen

genOfFuns_ins_pair0 : {fuel : Fuel} -> Gen (a ** ((0 b : Type) -> Y a b))
genOfFuns_ins_pair0 = deriveGen

genOfFuns_ins_pair1 : {fuel : Fuel} -> Gen (a ** ((1 b : Type) -> Y a b))
genOfFuns_ins_pair1 = deriveGen

genOfFuns_out_pair : {fuel : Fuel} -> Gen $ (b : Type) -> (a ** Y a b)
genOfFuns_out_pair = deriveGen

genOfFuns_out_pair0 : {fuel : Fuel} -> Gen $ (0 b : Type) -> (a ** Y a b)
genOfFuns_out_pair0 = deriveGen

genOfFuns_out_pair1 : {fuel : Fuel} -> Gen $ (1 b : Type) -> (a ** Y a b)
genOfFuns_out_pair1 = deriveGen

-- TODO to add more type that cannot be said as "pure types inside a `Gen`", if needed.

--- Non-variable arguments of the target type ---

genY_Int : {fuel : Fuel} -> (a : Type) -> Gen $ Y a Int
genY_Int = deriveGen

--- Unexpected zero and linear arguments ---

genY_given_zero_fuel : {0 fuel : Fuel} -> (a, b : Type) -> Gen $ Y a b
genY_given_zero_fuel = deriveGen

genY_given_zero_arg1 : {fuel : Fuel} -> (0 a : Type) -> (b : Type) -> Gen $ Y a b
genY_given_zero_arg1 = deriveGen

genY_given_zero_args : {fuel : Fuel} -> (0 a, b : Type) -> Gen $ Y a b
genY_given_zero_args = deriveGen

genY_given_lin_fuel : {1 fuel : Fuel} -> (a, b : Type) -> Gen $ Y a b
genY_given_lin_fuel = deriveGen

genY_given_lin_arg1 : {fuel : Fuel} -> (1 a : Type) -> (b : Type) -> Gen $ Y a b
genY_given_lin_arg1 = deriveGen

genY_given_lin_args : {fuel : Fuel} -> (1 a, b : Type) -> Gen $ Y a b
genY_given_lin_args = deriveGen

genY_given_zero_lin_args : {fuel : Fuel} -> (0 a : Type) -> (1 b : Type) -> Gen $ Y a b
genY_given_zero_lin_args = deriveGen

--- Gen for type with no constructors ---

genVoid : {fuel : Fuel} -> Gen Void
genVoid = deriveGen

--- Repeating external gens ---

genY_repX_hinted : {fuel : Fuel} -> (a, b : Type) -> Gen $ Y a b
genY_repX_hinted = deriveGen {externalHintedGens = [ `(Gen X), `(Gen X) ]}

genY_repX_autoimpl : {fuel : Fuel} -> Gen X => Gen X => (a, b : Type) -> Gen $ Y a b
genY_repX_autoimpl = deriveGen

genY_repX_both : {fuel : Fuel} -> Gen X => (a, b : Type) -> Gen $ Y a b
genY_repX_both = deriveGen {externalHintedGens = [ `(Gen X) ]}

genY_repX_both' : {fuel : Fuel} -> Gen X => Gen X => (a, b : Type) -> Gen $ Y a b
genY_repX_both' = deriveGen {externalHintedGens = [ `(Gen X), `(Gen X) ]}

--- Non-existent hinted gens ---

genY_nonex_hinted : {fuel : Fuel} -> (a, b : Type) -> Gen $ Y a b
genY_nonex_hinted = deriveGen {externalHintedGens = [ `(Gen NonExistent) ]}

genY_nonex_hinted' : {fuel : Fuel} -> (a, b : Type) -> Gen $ Y a b
genY_nonex_hinted' = deriveGen {externalHintedGens = [ `(forall a. Gen $ NonExistent a) ]}

genY_nonex_hinted'' : {fuel : Fuel} -> (a, b : Type) -> Gen $ Y a b
genY_nonex_hinted'' = deriveGen {externalHintedGens = [ `(Gen $ NonExistent a) ]}

--- Non-gen externals ---

genY_nongen_hinted_list : {fuel : Fuel} -> (a, b : Type) -> Gen $ Y a b
genY_nongen_hinted_list = deriveGen {externalHintedGens = [ `(List Int) ]}

genY_nongen_hinted_pair : {fuel : Fuel} -> (a, b : Type) -> Gen $ Y a b
genY_nongen_hinted_pair = deriveGen {externalHintedGens = [ `( (Gen X, Gen X') ) ]}

genY_nongen_hinted_dpair : {fuel : Fuel} -> (a, b : Type) -> Gen $ Y a b
genY_nongen_hinted_dpair = deriveGen {externalHintedGens = [ `( (a ** b ** Gen $ Y a b) ) ]}

genY_nongen_autoimpl_list : {fuel : Fuel} -> List Int => (a, b : Type) -> Gen $ Y a b
genY_nongen_autoimpl_list = deriveGen

genY_nongen_autoimpl_pair : {fuel : Fuel} -> (Gen X, Gen X') => (a, b : Type) -> Gen $ Y a b
genY_nongen_autoimpl_pair = deriveGen

genY_nongen_autoimpl_dpair : {fuel : Fuel} -> (a ** b ** Gen $ Y a b) => (a, b : Type) -> Gen $ Y a b
genY_nongen_autoimpl_dpair = deriveGen

--- Auto-implicits not right after the `Fuel` parameter ---

-- TODO to add if it is needed

--- Not all arguments are used ---

-- TODO to add if it is needed
