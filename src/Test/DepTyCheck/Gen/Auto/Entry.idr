||| External generation interface and aux stuff for that
module Test.DepTyCheck.Gen.Auto.Entry

import Data.Either
import public Data.Fuel

import public Debug.Reflection

import public Test.DepTyCheck.Gen -- for `Gen` data type
import public Test.DepTyCheck.Gen.Auto.Checked

%default total

-------------------------
--- Utility functions ---
-------------------------

listToVectExact : (n : Nat) -> List a -> Maybe $ Vect n a
listToVectExact Z     []      = Just []
listToVectExact (S k) (x::xs) = (x ::) <$> listToVectExact k xs
listToVectExact Z     (_::_)  = Nothing
listToVectExact (S k) []      = Nothing

-----------------------------------------
--- Utility `TTImp`-related functions ---
-----------------------------------------

--- Parsing `TTImp` stuff ---

unDPair : TTImp -> (List (Count, PiInfo TTImp, Maybe Name, TTImp), TTImp)
unDPair (IApp _ (IApp _ (IVar _ `{Builtin.DPair.DPair}) typ) (ILam _ cnt piInfo mbname _ lamTy)) =
    mapFst ((cnt, piInfo, mbname, typ)::) $ unDPair lamTy
unDPair expr = ([], expr)

--- General purpose instances ---

Eq Namespace where
  MkNS xs == MkNS ys = xs == ys

Eq Name where
  UN x   == UN y   = x == y
  MN x n == MN y m = x == y && n == m
  NS s n == NS p m = s == p && n == m
  DN x n == DN y m = x == y && n == m
  RF x   == RF y   = x == y
  _ == _ = False

----------------------------------------
--- Internal functions and instances ---
----------------------------------------

analyzeSigResult : TTImp -> Elab (ty : TypeInfo ** (Vect ty.args.length Name, List (Fin ty.args.length, TTImp)))
analyzeSigResult sigResult = do
  -- check the resulting type is `Gen`
  let IApp _ (IVar _ `{Test.DepTyCheck.Gen.Gen}) targetType = sigResult
    | _ => failAt (getFC sigResult) "The result type must be a `deptycheck`'s `Gen` applied to a type"

  -- treat the generated type as a dependent pair
  let (paramsToBeGenerated, targetType) = unDPair targetType

  -- check that all parameters of `DPair` are as expected
  paramsToBeGenerated <- for paramsToBeGenerated $ \case
    (MW, ExplicitArg, Just nm, t) => pure (nm, t)
    (_,  _,           Nothing, _) => failAt (getFC sigResult) "All arguments of dependent pair under the resulting `Gen` are expected to be named"
    _                             => failAt (getFC sigResult) "Bad lambda argument of RHS of dependent pair under the `Gen`, it must be `MW` and explicit"

  -- treat the target type as a function application
  let (targetType, targetTypeArgs) = unApp targetType

  -- check it's applied to some name
  let IVar targetTypeFC targetType = targetType
    | _ => failAt (getFC targetType) "Target type is not a simple name"

  -- check that desired `Gen` is not a generator of `Gen`s
  case targetType of
    `{Test.DepTyCheck.Gen.Gen} => failAt targetTypeFC "Target type of a derived `Gen` cannot be a `deptycheck`'s `Gen`"
    _ => pure ()

  -- check we can analyze the target type itself
  targetType <- getInfo' targetType

  -- check that there are at least non-zero constructors
  let (_::_) = targetType.cons
    | [] => fail "No constructors found for the type `\{show targetType.name}`"

  -- check the given type info corresponds to the given type application, and convert a `List` to an appropriate `Vect`
  let Just targetTypeArgs = listToVectExact targetType.args.length targetTypeArgs
    | Nothing => fail "Lengths of target type applcation and description are not equal: \{show targetTypeArgs.length} and \{show targetType.args.length}"

  -- check all the arguments of the target type are variable names, not complex expressions
  targetTypeArgs <- for targetTypeArgs $ \case
    IVar _ argName => pure argName
    nonVarArg => failAt (getFC nonVarArg) "Argument is expected to be a variable name"

  -- Here we assume, that all parameters in `parametersToBeGenerated` have different names

  -- check that all parameters to be generated are actually used inside the target type
  paramsToBeGenerated <- for paramsToBeGenerated $ \(name, ty) => case elemIndex name targetTypeArgs of
    Just found => pure (found, ty)
    Nothing => failAt (getFC ty) "Generated parameter is not used in the target type"

  pure (targetType ** (targetTypeArgs, paramsToBeGenerated))

-- This function either fails or not instead of returning some error-containing result.
-- This is due to technical limitation of the `Elab`'s `check` function.
-- TODO To think of return type of `TypeInfo` and, maybe, somewhat parsed arguments,
--      like `Vect ty.args.length $ Maybe ArgExplicitness`, like is was before.
-- TODO Also, maybe, there is a need in the result of some map from `TypeInfo` (and, maybe, `Vect` like above) to `auto-implicit | hinted`.
--      Or, at least, the filled generators manager, that remembers what already is generated (and how it is named) and
--      what is present as external (with auto-implicit or hinted).
--      In this case, it would be a stateful something.
checkTypeIsGen : TTImp -> Elab ()
checkTypeIsGen sig = do
  -- check the given expression is a type
  _ <- check {expected=Type} sig

  -- treat the given type expression as a (possibly 0-ary) function type
  (sigArgs, sigResult) <- unPiNamed sig

--  logMsg "gen.derive" 0 $ "goal's result:\n- \{show sigResult}"

  -- check and parse the resulting part of the generator function's signature
  (targetType ** (targetTypeArgs, paramsToBeGenerated)) <- analyzeSigResult sigResult

  -- check that there are at least some parameters in the signature
  let (firstArg::sigArgs) = sigArgs
    | [] => failAt (getFC sig) "No arguments in the signature, at least fuel argument must be present"

  -- check that the first argument is a correct fuel argument
  let MkArg MW ExplicitArg (MN _ _) (IVar _ `{Data.Fuel.Fuel}) = firstArg
    | _ => failAt (getFC firstArg.type) "The first argument must be an explicit unnamed runtime one of type `Fuel`"

  -- check that all arguments are omega, not erased or linear; and that all arguments are properly named
  sigArgs <- for {b = Either _ TTImp} sigArgs $ \case
    MkArg MW ImplicitArg (UN name) type => pure $ Left (Checked.ImplicitArg, name, type)
    MkArg MW ExplicitArg (UN name) type => pure $ Left (Checked.ExplicitArg, name, type)
    MkArg MW AutoImplicit (MN _ _) type => pure $ Right type

    MkArg MW ImplicitArg     _ ty => failAt (getFC ty) "All implicit arguments are expected to be named"
    MkArg MW ExplicitArg     _ ty => failAt (getFC ty) "All explicit arguments are expected to be named"
    MkArg MW AutoImplicit    _ ty => failAt (getFC ty) "Auto-implicit parameters are expected to be unnamed"

    MkArg M0 _               _ ty => failAt (getFC ty) "Erased arguments are not supported in generator signatures"
    MkArg M1 _               _ ty => failAt (getFC ty) "Linear arguments are not supported in generator signatures"
    MkArg MW (DefImplicit _) _ ty => failAt (getFC ty) "Default implicit arguments are not supported in generator signatures"
  let givenParams := lefts sigArgs
  let autoImplArgs := rights sigArgs
  --let (givenParams, autoImplArgs) := (lefts sigArgs, rights sigArgs) -- `partitionEithers sigArgs` does not reduce here somewhy :-(

  -- TODO to check whether all target type's argument names are present either in the function's arguments or in the resulting generated depedent pair.

  ?checkTypeIsGen_impl

  -- result
  --   check the resulting type is `Gen`
  --   check the `Gen`'s parameter is pure type or a dependent pair resulting a pure type
  --   check that all parts of the dependent pair are the type parameters of the target type
  --   (not sure, if needed) check that parameters of the target type are open (either a parameter of function or present in the dependent pair)
  -- arguments
  --   check all arguments are MW, not M0 or M1
  --   check the first explicit argument is `Fuel`
  --   (not sure, if needed) check all `auto` `implicit` external `Gen`'s are before the all other parameters
  --   (not sure, if needed) check that all arguments are actually used
  -- externals
  --   check there are no repetition in the external gens lists, both in auto-implicit and hinted, and also between them
  --

------------------------------
--- Functions for the user ---
------------------------------

||| The entry-point function of automatic derivation of `Gen`'s.
|||
||| Consider, you have a `data X (a : A) (b : B n) (c : C) where ...` and
||| you want a derived `Gen` for `X`.
||| Say, you want to have `a` and `c` parameters of `X` to be set by the caller and the `b` parameter to be generated.
||| For this your generator function should have a signature like `(a : A) -> (c : C) -> (n ** b : B n ** X a b c)`.
||| So, you need to define a function with this signature, say, named as `genX` and
||| to write `genX = deriveGen` as an implementation to make the body to be derived.
|||
||| Say, you want `n` to be set by the caller and, as the same time, to be an implicit argument.
||| In this case, the signature of the main function to be derived,
||| becomes `{n : _} -> (a : A) -> (c : C) -> (b : B n ** X a b c)`.
||| But still, you can use this function `deriveGen` to derive a function with such signature.
|||
||| Say, you want your generator to be parameterized with some external `Gen`'s.
||| Some of these `Gen`'s are known declared `%hint x : Gen Y`, some of them should go as an `auto` parameters.
||| Consider types `data Y where ...`, `data Z1 where ...` and `data Z2 (b : B n) where ...`.
||| For this, `auto`-parameters can be listed with `=>`-syntax in the signature.
||| External generators declared with `%hint` need to be listed separately in the implicit argument of `deriveGen`.
|||
||| For example, if you want to use `%hint` for `Gen Y` and `Gen`'s for `Z1` and `Z2` to be `auto` parameters,
||| you can define your function in the following way:
|||
|||   ```idris
|||   genX : Gen Z1 => ({n : _} -> {b : B n} -> Gen (Z2 b)) => {n : _} -> (a : A) -> (c : C) -> (b : B n ** X a b c)
|||   genX = deriveGen { externalHintedGens = [ `(Gen Y) ] }
|||   ```
|||
||| `%hint _ : Gen Y` from the current scope will be used as soon as a value of type `Y` will be needed for generation.
|||
||| Consider another example, where all generators for `Y`, `Z1` and `Z2` are means to be defined with `%hint`.
||| In this case, you are meant to declare it in the following way:
|||
|||   ```idris
|||   genX : {n : _} -> (a : A) -> (c : C) -> (b : B n ** X a b c)
|||   genX = deriveGen { externalHintedGens = [ `(Gen Z1), `({n : _} -> {b : B n} -> Gen (Z2 b)), `(Gen Y) ] }
|||   ```
|||
||| Consider also, that you may be asked for having the `Fuel` argument as the first argument in the signature
||| due to (maybe, temporary) unability of `Gen`'s to manage infinite processes of values generation.
|||
export %macro
deriveGen : {default [] externalHintedGens : List TTImp} -> Elab a
deriveGen = do
  Just signature <- goal
     | Nothing => fail "The goal signature is not found. Generators derivation must be used only for fully defined signatures"
  checkTypeIsGen signature
  for_ externalHintedGens checkTypeIsGen
  ?deriveGen_foo
