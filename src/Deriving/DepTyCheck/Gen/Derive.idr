||| Interfaces for using a derivator
module Deriving.DepTyCheck.Gen.Derive

import public Control.Monad.Error.Interface

import public Data.SortedMap
import public Data.SortedMap.Dependent
import public Data.SortedSet

import public Deriving.DepTyCheck.Util.Reflection

%default total

---------------------------------------------------
--- Simplest `Gen` signature, user for requests ---
---------------------------------------------------

public export
record GenSignature where
  constructor MkGenSignature
  targetType : TypeInfo
  {auto 0 targetTypeCorrect : AllTyArgsNamed targetType}
  givenParams : SortedSet $ Fin targetType.args.length

namespace GenSignature

  export
  characteristics : GenSignature -> (String, List Nat)
  characteristics $ MkGenSignature ty giv = (show ty.name, toNatList giv)

public export %inline
(.generatedParams) : (sig : GenSignature) -> SortedSet $ Fin sig.targetType.args.length
sig.generatedParams = fromList (allFins sig.targetType.args.length) `difference` sig.givenParams

export
SingleLogPosition GenSignature where
  logPosition sig = do
    let uName : Arg -> Maybe UserName
        uName $ MkArg {name=Just $ UN un, _} = Just un
        uName _ = Nothing
    let givs = sig.givenParams.asList <&> \idx => maybe (show idx) (\n => "\{show idx}(\{show n})") $ uName $ index' sig.targetType.args idx
    "\{logPosition sig.targetType}[\{joinBy ", " givs}]"

public export
Eq GenSignature where
  (==) = (==) `on` characteristics

public export
Ord GenSignature where
  compare = comparing characteristics

----------------------
--- Main interface ---
----------------------

public export
interface Elaboration m => NamesInfoInTypes => ConsRecs => CanonicGen m where
  callGen : (sig : GenSignature) -> (fuel : TTImp) -> Vect sig.givenParams.size TTImp -> m TTImp

export
CanonicGen m => MonadTrans t => Monad (t m) => CanonicGen (t m) where
  callGen sig fuel params = lift $ callGen sig fuel params

--- Low-level derivation interface ---

export
canonicSig : GenSignature -> TTImp
canonicSig sig = piAll returnTy $ MkArg MW ExplicitArg Nothing `(Data.Fuel.Fuel) :: (arg <$> Prelude.toList sig.givenParams) where
  -- TODO Check that the resulting `TTImp` reifies to a `Type`? During this check, however, all types must be present in the caller's context.

  arg : Fin sig.targetType.args.length -> Arg
  arg idx = let MkArg {name, type, _} = index' sig.targetType.args idx in MkArg MW ExplicitArg name type

  returnTy : TTImp
  returnTy = `(Test.DepTyCheck.Gen.Gen Test.DepTyCheck.Gen.Emptiness.MaybeEmpty ~(buildDPair targetTypeApplied generatedArgs)) where

    targetTypeApplied : TTImp
    targetTypeApplied = foldr apply (extractTargetTyExpr sig.targetType) $ reverse $ sig.targetType.args <&> \(MkArg {name, piInfo, _}) => do
                          let name = stname name
                          case piInfo of
                            ExplicitArg   => (.$ var name)
                            ImplicitArg   => \f => namedApp f name $ var name
                            DefImplicit _ => \f => namedApp f name $ var name
                            AutoImplicit  => (`autoApp` var name)

    generatedArgs : List (Name, TTImp)
    generatedArgs = mapMaybeI sig.targetType.args $ \idx, (MkArg {name, type, _}) =>
                      ifThenElse .| contains idx sig.givenParams .| Nothing .| Just (stname name, type)

-- Complementary to `canonicSig`
export
callCanonic : (0 sig : GenSignature) -> (topmost : Name) -> (fuel : TTImp) -> Vect sig.givenParams.size TTImp -> TTImp
callCanonic _ = foldl app .: appFuel

public export
interface DerivatorCore where
  canonicBody : CanonicGen m => GenSignature -> Name -> m $ List Clause

-- NOTE: Implementation of `internalGenBody` cannot know the `Name` of the called gen, thus it cannot use `callInternalGen` function directly.
--       It have to use `callGen` function from `CanonicGen` interface instead.
--       But `callInternalGen` function is still present here because, in some sense, it is a complementary to `internalGenSig`.
--       Internals and changes in the implementation of `internalGenSig` influence on the implementation of `callInternalGen`.

--- Expressions generation utils ---

defArgNames : {sig : GenSignature} -> Vect sig.givenParams.size String
defArgNames = sig.givenParams.asVect <&> show . argName . index' sig.targetType.args

export %inline
canonicDefaultLHS' : (namesFun : String -> String) -> GenSignature -> Name -> (fuel : String) -> TTImp
canonicDefaultLHS' nmf sig n fuel = callCanonic sig n .| bindVar fuel .| bindVar . nmf <$> defArgNames

export %inline
canonicDefaultRHS' : (namesFun : String -> String) -> GenSignature -> Name -> (fuel : TTImp) -> TTImp
canonicDefaultRHS' nmf sig n fuel = callCanonic sig n fuel .| varStr . nmf <$> defArgNames

export %inline
canonicDefaultLHS : GenSignature -> Name -> (fuel : String) -> TTImp
canonicDefaultLHS = canonicDefaultLHS' id

export %inline
canonicDefaultRHS : GenSignature -> Name -> (fuel : TTImp) -> TTImp
canonicDefaultRHS = canonicDefaultRHS' id

---------------------------------
--- External-facing functions ---
---------------------------------

export
deriveCanonical : DerivatorCore => CanonicGen m => GenSignature -> Name -> m (Decl, Decl)
deriveCanonical sig name = pure (export' name (canonicSig sig), def name !(canonicBody sig name))
