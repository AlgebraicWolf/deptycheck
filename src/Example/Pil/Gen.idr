module Example.Pil.Gen

import Data.List

import public Example.DecEqPrime
import public Example.Gen
import public Example.Pil.Lang

%default total

------------------
--- Generation ---
------------------

--- Expressions ---

export
constExprGen : Gen a -> Gen (Expression ctx a)
constExprGen = map C

maybeToList : Maybe a -> List a
maybeToList (Just x) = [x]
maybeToList Nothing = []

export
varExprGen' : {a : Type} -> {ctx : Context} -> DecEq' Type => List (Expression ctx a)
varExprGen' = varExpressions {- this could be `oneOf $ map pure (fromList varExpressions)` if `Gen` could fail (contain zero) -} where
  varExpressions : List (Expression ctx a)
  varExpressions = map varExpr varsOfType where
    varExpr : (n : Name ** lk : Lookup n ctx ** reveal lk = a) -> Expression ctx a
    varExpr (n ** _ ** prf) = rewrite sym prf in V n

    varsOfType : List (n : Name ** lk : Lookup n ctx ** reveal lk = a)
    varsOfType = varsOfTypeOfCtx $ addLookups ctx
      where
        addLookups : (ctx : Context) -> List (n : Name ** ty : Type ** lk : Lookup n ctx ** reveal lk = ty)
        addLookups [] = []
        addLookups ((n, ty)::xs) = (n ** ty ** Here ty ** Refl) ::
                                   map (\(n ** ty ** lk ** lk_ty) => (n ** ty ** There lk ** lk_ty)) (addLookups xs)

        varsOfTypeOfCtx : List (n : Name ** ty : Type ** lk : Lookup n ctx ** reveal lk = ty) -> List (n : Name ** lk : Lookup n ctx ** reveal lk = a)
        varsOfTypeOfCtx [] = []
        varsOfTypeOfCtx ((n ** ty ** lk ** lk_ty)::xs) = maybeToList varX ++ varsOfTypeOfCtx xs where
          varX : Maybe (n : Name ** lk : Lookup n ctx ** reveal lk = a)
          varX = case decEq' ty a of
            (Yes ty_a) => Just (n ** lk ** trans lk_ty ty_a)
            No => Nothing

export
unaryExprGen : Gen (a -> a) -> Gen (Expression ctx a) -> Gen (Expression ctx a)
unaryExprGen gg sub = [| U gg sub |]

export
binaryExprGen : Gen (a -> a -> a) -> Gen (Expression ctx a) -> Gen (Expression ctx a)
binaryExprGen ggg sub = [| B ggg sub sub |]

commonGens : {a : Type} -> {ctx : Context} -> Gen a -> DecEq' Type => (n ** Vect n $ Gen $ Expression ctx a)
commonGens g = ( _ ** [constExprGen g] ++ map pure (fromList varExprGen') )

export
exprGen : (szBound : Nat) -> {a : Type} -> Gen a -> Gen (a -> a) -> Gen (a -> a -> a) -> {ctx : Context} -> DecEq' Type => Gen (Expression ctx a)
exprGen Z g _ _ = oneOf $ snd $ commonGens g
exprGen (S n) g gg ggg = oneOf $ snd (commonGens g) ++
                               [ unaryExprGen gg (exprGen n g gg ggg)
                               , binaryExprGen ggg (exprGen n g gg ggg)
                               ]

--- Statements ---

lookupGen : (ctx : Context) -> NonEmpty ctx => Gen (n : Name ** Lookup n ctx)
lookupGen ctx = let (lks@(_::_) ** _) = mapLk ctx in
                oneOf $ map pure $ fromList lks
  where
    mapLk : (ctx : Context) -> NonEmpty ctx => (l : List (n : Name ** Lookup n ctx) ** NonEmpty l)
    mapLk [(n, ty)] = ( [(n ** Here ty)] ** IsNonEmpty )
    mapLk ((n, ty)::xs@(_::_)) = ( (n ** Here ty) :: map (\(n ** lk) => (n ** There lk)) (fst $ mapLk xs) ** IsNonEmpty )

noDeclsNoRec : (ctx : Context) ->
               (genExpr : {a : Type} -> {ctx : Context} -> Gen (Expression ctx a)) =>
               Vect 3 $ Gen (Statement ctx ctx)
noDeclsNoRec ctx =
  [ pure nop
  , case ctx of
    []     => pure nop -- this is returned because `oneOf` requires `Vect`, thus all cases must have equal size.
    (_::_) => do (n ** _) <- lookupGen ctx
                 pure $ n #= !genExpr
  , do pure $ print !(genExpr {a=String})
  ]

declsNoRec : (pre : Context) ->
             (genTy : Gen Type) =>
             (genName : Gen Name) =>
             Gen (post ** Statement pre post)
declsNoRec pre = do
  ty <- genTy
  n <- genName
  pure ((n, ty)::pre ** ty. n)

mutual

  export
  noDeclStmtGen : (bound : Nat) ->
                  (ctx : Context) ->
                  Gen Type =>
                  Gen Name =>
                  (genExpr : {a : Type} -> {ctx : Context} -> Gen (Expression ctx a)) =>
                  Gen (Statement ctx ctx)
  noDeclStmtGen Z     ctx = oneOf $ noDeclsNoRec ctx
  noDeclStmtGen (S n) ctx = oneOf $
    noDeclsNoRec ctx ++
    [ do (inside_for ** init) <- stmtGen n ctx
         (_ ** body) <- stmtGen n inside_for
         pure $ for init !genExpr !(noDeclStmtGen n inside_for) body
    , pure $ if__ !genExpr (snd !(stmtGen n ctx)) (snd !(stmtGen n ctx))
    , pure $ !(noDeclStmtGen n ctx) *> !(noDeclStmtGen n ctx)
    , pure $ block $ snd !(stmtGen n ctx)
    ]

  export
  stmtGen : (bound : Nat) ->
            (pre : Context) ->
            (genTy : Gen Type) =>
            (genName : Gen Name) =>
            ({a : Type} -> {ctx : Context} -> Gen (Expression ctx a)) =>
            Gen (post ** Statement pre post)
  stmtGen Z     pre = oneOf $ [declsNoRec pre, pure (pre ** !(noDeclStmtGen Z pre))]
  stmtGen (S n) pre = oneOf $
    [declsNoRec pre] ++
    [ pure (pre ** !(noDeclStmtGen n pre))
    , do (mid ** l) <- stmtGen n pre
         (post ** r) <- stmtGen n mid
         pure (post ** l *> r)
    ]
