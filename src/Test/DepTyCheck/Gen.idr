module Test.DepTyCheck.Gen

import Control.Monad.Maybe
import public Control.Monad.Error.Interface
import Control.Monad.Random
import public Control.Monad.Random.Interface

import Data.Bool
import public Data.CheckedEmpty.List.Lazy
import Data.CheckedEmpty.List.Lazy.Elem
import Data.CheckedEmpty.List.Lazy.Quantifiers
import Data.CheckedEmpty.List.Lazy.Properties
import Data.Fuel
import public Data.Nat1
import Data.List
import Data.List.Lazy
import Data.List.Lazy.Extra
import Data.Vect

import Decidable.Equality

import public Language.Implicits.IfUnsolved

import Syntax.WithProof

import public Test.DepTyCheck.Gen.Emptiness
import public Test.DepTyCheck.Gen.Labels

%default total

-------------------------
--- Utility functions ---
-------------------------

randomFin : MonadRandom m => (n : Nat1) -> m $ Fin n.asNat
randomFin $ FromNat (S _) = getRandom

public export %inline
wrapLazy : (a -> b) -> Lazy a -> Lazy b
wrapLazy f = delay . f . force

%inline
wrapMaybeTaggedLazy : (a -> Maybe b) -> (tag, Lazy a) -> Maybe (tag, Lazy b)
wrapMaybeTaggedLazy f = traverse $ map delay . f . force

0 unpackTaggedLazy : Functor f => f (tag, Lazy a) -> f a
unpackTaggedLazy = map $ force . snd

-------------------------------
--- Definition of the `Gen` ---
-------------------------------

record RawGen a where
  constructor MkRawGen
  unRawGen : forall m. MonadRandom m => CanManageLabels m => m a

||| A transformation of a random computation, used when a generator is run in a special way, e.g. by `variant`
record Modifier where
  constructor MkModifier
  modify : forall m, x. MonadRandom m => m x -> m x

export
data Gen : Emptiness -> Type -> Type

0 IsNonEmpty : Gen em a -> Type

export
record GenAlternatives (0 mustBeNotEmpty : Bool) (0 em : Emptiness) (a : Type)

0 All : (Gen em a -> Type) -> GenAlternatives ne em a -> Type

data Gen : Emptiness -> Type -> Type where

  Empty : Gen MaybeEmpty a

  Pure  : a -> Gen em a

  Raw   : RawGen a -> Gen em a

  OneOf : (gs : GenAlternatives True alem a) ->
          (0 _ : All IsNonEmpty gs) =>
          (0 _ : alem `NoWeaker` em) =>
          Gen em a

  Bind  : (0 _ : biem `NoWeaker` em) =>
          RawGen c -> (c -> Gen biem a) -> Gen em a

  Labelled : Label -> (g : Gen em a) -> (0 _ : IsNonEmpty g) => Gen em a

  ||| A structured generator (a choice or another such generator) followed by a continuation.
  |||
  ||| This is a bind (or a map) which is not pushed down to the alternatives of the choice.
  ||| Semantically, it is the same as if the continuation was pushed down.
  ||| For a possibly empty continuation, it is not known whether this generator is empty;
  ||| alternatives that turn out to be empty after the continuation is applied are excluded during the sampling,
  ||| thus the distribution is the same as if empty alternatives were removed after pushing the continuation down.
  |||
  ||| The `clean` flag means that empty alternatives (after the continuation applied) were removed
  ||| if the continuation was pushed down.
  Then : (0 _ : iem `NoWeaker` em) => (0 _ : biem `NoWeaker` em) =>
         (clean : Bool) -> Gen iem c -> (c -> Gen biem a) -> Gen em a

  ||| A possibly empty generator with hidden structure, run with a modifier, followed by a continuation.
  |||
  ||| This generator is empty when the hidden one is empty;
  ||| emptiness of the continuation is not propagated through it, like through `Bind`.
  Hidden : (0 _ : MaybeEmpty `NoWeaker` em) =>
           Modifier -> Gen MaybeEmpty c -> (c -> Gen biem a) -> Gen em a

isEmpty : Gen em a -> Bool
isEmpty Empty = True
isEmpty _     = False

%inline
isNonEmpty : Gen em a -> Bool
isNonEmpty = not . isEmpty

IsNonEmpty g = isEmpty g === False

record GenAlternatives (0 mustBeNotEmpty : Bool) (0 em : Emptiness) (a : Type) where
  constructor MkGenAlts
  unGenAlts : LazyLst mustBeNotEmpty (Nat1, Lazy (Gen em a))

0 listOfAlts : GenAlternatives ne em a -> LazyLst ne $ Gen em a
listOfAlts $ MkGenAlts gs = unpackTaggedLazy gs

All p = All p . listOfAlts

0 Elem : Gen em a -> GenAlternatives ne em a -> Type
Elem g = Elem g . listOfAlts

(.totalWeight) : GenAlternatives True em a -> Nat1
(.totalWeight) = foldl1 (+) . map fst . unGenAlts

public export %inline
Gen1 : Type -> Type
Gen1 = Gen NonEmpty

||| Generator with least guarantees on emptiness.
|||
||| This type should not be used as an input argument unless it is strictly required.
||| You should prefer to be polymorphic on emptiness instead.
public export %inline
Gen0 : Type -> Type
Gen0 = Gen MaybeEmpty

%hint
0 isNonEmptyGen1 : {g : Gen1 a} -> IsNonEmpty g
isNonEmptyGen1 {g=Pure _}       = Refl
isNonEmptyGen1 {g=Raw _}        = Refl
isNonEmptyGen1 {g=OneOf _}      = Refl
isNonEmptyGen1 {g=Bind _ _}     = Refl
isNonEmptyGen1 {g=Labelled _ _} = Refl
isNonEmptyGen1 {g=Then _ _ _}   = Refl

-----------------------------
--- Very basic generators ---
-----------------------------

export
chooseAny : Random a => (0 _ : IfUnsolved ne NonEmpty) => Gen ne a
chooseAny = Raw $ MkRawGen getRandom

public export %inline
chooseAnyOf : (0 a : _) -> Random a => (0 _ : IfUnsolved ne NonEmpty) => Gen ne a
chooseAnyOf _ = chooseAny

export
choose : Random a => (0 _ : IfUnsolved ne NonEmpty) => (a, a) -> Gen ne a
choose bounds = Raw $ MkRawGen $ getRandomR bounds

export %inline
empty : Gen0 a
empty = Empty

export
label : Label -> Gen em a -> Gen em a
label l g with (isEmpty g) proof 0 prf
  label _ Empty | True  = Empty
  label l g     | False = Labelled l g

total
0 labelNonEmpty : {g : Gen em a} -> IsNonEmpty g => IsNonEmpty $ label l g
labelNonEmpty {g=Pure _}       = Refl
labelNonEmpty {g=Raw _}        = Refl
labelNonEmpty {g=OneOf _}      = Refl
labelNonEmpty {g=Bind _ _}     = Refl
labelNonEmpty {g=Labelled _ _} = Refl
labelNonEmpty {g=Then _ _ _}   = Refl
labelNonEmpty {g=Hidden _ _ _} = Refl

------------------------------------------------
--- Technical stuff for mapping alternatives ---
------------------------------------------------

mapTaggedLazy : Functor f => (a -> b) -> f (tag, Lazy a) -> f (tag, Lazy b)
mapTaggedLazy f = map $ \x => (fst x, wrapLazy f $ snd x)

mapOneOf : GenAlternatives ne iem a -> (Gen iem a -> Gen em b) -> GenAlternatives ne em b
mapOneOf $ MkGenAlts gs = MkGenAlts . flip mapTaggedLazy gs

0 allMapTaggedLazy : {0 f : a -> b} -> {xs : LazyLst ne (tag, Lazy a)} ->
                     ({x : a} -> (0 _ : Elem x $ unpackTaggedLazy xs) -> p $ f x) ->
                     All p $ unpackTaggedLazy $ mapTaggedLazy f xs
allMapTaggedLazy h = allMap $ allMapForall $ \e => h $ elemMap _ e

0 allMapOneOf : {0 f : Gen iem a -> Gen em b} ->
                {gs : GenAlternatives ne iem a} ->
                ({x : Gen iem a} -> (0 _ : Elem x gs) -> p $ f x) ->
                All p $ mapOneOf gs f
allMapOneOf {gs=MkGenAlts _} = allMapTaggedLazy

mapElem : (xs : LazyLst ne a) -> ((x : a) -> (0 _ : Elem x xs) -> b) -> LazyLst ne b
mapElem []        _ = []
mapElem (x :: xs) f = f x Here :: mapElem xs (\y, e => f y $ There e)

mapTaggedLazyElem : (xs : LazyLst ne (tag, Lazy a)) ->
                    ((x : a) -> (0 _ : Elem x $ unpackTaggedLazy xs) -> b) ->
                    LazyLst ne (tag, Lazy b)
mapTaggedLazyElem xs f = mapElem xs $ \x, e => (fst x, delay $ f (snd x) $ elemMap _ e)

mapOneOfElem : (gs : GenAlternatives ne iem a) ->
               ((g : Gen iem a) -> (0 _ : Elem g gs) -> Gen em b) ->
               GenAlternatives ne em b
mapOneOfElem $ MkGenAlts gs = MkGenAlts . mapTaggedLazyElem gs

0 allMapElem : {xs : LazyLst ne a} ->
               {0 f : (x : a) -> (0 _ : Elem x xs) -> b} ->
               ({x : a} -> (0 e : Elem x xs) -> p $ f x e) ->
               All p $ mapElem xs f
allMapElem {xs=[]}      _ = []
allMapElem {xs=x :: xs} h = h Here :: allMapElem (\e => h $ There e)

0 allMapTaggedLazyElem : {xs : LazyLst ne (tag, Lazy a)} ->
                         {0 f : (x : a) -> (0 _ : Elem x $ unpackTaggedLazy xs) -> b} ->
                         ({x : a} -> (0 e : Elem x $ unpackTaggedLazy xs) -> p $ f x e) ->
                         All p $ unpackTaggedLazy $ mapTaggedLazyElem xs f
allMapTaggedLazyElem h = allMap $ allMapElem $ \e => h $ elemMap _ e

0 allMapOneOfElem : {gs : GenAlternatives ne iem a} ->
                    {0 f : (g : Gen iem a) -> (0 _ : Elem g gs) -> Gen em b} ->
                    ({g : Gen iem a} -> (0 e : Elem g gs) -> p $ f g e) ->
                    All p $ mapOneOfElem gs f
allMapOneOfElem {gs=MkGenAlts _} = allMapTaggedLazyElem

-----------------------------
--- Emptiness tweakenings ---
-----------------------------

export
relax : (0 _ : iem `NoWeaker` em) => Gen iem a -> Gen em a
0 relaxNonEmpty : {g : Gen iem a} -> IsNonEmpty g => IsNonEmpty $ relax @{nw} g

relax @{nw} Empty           = rewrite maybeEmptyIsMinimal nw in Empty
relax $ Pure x              = Pure x
relax $ Raw x               = Raw x
relax $ OneOf @{ne} @{nw} x = OneOf @{ne} @{transitive' nw %search} x
relax $ Bind @{nw} x f      = Bind @{transitive' nw %search} x f
relax $ Labelled l x        = Labelled @{relaxNonEmpty} l $ relax x
relax $ Then @{nw} @{nw'} c x f = Then @{transitive' nw %search} @{transitive' nw' %search} c x f
relax $ Hidden @{nw} m x f  = Hidden @{transitive' nw %search} m x f

relaxNonEmpty {g=Pure _}       = Refl
relaxNonEmpty {g=Raw _}        = Refl
relaxNonEmpty {g=OneOf _}      = Refl
relaxNonEmpty {g=Bind _ _}     = Refl
relaxNonEmpty {g=Labelled _ _} = Refl
relaxNonEmpty {g=Then _ _ _}   = Refl
relaxNonEmpty {g=Hidden _ _ _} = Refl

--------------------
--- More utility ---
--------------------

0 maybeEmptyMinLeft : MaybeEmpty `NoWeaker` a -> MaybeEmpty `NoWeaker` min a b
maybeEmptyMinLeft AS = rewrite minMaybeEmptyLeft b in AS

0 maybeEmptyMinRight : {a : _} -> MaybeEmpty `NoWeaker` b -> MaybeEmpty `NoWeaker` min a b
maybeEmptyMinRight AS = rewrite minMaybeEmptyRight a in AS

nonEmpty : Gen em a -> Maybe $ Gen em a
nonEmpty Empty = Nothing
nonEmpty x     = Just x

0 nonEmptyNonEmpty : {g : Gen em a} -> IsJust (nonEmpty g) =>
                     IsNonEmpty $ fromJust $ nonEmpty g
nonEmptyNonEmpty {g=Pure _}       = Refl
nonEmptyNonEmpty {g=Raw _}        = Refl
nonEmptyNonEmpty {g=OneOf _}      = Refl
nonEmptyNonEmpty {g=Bind _ _}     = Refl
nonEmptyNonEmpty {g=Labelled _ _} = Refl
nonEmptyNonEmpty {g=Then _ _ _}   = Refl
nonEmptyNonEmpty {g=Hidden _ _ _} = Refl

mapMaybeTaggedLazy : (a -> Maybe b) -> LazyLst ne (tag, Lazy a) -> LazyLst0 (tag, Lazy b)
mapMaybeTaggedLazy = mapMaybe . wrapMaybeTaggedLazy

0 allMapMaybeJustTaggedLazy : {f : a -> Maybe b} ->
                              {xs : LazyLst ne (tag, Lazy a)} ->
                              ((x : a) ->
                               (0 _ : IsJust $ f x) ->
                               p $ fromJust $ f x) ->
                              All p $ unpackTaggedLazy $ mapMaybeTaggedLazy f xs
allMapMaybeJustTaggedLazy h = allMap $ allMapMaybeJust helper
  where
    helper : (x : (tag, Lazy a)) ->
             (0 _ : IsJust $ wrapMaybeTaggedLazy f x) ->
             p $ force $ snd $ fromJust $ wrapMaybeTaggedLazy f x
    helper (w, x) _ with (f x) proof 0 prf
      _ | Just y = do
        let yIsJust : IsJust (f x) = rewrite prf in ItIsJust
        let Refl : y === fromJust (f x) = rewrite prf in Refl
        h x yIsJust

namespace OneOf

  public export
  data AltsNonEmpty : Bool -> Emptiness -> Type where
    NT : AltsNonEmpty True   NonEmpty
    Sx : AltsNonEmpty altsNe MaybeEmpty

  export %defaulthint
  altsNonEmptyTrue : {em : _} -> AltsNonEmpty True em
  altsNonEmptyTrue {em=NonEmpty}   = NT
  altsNonEmptyTrue {em=MaybeEmpty} = Sx

mkOneOfMaybeEmpty : (xs : LazyLst altsNe (Nat1, Lazy (Gen alem a))) ->
                    (0 _ : All IsNonEmpty $ unpackTaggedLazy xs) =>
                    Gen0 a
mkOneOfMaybeEmpty []                  = Empty
mkOneOfMaybeEmpty (x :: xs) @{_ :: _} = OneOf $ MkGenAlts $ x :: xs

mkOneOf : {em : _} ->
          (0 _ : alem `NoWeaker` em) =>
          (0 _ : AltsNonEmpty altsNe em) =>
          LazyLst altsNe (Nat1, Lazy (Gen alem a)) ->
          Gen em a
mkOneOf {em=NonEmpty} @{nw} @{NT} xs with 0 (nonEmptyIsMaximal nw)
  _ | Refl = OneOf @{allTrue isNonEmptyGen1} $ MkGenAlts xs
mkOneOf {em=MaybeEmpty} xs =
  mkOneOfMaybeEmpty (mapMaybeTaggedLazy nonEmpty xs)
    @{allMapMaybeJustTaggedLazy {f=nonEmpty} $ \_, _ => nonEmptyNonEmpty}

--------------------------
--- Running generators ---
--------------------------

||| A stack of continuations that are yet to be applied to a value generated by some generator
data Conts : Type -> Type -> Type where
  Nil  : Conts a a
  (::) : (a -> Gen em b) -> Conts b c -> Conts a c

allDetermValues' : Gen em a -> Conts a b -> LazyList b
allDetermValues' Empty            _         = []
allDetermValues' (Pure x)         []        = [x]
allDetermValues' (Pure x)         (k :: ks) = assert_total allDetermValues' (k x) ks
allDetermValues' (Raw {})         _         = [] -- here we take only determinicstic values, no raw gens
allDetermValues' (OneOf gs)       ks        = toLazyList (unGenAlts gs) >>= \(_, g) => allDetermValues' (assert_smaller gs g) ks
allDetermValues' (Bind {})        _         = [] -- here we take only determinicstic values, no raw gens
allDetermValues' (Labelled _ g)   ks        = allDetermValues' g ks
allDetermValues' (Then _ g k)     ks        = allDetermValues' g (k :: ks)
allDetermValues' (Hidden {})      _         = [] -- here we take only determinicstic values, no raw gens

||| Returns a lazy list of all values that this generator can generate, except for those values which use raw generators, like `choose` or `chooseAny`.
export
allDetermValues : Gen em a -> LazyList a
allDetermValues g = allDetermValues' g []

--- Non-empty generators ---

export
unGen1 : MonadRandom m => (labels : CanManageLabels m) => Gen1 a -> m a
unGen1 $ Pure x         = pure x
unGen1 $ Raw sf         = sf.unRawGen
unGen1 $ OneOf @{_} @{nw} oo with 0 (nonEmptyIsMaximal nw)
  _ | Refl = assert_total unGen1 . force . pickWeighted oo.unGenAlts . finToNat =<< randomFin oo.totalWeight
unGen1 $ Bind @{nw} x f with 0 (nonEmptyIsMaximal nw)
  _ | Refl = x.unRawGen >>= unGen1 . f
unGen1 $ Labelled l x   = manageLabel l >> unGen1 x
unGen1 $ Then @{nw} @{nw'} _ x f with 0 (nonEmptyIsMaximal nw)
  _ | Refl with 0 (nonEmptyIsMaximal nw')
    _ | Refl = assert_total unGen1 x >>= assert_total unGen1 . f

export
unGenAll' : RandomGen g => (seed : g) -> Gen1 a -> Stream (g, a)
unGenAll' seed gen = do
  let sv@(seed, _) = runRandom seed $ unGen1 {m=Rand} gen
  sv :: unGenAll' seed gen

export
unGenAll : RandomGen g => (seed : g) -> Gen1 a -> Stream a
unGenAll = map snd .: unGenAll'

||| Picks one random value from a generator
export
pick1 : CanInitSeed g m => Functor m => Gen1 a -> m a
pick1 gen = initSeed <&> \s => evalRandom s $ unGen1 gen

--- Possibly empty generators ---

||| The result of a sampling attempt
data Sampled a
  = ||| A value is generated
    Val a
  | ||| The generator turned out to be structurally empty, i.e. empty regardless of values of raw generators.
    ||| No raw generator was run during an attempt with such result.
    ||| Structurally empty alternatives are excluded from choices, as if they were removed when generators were composed.
    Rej
  | ||| The generator is not structurally empty, but it failed after some raw generator was run
    Fail

||| Labels which were met during the current sampling attempt, but not yet passed to the labels manager.
|||
||| Labels are held until it is known that they would not be cancelled by a structurally empty result.
||| This is known for sure once some raw generator is run.
Pending : Type
Pending = SnocList Label

%inline
flush : CanManageLabels m => Pending -> m ()
flush [<] = pure ()
flush ls  = for_ (ls <>> []) manageLabel

||| The weight of all given alternatives
totalWeightOf : (Nat1, x) -> List (Nat1, x) -> Nat1
totalWeightOf (w, _) = foldl (\acc, y => acc + fst y) w

||| Picks an alternative like `pickWeighted` do, also returning the list of the rest alternatives
extractWeighted : (Nat1, x) -> List (Nat1, x) -> Nat -> (x, Lazy (List (Nat1, x)))
extractWeighted (_, x)         []        _ = (x, [])
extractWeighted (FromNat n, x) (y :: ys) k = if k < n then (x, y :: ys) else do
  let (z, rest) = extractWeighted y ys (k `minus` n)
  (z, (FromNat n, x) :: rest)

||| Turns structural emptiness into a failure, for the case when some raw generator was run before
%inline
committed : Functor m => Pending -> m (Pending, Sampled a) -> m (Pending, Sampled a)
committed ls = map $ \case
  (_, Rej) => (ls, Fail)
  r        => r

||| Checks whether the given generator followed by given continuations is structurally empty.
|||
||| No randomness is involved, the generator is examined until the first value or the first raw generator.
covering
structEmpty : Gen em a -> Conts a b -> Bool

||| Checks whether all the given alternatives are structurally empty, stopping at the first non-empty one.
|||
||| This is written explicitly, because `all` from the prelude, being implemented through `foldMap`,
||| looks at every element of a list, which makes the check exponential in the depth of the generator.
covering
allStructEmpty : LazyLst ne (Nat1, Lazy (Gen em c)) -> Conts c b -> Bool
allStructEmpty []             _  = True
allStructEmpty ((_, g) :: gs) ks = structEmpty g ks && allStructEmpty gs ks

structEmpty Empty            _         = True
structEmpty (Pure x)         []        = False
structEmpty (Pure x)         (k :: ks) = structEmpty (k x) ks
structEmpty (Raw _)          _         = False
structEmpty (Bind _ _)       _         = False
structEmpty (Labelled _ g)   ks        = structEmpty g ks
structEmpty (OneOf oo)       ks        = allStructEmpty oo.unGenAlts ks
structEmpty (Then _ g k)     ks        = structEmpty g $ k :: ks
structEmpty (Hidden _ g _)   _         = structEmpty g []

||| A tree of weighted alternatives for repeated picking with removal; zero weight marks removed subtrees
data WTree : Type -> Type where
  Tip : WTree x
  Lf  : Nat -> x -> WTree x
  Br  : Nat -> WTree x -> WTree x -> WTree x

weight : WTree x -> Nat
weight Tip        = 0
weight (Lf w _)   = w
weight (Br w _ _) = w

br : WTree x -> WTree x -> WTree x
br l r = Br (weight l + weight r) l r

||| Builds a balanced tree of the given number of first elements, returning the rest elements
covering
buildWTree : Nat -> List (Nat1, x) -> (WTree x, List (Nat1, x))
buildWTree 0 xs             = (Tip, xs)
buildWTree _ []             = (Tip, [])
buildWTree 1 ((w, x) :: xs) = (Lf w.asNat x, xs)
buildWTree n xs             = do
  let h = n `div` 2
  let (l, xs) = buildWTree h xs
  let (r, xs) = buildWTree (n `minus` h) xs
  (br l r, xs)

||| Picks an element by an index less than the total weight, and removes it from the tree
pickRemove : WTree x -> Nat -> Maybe (x, WTree x)
pickRemove Tip        _ = Nothing
pickRemove (Lf _ x)   _ = Just (x, Tip)
pickRemove (Br _ l r) k = if k < weight l
  then pickRemove l k <&> \(x, l) => (x, br l r)
  else pickRemove r (k `minus` weight l) <&> \(x, r) => (x, br l r)

mutual

  ||| Picks one of alternatives and samples it.
  |||
  ||| Structurally empty alternatives are excluded, i.e. each non-empty alternative is picked with probability
  ||| proportional to its weight among all non-empty ones.
  ||| The first attempt is made as if there are no empty alternatives,
  ||| when it fails, structurally empty alternatives are looked for directly,
  ||| until the first non-empty alternative is found; the rest is done by repeated attempts.
  covering
  sampleAlts : MonadRandom m => CanManageLabels m =>
               Pending -> List (Nat1, Lazy (Gen em c)) -> Conts c b -> m (Pending, Sampled b)
  sampleAlts ls []        _  = pure (ls, Rej)
  sampleAlts ls (x :: xs) ks = do
    i <- randomFin $ totalWeightOf x xs
    let (g, rest) = extractWeighted x xs $ finToNat i
    r <- sample ls g ks
    case snd r of
      Rej => case dropWhile (\y => structEmpty (force $ snd y) ks) rest of
        []   => pure (ls, Rej)
        rest => sampleTree ls (fst $ buildWTree (length rest) rest) ks
      _   => pure r

  ||| Repeatedly picks one of alternatives until some appears not to be structurally empty
  covering
  sampleTree : MonadRandom m => CanManageLabels m =>
               Pending -> WTree (Lazy (Gen em c)) -> Conts c b -> m (Pending, Sampled b)
  sampleTree ls t ks = do
    let Just w = toNat1 $ weight t
      | Nothing => pure (ls, Rej)
    i <- randomFin w
    let Just (g, t) = pickRemove t $ finToNat i
      | Nothing => pure (ls, Rej)
    r <- sample ls g ks
    case snd r of
      Rej => sampleTree ls t ks
      _   => pure r

  covering
  sample : MonadRandom m => CanManageLabels m => Pending -> Gen em a -> Conts a b -> m (Pending, Sampled b)
  sample ls Empty             _         = pure (ls, Rej)
  sample ls (Pure x)          []        = pure (ls, Val x)
  sample ls (Pure x)          (k :: ks) = sample ls (k x) ks
  sample ls (Raw sf)          ks        = do flush ls; x <- sf.unRawGen; committed [<] $ sample [<] (Pure {em=NonEmpty} x) ks
  sample ls (Bind x f)        ks        = do flush ls; c <- x.unRawGen; committed [<] $ sample [<] (f c) ks
  sample ls (Labelled l x)    ks        = sample (ls :< l) x ks
  sample ls (OneOf oo)        ks        = sampleAlts ls (toList oo.unGenAlts) ks
  sample ls (Then _ g k)      ks        = sample ls g (k :: ks)
  sample ls (Hidden md g k)   ks        = do
    (ls', r) <- md.modify $ sample ls g []
    case r of
      Val x => committed ls' $ sample ls' (k x) ks
      Rej   => pure (ls, Rej)
      Fail  => pure (ls', Fail)

export
unGen : MonadRandom m => MonadError () m => (labels : CanManageLabels m) => Gen em a -> m a
unGen g = do
  (ls, r) <- assert_total $ sample [<] g []
  case r of
    Val x => flush ls $> x
    Fail  => flush ls >> throwError ()
    Rej   => throwError ()

export %inline
unGen' : MonadRandom m => (labels : CanManageLabels m) => Gen em a -> m $ Maybe a
unGen' = runMaybeT . unGen {m=MaybeT m}

export
unGenTryAll' : RandomGen g => (seed : g) -> Gen em a -> Stream (g, Maybe a)
unGenTryAll' seed gen = do
  let sv@(seed, _) = runRandom seed $ runMaybeT $ unGen {m=MaybeT Rand} gen
  sv :: unGenTryAll' seed gen

export
unGenTryAll : RandomGen g => (seed : g) -> Gen em a -> Stream $ Maybe a
unGenTryAll = map snd .: unGenTryAll'

export
unGenTryN : RandomGen g => (n : Nat) -> g -> Gen em a -> LazyList a
unGenTryN n = mapMaybe id .: take (limit n) .: unGenTryAll

||| Tries once to pick a random value from a generator
export
pick : CanInitSeed g m => Functor m => Gen em a -> m $ Maybe a
pick gen = initSeed <&> flip evalRandom (unGen' gen)

||| Tries to pick a random value from a generator, returning the number of unsuccessful attempts, if generated successfully
export
pickTryN : CanInitSeed g m => Functor m => (n : Nat) -> Gen em a -> m $ Maybe (Fin n, a)
pickTryN n g = initSeed <&> \s => head' (withIndex $ unGenTryN n s g) >>= \(i, x) => natToFin i n <&> (,x)

-- TODO To add config and Reader for that.
--      This config should contain attempts count for each `unGen` (including those in combinators)
--      Current `unGen` should be renamed to `unGen1` and not be exported.
--      Current `unGenTryN` should be changed returning `LazyList (a, g)` and
--      new `unGen` should be implemented trying `retry` times from config using this (`g` must be stored to restore correct state of seed).

---------------------------------------
--- Standard combination interfaces ---
---------------------------------------

--- `RawGen` ---

Functor RawGen where
  map f $ MkRawGen sf = MkRawGen $ f <$> sf

Applicative RawGen where
  pure x = MkRawGen $ pure x
  MkRawGen x <*> MkRawGen y = MkRawGen $ x <*> y

--- `Gen` ---
export
Functor (Gen em)
0 mapNonEmpty : {g : Gen iem a} -> IsNonEmpty g => IsNonEmpty $ f <$> g

Functor (Gen em) where
  map f $ Empty          = Empty
  map f $ Pure x         = Pure $ f x
  map f $ Raw sf         = Raw $ f <$> sf
  -- Mapping is not pushed down to alternatives, to not to accumulate pending mappings in nested generators
  map f g@(OneOf _)      = Then @{reflexive} @{nonEmptyIsStrongest} False g $ Pure . f
  map f g@(Bind {})      = Then @{reflexive} @{nonEmptyIsStrongest} False g $ Pure . f
  map f $ Labelled l x   = Labelled @{mapNonEmpty} l $ map f x
  map f g@(Then {})      = Then @{reflexive} @{nonEmptyIsStrongest} False g $ Pure . f
  map f g@(Hidden {})    = Then @{reflexive} @{nonEmptyIsStrongest} False g $ Pure . f

mapNonEmpty {g=Pure _}       = Refl
mapNonEmpty {g=Raw _}        = Refl
mapNonEmpty {g=OneOf _}      = Refl
mapNonEmpty {g=Bind _ _}     = Refl
mapNonEmpty {g=Labelled _ _} = Refl
mapNonEmpty {g=Then _ _ _}   = Refl
mapNonEmpty {g=Hidden _ _ _} = Refl

||| Bind; the `clean` flag tells whether empty alternatives would be removed if the continuation was pushed down to them
bindWith : (clean : Bool) -> Gen lem a -> (a -> Gen rem b) -> Gen (min lem rem) b
bindWith _ Empty                _  = rewrite minMaybeEmptyLeft rem in Empty
bindWith _ (Pure x)             nf = relax @{rightNoWeakerMin} $ nf x
bindWith _ (Raw g)              nf = Bind @{rightNoWeakerMin} g nf
bindWith c (Labelled l x)       nf = label l $ bindWith c x nf
-- The continuation is not pushed down: for a choice and possibly empty continuation, each alternative would be checked
-- for being empty, and anyway pending continuations would accumulate in nested generators.
-- Instead, the continuation is applied during the sampling, and empty alternatives are excluded then.
bindWith c g@(Bind {})          nf = Then @{leftNoWeakerMin} @{rightNoWeakerMin} c g nf
bindWith c g@(Hidden {})        nf = Then @{leftNoWeakerMin} @{rightNoWeakerMin} c g nf
bindWith c g@(OneOf _)          nf = Then @{leftNoWeakerMin} @{rightNoWeakerMin} c g nf
bindWith c g@(Then {})          nf = Then @{leftNoWeakerMin} @{rightNoWeakerMin} c g nf

||| Shows a `Then` which starts with a raw or a hidden generator as such generator,
||| like it would be if the continuation was pushed down.
||| This is used to preserve the order of random draws in the applicative composition.
asBind : Gen em a -> Gen em a
asBind g@(Then @{nw} @{nw'} c x k) = case assert_total asBind x of
  Bind @{nw''} y f    => Bind @{rewrite sym $ minSame em in minNoWeaker (transitive' nw'' nw) nw'} y $ \v => bindWith c (f v) k
  Hidden @{nwh} m y f => Hidden @{transitive' nwh nw} m y $ \v => bindWith c (f v) k
  _                   => g
asBind g = g

0 asBindNonEmpty : {g : Gen em a} -> IsNonEmpty g => IsNonEmpty $ asBind g
asBindNonEmpty {g=Pure _}       = Refl
asBindNonEmpty {g=Raw _}        = Refl
asBindNonEmpty {g=OneOf _}      = Refl
asBindNonEmpty {g=Bind _ _}     = Refl
asBindNonEmpty {g=Labelled _ _} = Refl
asBindNonEmpty {g=Hidden _ _ _} = Refl
asBindNonEmpty {g=Then _ x _} with (assert_total asBind x)
  _ | Bind _ _     = Refl
  _ | Hidden _ _ _ = Refl
  _ | Empty        = Refl
  _ | Pure _       = Refl
  _ | Raw _        = Refl
  _ | OneOf _      = Refl
  _ | Labelled _ _ = Refl
  _ | Then _ _ _   = Refl

private infixl 3 <**>, <***>

(<**>) : (g : Gen lem $ a -> b) -> (h : Gen rem a) -> Gen (min lem rem) b
0 apNonEmpty : {g, h : _} -> IsNonEmpty g => IsNonEmpty h => IsNonEmpty $ g <**> h

(<***>) : (g : Gen lem $ a -> b) -> (h : Gen rem a) -> Gen (min lem rem) b
0 apNonEmpty' : {g, h : _} -> IsNonEmpty g => IsNonEmpty h => IsNonEmpty $ g <***> h

g <**> h = assert_total $ asBind g <***> asBind h
apNonEmpty = apNonEmpty' @{asBindNonEmpty} @{asBindNonEmpty}

g <***> h with (isEmpty g) proof 0 prfLeft | (isEmpty h) proof 0 prfRight
  Empty <***> _ | _ | _ = rewrite minMaybeEmptyLeft rem in Empty
  _ <***> Empty | _ | _ = rewrite minMaybeEmptyRight lem in Empty

  Pure f <***> g | _ | _ = f <$> relax @{rightNoWeakerMin} g
  g <***> Pure x | _ | _ = relax @{leftNoWeakerMin} g <&> \f => f x

  Raw sfl <***> Raw sfr | _ | _ = Raw $ sfl <*> sfr

  Labelled l x <***> y | _     | False = Labelled @{apNonEmpty} l $ x <**> y
  x <***> Labelled l y | False | _     = Labelled @{apNonEmpty} l $ x <**> y

  OneOf @{ne} @{nw} oo <***> g | _ | False =
      OneOf @{allMapOneOf $ \e => apNonEmpty @{indexAll e ne}}
            @{minNoWeakerLeft nw} $
        mapOneOf oo $ \x => assert_total $ x <**> g
  Then @{nw} @{nw'} c x f <***> g | _ | False =
    Then @{transitive' nw leftNoWeakerMin} @{minNoWeakerLeft nw'} c x $ \y => f y <**> g

  g <***> OneOf @{ne} @{nw} oo | False | _ =
    OneOf @{allMapOneOf $ \e => apNonEmpty @{%search} @{indexAll e ne}}
          @{minNoWeakerRight nw} $
      mapOneOf oo $ \x => assert_total $ g <**> x
  g <***> Then @{nw} @{nw'} c x f | False | _ =
    Then @{transitive' nw rightNoWeakerMin} @{minNoWeakerRight nw'} c x $ \y => g <**> f y

  -- Emptiness of a hidden generator must be found out before any raw generator is run
  Hidden @{nw} m x f <***> g | _ | _ =
    Hidden @{maybeEmptyMinLeft nw} m x $ \c => f c <**> g
  g <***> Hidden @{nw} m x f | _ | _ =
    Hidden @{maybeEmptyMinRight nw} m x $ \c => g <**> f c

  Bind @{nw} x f <***> Raw y | _ | _ =
    Bind @{minNoWeakerLeft nw}  x $ \c => f c <**> Raw y
  Raw y <***> Bind @{nw} x f | _ | _ =
    Bind @{minNoWeakerRight nw} x $ \c => Raw y <**> f c

  Bind @{lnw} x f <***> Bind @{rnw} y g | _ | _ =
    Bind @{minNoWeaker lnw rnw} [| (x, y) |] $ \(l, r) => f l <**> g r

apNonEmpty' with (isEmpty g) proof 0 prfLeft | (isEmpty h) proof 0 prfRight
  apNonEmpty' {g=Empty}        {h}              | True  | _     impossible
  apNonEmpty' {g}              {h=Empty}        | _     | True  impossible

  apNonEmpty' {g=Pure _}       {h=Pure _}       | _     | _     = Refl
  apNonEmpty' {g=Pure _}       {h=Raw _}        | _     | _     = Refl
  apNonEmpty' {g=Pure _}       {h=OneOf _}      | _     | _     = Refl
  apNonEmpty' {g=Pure _}       {h=Bind _ _}     | _     | _     = Refl
  apNonEmpty' {g=Pure _}       {h=Labelled _ _} | _     | _     = Refl

  apNonEmpty' {g=Raw _}        {h=Pure _}       | _     | _     = Refl
  apNonEmpty' {g=OneOf _}      {h=Pure _}       | _     | _     = Refl
  apNonEmpty' {g=Bind _ _}     {h=Pure _}       | _     | _     = Refl
  apNonEmpty' {g=Labelled _ _} {h=Pure _}       | _     | _     = Refl

  apNonEmpty' {g=Raw _}        {h=Raw _}        | _     | _     = Refl

  apNonEmpty' {g=Labelled _ _} {h=Raw _}        | _     | False = Refl
  apNonEmpty' {g=Labelled _ _} {h=OneOf _}      | _     | False = Refl
  apNonEmpty' {g=Labelled _ _} {h=Bind _ _}     | _     | False = Refl
  apNonEmpty' {g=Labelled _ _} {h=Labelled _ _} | _     | False = Refl

  apNonEmpty' {g=Raw _}        {h=Labelled _ _} | False | False = Refl
  apNonEmpty' {g=OneOf _}      {h=Labelled _ _} | False | False = Refl
  apNonEmpty' {g=Bind _ _}     {h=Labelled _ _} | False | False = Refl

  apNonEmpty' {g=OneOf _}      {h=Raw _}        | False | False = Refl
  apNonEmpty' {g=OneOf _}      {h=OneOf _}      | False | False = Refl
  apNonEmpty' {g=OneOf _}      {h=Bind _ _}     | False | False = Refl

  apNonEmpty' {g=Bind _ _}     {h=OneOf _}      | False | False = Refl
  apNonEmpty' {g=Raw _}        {h=OneOf _}      | False | False = Refl

  apNonEmpty' {g=Raw _}        {h=Bind _ _}     | _     | False = Refl
  apNonEmpty' {g=Bind _ _}     {h=Raw _}        | _     | False = Refl

  apNonEmpty' {g=Bind _ _}     {h=Bind _ _}     | _     | False = Refl

  apNonEmpty' {g=Pure _}         {h=Then _ _ _}     | _ | _ = Refl
  apNonEmpty' {g=Pure _}         {h=Hidden _ _ _}   | _ | _ = Refl
  apNonEmpty' {g=Then _ _ _}     {h=Pure _}         | _ | _ = Refl
  apNonEmpty' {g=Hidden _ _ _}   {h=Pure _}         | _ | _ = Refl

  apNonEmpty' {g=Labelled _ _}   {h=Then _ _ _}     | _ | False = Refl
  apNonEmpty' {g=Labelled _ _}   {h=Hidden _ _ _}   | _ | False = Refl
  apNonEmpty' {g=Then _ _ _}     {h=Labelled _ _}   | False | False = Refl
  apNonEmpty' {g=Hidden _ _ _}   {h=Labelled _ _}   | False | False = Refl

  apNonEmpty' {g=OneOf _}        {h=Then _ _ _}     | False | False = Refl
  apNonEmpty' {g=OneOf _}        {h=Hidden _ _ _}   | False | False = Refl
  apNonEmpty' {g=Then _ _ _}     {h=Raw _}          | False | False = Refl
  apNonEmpty' {g=Then _ _ _}     {h=OneOf _}        | False | False = Refl
  apNonEmpty' {g=Then _ _ _}     {h=Bind _ _}       | False | False = Refl
  apNonEmpty' {g=Then _ _ _}     {h=Then _ _ _}     | False | False = Refl
  apNonEmpty' {g=Then _ _ _}     {h=Hidden _ _ _}   | False | False = Refl
  apNonEmpty' {g=Hidden _ _ _}   {h=OneOf _}        | False | False = Refl
  apNonEmpty' {g=Raw _}          {h=Then _ _ _}     | False | False = Refl
  apNonEmpty' {g=Bind _ _}       {h=Then _ _ _}     | False | False = Refl
  apNonEmpty' {g=Hidden _ _ _}   {h=Then _ _ _}     | False | False = Refl

  apNonEmpty' {g=Hidden _ _ _}   {h=Raw _}          | False | False = Refl
  apNonEmpty' {g=Hidden _ _ _}   {h=Bind _ _}       | False | False = Refl
  apNonEmpty' {g=Hidden _ _ _}   {h=Hidden _ _ _}   | False | False = Refl
  apNonEmpty' {g=Raw _}          {h=Hidden _ _ _}   | False | False = Refl
  apNonEmpty' {g=Bind _ _}       {h=Hidden _ _ _}   | False | False = Refl

export
Applicative (Gen em) where
  pure = Pure
  g <*> h = rewrite sym $ minSame em in g <**> h

private infixl 1 >>==

||| Bind which removes empty alternatives (on sampling) when the continuation is possibly empty
(>>==) : {rem : _} -> Gen lem a -> (a -> Gen rem b) -> Gen (min lem rem) b
g >>== nf = bindWith (rem == MaybeEmpty) g nf

export
{em : _} -> Monad (Gen em) where
  g >>= h = rewrite sym $ minSame em in g >>== h

-----------------------------------------
--- Detour: special list of lazy gens ---
-----------------------------------------

namespace GenAlternatives

  export %inline
  Nil : GenAlternatives False em a
  Nil = MkGenAlts []

  export %inline
  (::) : (0 _ : lem `NoWeaker` em) =>
         (0 _ : rem `NoWeaker` em) =>
         (0 _ : IfUnsolved e True) =>
         (0 _ : IfUnsolved em NonEmpty) =>
         (0 _ : IfUnsolved lem em) =>
         (0 _ : IfUnsolved rem em) =>
         Lazy (Gen lem a) -> Lazy (GenAlternatives e rem a) -> GenAlternatives ne em a
  x :: xs = MkGenAlts $ (1, relax x) :: mapTaggedLazy relax xs.unGenAlts

  -- This concatenation breaks relative proportions in frequencies of given alternative lists
  public export %inline
  (++) : (0 _ : lem `NoWeaker` em) =>
         (0 _ : rem `NoWeaker` em) =>
         (0 _ : IfUnsolved lem em) =>
         (0 _ : IfUnsolved rem em) =>
         (0 _ : IfUnsolved nel False) =>
         (0 _ : IfUnsolved ner False) =>
         GenAlternatives nel lem a -> Lazy (GenAlternatives ner rem a) -> GenAlternatives (nel || ner) em a
  xs ++ ys = MkGenAlts $ mapTaggedLazy relax xs.unGenAlts ++ mapTaggedLazy relax ys.unGenAlts

  public export %inline
  length : GenAlternatives ne em a -> Nat
  length = length . unGenAlts

  export %inline
  processAlternatives : (Gen em a -> Gen em b) -> GenAlternatives ne em a -> GenAlternatives ne em b
  processAlternatives = flip mapOneOf

  export %inline
  processAlternativesMaybe : (Gen em a -> Maybe $ Lazy (Gen em b)) -> GenAlternatives ne em a -> GenAlternatives False em b
  processAlternativesMaybe f = MkGenAlts . mapMaybe (traverse $ f . force) . unGenAlts

  export %inline
  processAlternatives'' : (Gen em a -> GenAlternatives neb em b) -> GenAlternatives nea em a -> GenAlternatives (nea && neb) em b
  processAlternatives'' f = mapGens where

    mapWeight : forall a, nea. (Nat1 -> Nat1) -> GenAlternatives nea em a -> GenAlternatives nea em a
    mapWeight f = MkGenAlts . map (mapFst f) . unGenAlts

    mapGens : GenAlternatives nea em a -> GenAlternatives (nea && neb) em b
    mapGens xs = MkGenAlts $ xs.unGenAlts `bind` \(w, x) => unGenAlts $ mapWeight (w *) $ f x

  export %inline
  processAlternatives' : (Gen em a -> GenAlternatives ne em b) -> GenAlternatives ne em a -> GenAlternatives ne em b
  processAlternatives' f xs = rewrite sym $ andSameNeutral ne in processAlternatives'' f xs

  export %inline
  relax : GenAlternatives True em a -> GenAlternatives ne em a
  relax = MkGenAlts . relaxT . unGenAlts

  export %inline
  strengthen : GenAlternatives ne em a -> Maybe $ GenAlternatives True em a
  strengthen = map MkGenAlts . strengthen . unGenAlts

  export
  Functor (GenAlternatives ne em) where
    map = processAlternatives . map

  export
  Applicative (GenAlternatives ne em) where
    pure x = [ pure x ]
    xs <*> ys = flip processAlternatives' xs $ flip processAlternatives ys . (<*>)

  export
  Alternative (GenAlternatives False em) where
    empty = []
    xs <|> ys = MkGenAlts $ xs.unGenAlts <|> ys.unGenAlts

  -- implementation for `Monad` is below --

export
Cast (LazyLst ne a) (GenAlternatives ne em a) where
  cast = MkGenAlts . map (\x => (1, pure x))

public export %inline
altsFromList : LazyLst ne a -> GenAlternatives ne em a
altsFromList = cast

----------------------------------
--- Creation of new generators ---
----------------------------------

||| Choose one of the given generators uniformly.
|||
||| All the given generators are treated as independent, i.e. `oneOf [oneOf [a, b], c]` is not the same as `oneOf [a, b, c]`.
||| In this example case, generator `oneOf [a, b]` and generator `c` will have the same probability in the resulting generator.
export
oneOf : {em : _} ->
        (0 _ : alem `NoWeaker` em) =>
        (0 _ : AltsNonEmpty altsNe em) =>
        (0 _ : IfUnsolved alem em) =>
        (0 _ : IfUnsolved altsNe $ em /= MaybeEmpty) =>
        GenAlternatives altsNe alem a -> Gen em a
oneOf = mkOneOf . unGenAlts

||| Choose one of the given generators with probability proportional to the given value, treating all source generators independently.
|||
||| This function treats given generators in the same way as `oneOf` do, but the resulting generator uses generator
||| from the given list the more frequently, the higher number is has.
||| If generator `g1` has the frequency `n1` and generator `g2` has the frequency `n2`, than `g1` will be used `n1/n2` times
||| more frequently than `g2` in the resulting generator (in case when `g1` and `g2` always generate some value).
export
frequency : {em : _} ->
            (0 _ : alem `NoWeaker` em) =>
            (0 _ : AltsNonEmpty altsNe em) =>
            (0 _ : IfUnsolved alem em) =>
            (0 _ : IfUnsolved altsNe $ em /= MaybeEmpty) =>
            LazyLst altsNe (Nat1, Lazy (Gen alem a)) -> Gen em a
frequency = oneOf . MkGenAlts

||| Choose one of the given values uniformly.
|||
||| This function is equivalent to `oneOf` applied to list of `pure` generators per each value.
export
elements : {em : _} ->
           (0 _ : AltsNonEmpty altsNe em) =>
           (0 _ : IfUnsolved em NonEmpty) =>
           (0 _ : IfUnsolved altsNe $ em /= MaybeEmpty) =>
           LazyLst altsNe a -> Gen em a
elements = oneOf {alem=NonEmpty} . altsFromList

export %inline
elements' : Foldable f => (0 _ : IfUnsolved f List) => f a -> Gen0 a
elements' xs = elements $ fromList $ toList xs

------------------------------
--- Analysis of generators ---
------------------------------

altsOrSelf : (self : Gen em a) -> (0 _ : IsNonEmpty self) =>
             (xs : LazyLst ne (Nat1, Lazy (Gen em a))) -> (0 _ : All IsNonEmpty $ unpackTaggedLazy xs) =>
             GenAlternatives True em a
altsOrSelf self []                       = MkGenAlts [(1, self)]
altsOrSelf _    (x :: xs) @{_} @{_ :: _} = MkGenAlts $ x :: xs

0 altsOrSelfNonEmpty : {self : Gen em a} -> {xs : LazyLst ne (Nat1, Lazy (Gen em a))} ->
                       {0 sne : IsNonEmpty self} -> {0 ane : All IsNonEmpty $ unpackTaggedLazy xs} ->
                       All IsNonEmpty $ altsOrSelf self xs @{sne} @{ane}
altsOrSelfNonEmpty {xs=[]}                   = [sne]
altsOrSelfNonEmpty {xs=_ :: _} {ane=a :: as} = a :: as

||| Removes empty alternatives, leaving the given generator if all of them are empty.
|||
||| When `deep` is set, structurally empty alternatives are removed, otherwise only those which are obviously empty.
cleanAlts : (deep : Bool) -> (self : Gen em a) -> (0 _ : IsNonEmpty self) =>
            LazyLst ne (Nat1, Lazy (Gen em a)) -> GenAlternatives True em a
cleanAlts deep self @{sne} xs =
  altsOrSelf self @{sne}
    (mapMaybeTaggedLazy nonEmpty $ the (LazyLst0 _) $ if deep then filter (\x => not $ assert_total structEmpty (force $ snd x) []) xs else relaxF xs)
    @{allMapMaybeJustTaggedLazy {f=nonEmpty} $ \_, _ => nonEmptyNonEmpty}

0 cleanAltsNonEmpty : {self : Gen em a} -> {xs : LazyLst ne (Nat1, Lazy (Gen em a))} -> {0 sne : IsNonEmpty self} ->
                      All IsNonEmpty $ cleanAlts deep self @{sne} xs
cleanAltsNonEmpty = altsOrSelfNonEmpty

||| Shallow alternatives of a generator.
|||
||| If the given generator is made by one of `oneOf`, `frequency` or `elements`,
||| this function returns alternatives which this generators contains.
||| Otherwise it returns a single-element alternative list containing given generator.
|||
||| In a sense, this function is a reverse function of `oneOf`, i.g.
||| `oneOf $ alternativesOf g` must be equivalent to `g` and
||| `alternativesof $ oneOf gs` must be equivalent to `gs`.
export
alternativesOf : Gen em a -> GenAlternatives True em a
0 alternativesOfNonEmpty : {g : Gen em a} -> IsNonEmpty g => All IsNonEmpty $ alternativesOf g

alternativesOf $ OneOf oo     = mapOneOf oo relax
alternativesOf $ Labelled l x = mapOneOfElem (alternativesOf x) $ \g, e => Labelled l g @{indexAll e alternativesOfNonEmpty}
-- The continuation is pushed down; empty alternatives are removed, as if they were removed when the continuation was pushed down
alternativesOf g@(Then {iem} {c} @{nw} @{nw'} cl x f) = do
  let bindAlt : Gen iem c -> Gen em a
      bindAlt y = relax @{rewrite sym $ minSame em in minNoWeaker nw nw'} $ bindWith cl y f
  cleanAlts cl g @{Refl} (mapOneOf (assert_total alternativesOf x) $ assert_total bindAlt).unGenAlts
alternativesOf g              = [g]

alternativesOfNonEmpty {g=Pure _}        = [Refl]
alternativesOfNonEmpty {g=Raw _}         = [Refl]
alternativesOfNonEmpty {g=OneOf @{ne} _} = allMapOneOf $ \e => relaxNonEmpty @{indexAll e ne}
alternativesOfNonEmpty {g=Bind _ _}      = [Refl]
alternativesOfNonEmpty {g=Labelled _ _}  = allMapOneOfElem $ \_ => Refl
alternativesOfNonEmpty {g=Then _ _ _}    = cleanAltsNonEmpty
alternativesOfNonEmpty {g=Hidden _ _ _}  = [Refl]

||| Any depth alternatives fetching.
|||
||| Alternatives of depth `0` are meant to be a single-item alternatives list with the original generator,
||| alternatives of depth `1` are those returned by the `alternativesOf` function,
||| alternatives of depth `n+1` are alternatives of all alternatives of depth `n` being flattened into a single alternatives list.
export
deepAlternativesOf : (depth : Nat) -> Gen em a -> GenAlternatives True em a
deepAlternativesOf 0     gen = [ gen ]
deepAlternativesOf 1     gen = alternativesOf gen
deepAlternativesOf (S k) gen = processAlternatives' alternativesOf $ deepAlternativesOf k gen

||| Whether the given generator is a choice, possibly followed by some continuations
startsWithChoice : Gen em a -> Bool
startsWithChoice (OneOf _)    = True
startsWithChoice (Then _ y _) = startsWithChoice y
startsWithChoice _            = False

||| Returns generator with internal structure hidden for `alternativesOf`,
||| except for an empty generator, which would still be returned as an empty generator.
|||
||| This function must not change distribution when the resulting generator used with usual `Gen` combinators.
|||
||| Please notice that this function does NOT influence to the result of `deepAlternativesOf`, if depth is increased by 1.
export
forgetAlternatives : Gen em a -> Gen em a
0 forgetAlternativesNonEmpty : {g : Gen iem a} -> IsNonEmpty g => IsNonEmpty $ forgetAlternatives g

forgetAlternatives g@(OneOf {})   = Labelled "forgetAlternatives" $ OneOf @{[Refl]} $ MkGenAlts [(1, g)]
forgetAlternatives g@(Then @{nw} @{nw'} c x k) =
  if startsWithChoice x
    then Labelled "forgetAlternatives" $ OneOf @{[Refl]} $ MkGenAlts [(1, Then @{nw} @{nw'} c x k)]
    else g
forgetAlternatives $ Labelled l x = Labelled @{forgetAlternativesNonEmpty} l $ forgetAlternatives x
forgetAlternatives g              = g

forgetAlternativesNonEmpty {g=Pure _}       = Refl
forgetAlternativesNonEmpty {g=Raw _}        = Refl
forgetAlternativesNonEmpty {g=OneOf _}      = Refl
forgetAlternativesNonEmpty {g=Bind _ _}     = Refl
forgetAlternativesNonEmpty {g=Labelled _ _} = Refl
forgetAlternativesNonEmpty {g=Then _ x _} with (startsWithChoice x)
  _ | True  = Refl
  _ | False = Refl
forgetAlternativesNonEmpty {g=Hidden _ _ _} = Refl

||| Returns generator with internal structure hidden to anything, including combinators,
||| except for an empty generator, which would still be returned as an empty generator.
|||
||| Apply with care! Don't use until you understand what you are doing!
||| Most probably, you need the lighter version of this function called `forgetAlternatives`.
||| The difference is that `forgetAlternatives` do not influence on the resulting distribution,
||| when this function may ruin it unexpectedly.
|||
||| But despite `forgetAlternatives`, this function acts on `deepAlternativesOf`
||| like `forgetAlternatives` acts on `alternativesOf`,
||| i.e. `deepAlternativesOf` would give a single alternative for any depth
||| being applied to the result of this function.
export
forgetStructure : {em : _} -> Gen em a -> Gen em a
forgetStructure Empty             = Empty
forgetStructure g@(Raw _)         = g
forgetStructure g {em=NonEmpty}   = Raw $ MkRawGen $ unGen1 g
forgetStructure g {em=MaybeEmpty} = Hidden (MkModifier id) g $ Pure {em=NonEmpty}

public export
processAlternatives : (Gen em a -> Gen em b) -> Gen em a -> GenAlternatives True em b
processAlternatives f = processAlternatives f . alternativesOf

public export
mapAlternativesOf : (a -> b) -> Gen em a -> GenAlternatives True em b
mapAlternativesOf = processAlternatives . map

public export %inline
mapAlternativesWith : Gen em a -> (a -> b) -> GenAlternatives True em b
mapAlternativesWith = flip mapAlternativesOf

-- Priority is chosen to be able to use these operators without parenthesis
-- in expressions of lists, i.e. involving operators `::` and `++`.
export
infix 8 `mapAlternativesOf`
      , `mapAlternativesWith`

export
{em : _} -> Monad (GenAlternatives True em) where
  xs >>= f = flip processAlternatives' xs $ alternativesOf . (>>= oneOf . f)

----------------------------------------
--- Additional composition functions ---
----------------------------------------

||| Associative composition of two generators, merging shallow alternatives of given two generators
|||
||| This operation being applied to arguments `a` and `b` is *not* the same as `oneOf [a, b]`.
||| Generator ``a `withAlts` b`` has equal probabilities of all shallow alternatives of generators `a` and `b`.
||| For example, when there are generators
||| ```idris
||| g1 = oneOf [elems [0, 1, 2, 3], elems [4, 5]]
||| g2 = oneOf elemts [10, 11, 12, 13, 14, 15]
||| ```
||| generator ``g1 `withAlts` g2`` would be equivalent to
||| `oneOf [elems [0, 1, 2, 3], elems [4, 5], pure 10, pure 11, pure 12, pure 13, pure 14, pure 15]`.
|||
||| In other words, ``a `withAlts` b`` must be equivalent to `oneOf $ alternativesOf a ++ alternativesOf b`.
export %inline
withAlts : {em : _} -> Gen em a -> Gen em a -> Gen em a
a `withAlts` b = oneOf $ alternativesOf a ++ alternativesOf b

-- As of `<|>`
export
infixr 2 `withAlts`

||| Associative composition of two generators, merging deep alternatives of given two generators
|||
||| This operation being applied to arguments `a` and `b` is *not* the same as `oneOf [a, b]`.
||| Generator ``a `withDeepAlts` b`` has equal probabilities of all deep alternatives of generators `a` and `b`.
||| For example, when there are generators
||| ```idris
||| g1 = oneOf [elems [0, 1, 2, 3], elems [4, 5]]
||| g2 = oneOf elemts [10, 11, 12, 13, 14, 15]
||| ```
||| generator ``withDeepAlts n g1 g2`` with `n >= 2` would be equivalent to
||| `oneOf elements [0, 1, 2, 3, 4, 5, 10, 11, 12, 13, 14, 15]`.
|||
||| In other words, ``withDeepAlts d a b`` must be equivalent to `oneOf $ deepAlternativesOf d a ++ deepAlternativesOf d b`.
export %inline
withDeepAlts : {em : _} -> (depth : Nat) -> Gen em a -> Gen em a -> Gen em a
withDeepAlts depth a b = oneOf $ deepAlternativesOf depth a ++ deepAlternativesOf depth b

-----------------
--- Filtering ---
-----------------

||| A function that behaves for `Gen0` like `guard` function for `Alternative`.
|||
||| It can be used as a handy way to filter directly in do-notation.
||| Generally, try to avoid direct filterings since they can lead to very ineffective generation.
public export
guard : Bool -> Gen0 ()
guard True  = pure ()
guard False = empty

export
mapMaybe : (a -> Maybe b) -> Gen em a -> Gen0 b
mapMaybe f g = maybe empty pure . f =<< relax g

export
suchThat_withPrf : Gen em a -> (p : a -> Bool) -> Gen0 $ a `Subset` So . p
suchThat_withPrf g p = mapMaybe lp g where
  lp : a -> Maybe $ a `Subset` So . p
  lp x with (p x) proof 0 prf
    _ | True  = Just $ Element x $ eqToSo prf
    _ | False = Nothing

export infixl 4 `suchThat`

public export
suchThat : Gen em a -> (a -> Bool) -> Gen0 a
suchThat g p = fst <$> suchThat_withPrf g p

export
suchThat_dec : Gen em a -> ((x : a) -> Dec $ prop x) -> Gen0 $ Subset a prop
suchThat_dec g f = mapMaybe d g where
  d : a -> Maybe $ Subset a prop
  d x = case f x of
    Yes p => Just $ Element x p
    No  _ => Nothing

||| Filters the given generator so, that resulting values `x` are solutions of equation `y = f x` for given `f` and `y`.
export
suchThat_invertedEq : DecEq b => Gen em a -> (y : b) -> (f : a -> b) -> Gen0 $ Subset a $ \x => y = f x
suchThat_invertedEq g y f = g `suchThat_dec` \x => y `decEq` f x

||| More elegant version of `suchThat_withPrf` for fuelled generators.
|||
||| Tries to repeat generation until there is some fuel, and fallback to `suchThat_withPrf` in case there isn't.
export
retryUntil_withPrf : (p : a -> Bool) -> (Fuel -> Gen em a) -> Fuel -> Gen0 $ a `Subset` So . p
retryUntil_withPrf p f Dry           = f Dry `suchThat_withPrf` p
retryUntil_withPrf p f fl'@(More fl) = do
  x <- relax $ f fl'
  case @@ p x of
    (True ** prf) => pure $ Element x $ eqToSo prf
    (False ** _)  => retryUntil_withPrf p f fl

||| More elegant version of `suchThat` for fuelled generators.
|||
||| Tries to repeat generation until there is some fuel, and fallback to `suchThat` in case there isn't.
public export %inline
retryUntil : (p : a -> Bool) -> (Fuel -> Gen em a) -> Fuel -> Gen0 a
retryUntil p = map fst .: retryUntil_withPrf p

||| More elegant version of `suchThat_dec` for fuelled generators.
|||
||| Tries to repeat generation until there is some fuel, and fallback to `suchThat_dec` in case there isn't.
export
retryUntil_dec : (p : (x : a) -> Dec $ prop x) -> (Fuel -> Gen em a) -> Fuel -> Gen0 $ Subset a prop
retryUntil_dec p f Dry           = f Dry `suchThat_dec` p
retryUntil_dec p f fl'@(More fl) = do
  x <- relax $ f fl'
  case p x of
    Yes p => pure $ Element x p
    No _  => retryUntil_dec p f fl

-------------------------------
--- Variation in generation ---
-------------------------------

iterate : Nat -> (a -> a) -> a -> a
iterate Z     _ = id
iterate (S n) f = iterate n f . f

-- TODO to reimplement `variant` to ensure that preserves the structure as far as it can.
export
variant : {em : _} -> Nat -> Gen em a -> Gen em a
variant _ Empty               = Empty
variant Z gen                 = gen
variant n gen {em=NonEmpty}   = Raw $ MkRawGen $ iterate n independent $ unGen1 gen
variant n gen {em=MaybeEmpty} = Hidden (MkModifier $ iterate n independent) gen $ Pure {em=NonEmpty}

-----------------------------
--- Particular generators ---
-----------------------------

export
listOf : {em : _} -> {default (choose (0, 10)) length : Gen em Nat} -> Gen em a -> Gen em $ List a
listOf g = sequence $ List.replicate !length g

export
vectOf : {em : _} -> {n : Nat} -> Gen em a -> Gen em $ Vect n a
vectOf = sequence . replicate n
