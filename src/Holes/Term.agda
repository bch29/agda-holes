module Holes.Term where

open import Holes.Prelude

-- TODO: This logically ought to be abstract, but that breaks the `cong!` macro
-- because when it is abstract, `⌞ x ⌟ ≡ x` does not hold (at least
-- definitionally). Look into a way of fixing this.
⌞_⌟ : ∀ {a}{A : Set a} → A → A
⌞ x ⌟ = x

private
  -- Given a term, if it is a hole, returns the list of arguments given to it.
  -- Otherwise returns nothing.

  toHole : Term → Maybe (List (Arg Term))
  -- First three arguments are the parameters of `⌞_⌟`, respectively the universe
  -- level `a`, the set `A` and the explicit parameter (i.e. the thing in the
  -- hole). So these are ignored.
  toHole (def (quote ⌞_⌟) (_ ∷ _ ∷ _ ∷ args)) = just args
  toHole _ = nothing

-- A HoleyTerm is an Agda term that has a single 'hole' in it, where another
-- term fits

data HoleyTerm : Set where
  hole : (args : List (Arg Term)) → HoleyTerm
  var : (x : ℕ) (args : List (Arg HoleyTerm)) → HoleyTerm
  con : (c : Name) (args : List (Arg HoleyTerm)) → HoleyTerm
  def : (f : Name) (args : List (Arg HoleyTerm)) → HoleyTerm
  lam : (v : Visibility) (holeyAbs : Abs HoleyTerm) → HoleyTerm
  pi : (a : Arg HoleyTerm) (b : Abs HoleyTerm) → HoleyTerm
  agda-sort : (s : Sort) → HoleyTerm
  lit : (l : Literal) → HoleyTerm
  unknown : HoleyTerm
  meta : (x : Meta) (args : List (Arg HoleyTerm)) → HoleyTerm

data HoleyErr : Set where
  noHole : HoleyErr
  unsupportedTerm : Term → HoleyErr
  mismatchedHoleTerms : HoleyErr

printHoleyErr : Term → HoleyErr → List ErrorPart
printHoleyErr goalLhs noHole
  = strErr "LHS of goal type contains no hole:"
  ∷ termErr goalLhs
  ∷ []
printHoleyErr goalLhs (unsupportedTerm x)
  = strErr "Goal type's LHS"
  ∷ termErr goalLhs
  ∷ strErr "contains unsupported term"
  ∷ termErr x
  ∷ []
printHoleyErr goalLhs mismatched-hole-terms
  = strErr "Terms in different holes failed to unify with each other."
  ∷ strErr "Check that every hole has an identical term in it."
  ∷ strErr "Offending term:"
  ∷ termErr goalLhs
  ∷ []

private
  mapArglist : {A B : Set} → (A → B) → List (Arg A) → List (Arg B)
  mapArglist = map ∘ mapArg

-- Converts a HoleyTerm to a regular term by filling in the hole with some other
-- given term which is a function of the number of binders encountered on the
-- way to the hole.
--
-- Free variables inside the holey term are detected and modified using the
-- provided function, because otherwise they might interact wrongly with
-- surrounding terms in the result.

{-# TERMINATING #-}
fillHoley : (ℕ → ℕ) → ℕ → (ℕ → List (Arg Term) → Term) → HoleyTerm → Term
fillHoley freeVarMod binderDepth filler = go binderDepth
  where
  go : ℕ → HoleyTerm → Term
  go depth (hole args) = filler depth args
  go _ (lit l) = lit l
  go depth (var x args) =
    let freeVar = not (x <? depth)
    in var (if freeVar then freeVarMod x else x) (mapArglist (go depth) args)
  go depth (con c args) = con c (mapArglist (go depth) args)
  go depth (def f args) = def f (mapArglist (go depth) args)
  go depth (meta x args) = meta x (mapArglist (go depth) args)
  go depth (lam v (abs s holey)) = lam v (abs s (go depth holey))
  go depth (pi (arg v a) (abs s b)) =
    pi (arg v (go depth a))
       (abs s (go depth b))
  go _ (agda-sort s) = agda-sort s
  go _ unknown = unknown

-- Converts a HoleyTerm to a regular term which abstracts a variable that is
-- used to fill the hole.
--
-- The `suc` function is provided for `fillHoley`'s `freeVarMod` parameter.
-- This is because the binding level of any free variables in the given term
-- will need to be lifted over the new lambda that we're introducing. Otherwise
-- they'll end up referring to the new lambda's variables, which is wrong. Bound
-- variables inside the given term don't need to be changed.

holeyToLam : HoleyTerm → Term
holeyToLam holey = lam visible (abs "hole" (fillHoley suc 0 var holey))

-- Converts a HoleyTerm to a regular term by filling in the hole with a constant
-- other term.

fillHoley′ : (List (Arg Term) → Term) → HoleyTerm → Term
fillHoley′ filler = fillHoley id 0 (λ _ → filler)

private
  mapPair : ∀ {a b x y}{A : Set a}{B : Set b}{X : Set x}{Y : Set y} → (A → X) → (B → Y) → A × B → X × Y
  mapPair f g (x , y) = f x , g y

  pushArg : ∀ {A B : Set} → Arg (A × B) → A × Arg B
  pushArg (arg i (x , y)) = x , arg i y

  mutual
    argHelper : (List (Arg HoleyTerm) → HoleyTerm) → List (Arg Term) → Result HoleyErr (List Term × HoleyTerm)
    argHelper buildHoley
      = fmap (mapPair concat buildHoley ∘ unzip)
      ∘ traverse (fmap pushArg ∘ traverse termToHoleyHelper)

    {-# TERMINATING #-}
    termToHoleyHelper : Term → Result HoleyErr (List Term × HoleyTerm)
    termToHoleyHelper term with toHole term
    termToHoleyHelper term | just args = ok (term ∷ [] , hole args)
    termToHoleyHelper (lit l) | nothing = ok ([] , lit l)
    termToHoleyHelper (var x args) | nothing = argHelper (var x) args
    termToHoleyHelper (con c args) | nothing = argHelper (con c) args
    termToHoleyHelper (def f args) | nothing = argHelper (def f) args
    termToHoleyHelper (meta x args) | nothing = argHelper (meta x) args
    termToHoleyHelper (lam v (abs s t)) | nothing =
      mapPair id (λ h → lam v (abs s h)) <$> termToHoleyHelper t
    termToHoleyHelper (pi (arg v a) (abs s b)) | nothing =
      termToHoleyHelper a >>=² λ ts₁ a′ →
      termToHoleyHelper b >>=² λ ts₂ b′ →
      return (ts₁ ++ ts₂ , pi (arg v a′) (abs s b′))
    termToHoleyHelper unknown | nothing = ok ([] , unknown)
    termToHoleyHelper (agda-sort s) | nothing = ok ([] , agda-sort s)
    ... | _ = err (unsupportedTerm term)

-- If a term has a hole in it, specified by ⌞_⌟ around a subterm, returns a
-- HoleyTerm with the hole removed.

termToHoley : Term → Result HoleyErr HoleyTerm
termToHoley term = proj₂ <$> termToHoleyHelper term

-- A variant of `termToHoley` that also returns the term in the hole. If there
-- are multiple holes, returns all of the terms that are in them.

termToHoley′ : Term → Result HoleyErr (List Term × HoleyTerm)
termToHoley′ = termToHoleyHelper

private
  unifyAll : List Term → TC (Maybe Term)
  unifyAll [] = return nothing
  unifyAll (x ∷ xs) = traverse- (unify x) xs >> return (just x)

checkedTermToHoley : Term → RTC HoleyErr (Term × HoleyTerm)
checkedTermToHoley term =
  liftResult (termToHoley′ term) >>=² λ holeTerms holey →
  liftTC (unifyAll holeTerms)
    ⟨ catchRTC ⟩
  throw mismatchedHoleTerms >>= λ
  { nothing → return (fillHoley′ (λ _ → unknown) holey , hole [])
  ; (just holeTerm) → return (holeTerm , holey)
  }

-- A variant of `termToHoley` that also returns the term in the hole, and checks
-- that the holey term is valid by unifying it with the original term. The list
-- of error parts given is thrown as a type error if the term could not be
-- converted to a holey term. Also, if there are no holes, treats the entire
-- expression as a hole.

checkedTermToHoley′ : (HoleyErr → List ErrorPart) → Term → TC (Term × HoleyTerm)
checkedTermToHoley′ error =
  runRTC (typeError ∘ error) ∘ checkedTermToHoley

-- These macros are useful for debugging and testing

macro
  -- Given a holey term, expands to a function which accepts something to go in
  -- the hole.

  lambdaIntoHole : Term → Term → TC ⊤
  lambdaIntoHole term target =
    checkedTermToHoley′ (λ _ → strErr "Unsupported term for holiness or no hole:"
                                ∷ termErr term
                                ∷ []) term >>=² λ _ →
    unify target ∘ holeyToLam

  -- Given a holey term, expands to the quoted form of a function which accepts
  -- something to go in the hole.

  lambdaIntoHole′ : Term → Term → TC ⊤
  lambdaIntoHole′ term target =
    checkedTermToHoley′ (λ _ → strErr "Unsupported term for holiness or no hole:"
                                ∷ termErr term
                                ∷ []) term >>=² λ _ result →
    quoteTC (holeyToLam result) >>=
    unify target

  -- Quotes a holey term, reifying its abstract syntax tree.

  quoteHoley : Term → Term → TC ⊤
  quoteHoley term target =
    checkedTermToHoley′ (λ _ → strErr "Unsupported term for holiness or no hole:"
                                ∷ termErr term
                                ∷ []) term >>=² λ _ result →
    quoteTC result >>= unify target

  -- Quotes a holey term and also the term in the hole. Expanded type is always
  -- `Term × HoleyTerm`.

  quoteHoley′ : Term → Term → TC ⊤
  quoteHoley′ term target =
    checkedTermToHoley′ (λ _ → strErr "Unsupported term for holiness or no hole:"
                                ∷ termErr term
                                ∷ []) term >>=
    quoteTC >>= unify target

private
  module Tests where
    open PropEq using (_≡_; refl)

    data Fin : ℕ → Set where
      zero : ∀ {n} → Fin (suc n)
      suc : ∀ {n} → Fin n → Fin (suc n)

    eqTyped : ∀ {a}(A : Set a) → A → A → Set a
    eqTyped _ x y = x ≡ y

    syntax eqTyped A x y = x ≡[ A ] y

    -- Holes don't have to match the type of the bigger expression
    test1 : lambdaIntoHole (4 + 5 * length ⌞ 1 ∷ [] ⌟ + 7) ≡ λ hole → 4 + 5 * length hole + 7
    test1 = refl

    -- Holes can be around functions
    test2 : lambdaIntoHole (⌞ _+_ ⌟ 3 4) ≡[ ((ℕ → ℕ → ℕ) → ℕ) ] λ hole → hole 3 4
    test2 = refl

    -- Holey terms can contain free variables
    test3 : ∀ x y z → lambdaIntoHole (⌞ x + y ⌟ + z) ≡ λ hole → hole + z
    test3 x y z = refl

    -- Multiple holes are possible
    test4 : ∀ x y z → lambdaIntoHole (x + ⌞ y + z ⌟ * ⌞ y + z ⌟ + y * z) ≡ λ hole → x + hole * hole + y * z
    test4 x y z = refl

    -- Holes into Π types
    test5 : ∀ x y → lambdaIntoHole (Fin ⌞ x + y ⌟ → ℕ) ≡ λ hole → Fin hole → ℕ
    test5 x y = refl

    -- Constructors on the path
    test6 : (x y : ℕ) → lambdaIntoHole (ℕ.suc (x + ⌞ y ⌟ + y)) ≡ λ hole → suc (x + hole + y)
    test6 x y = refl
