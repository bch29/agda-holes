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
  lit : (l : Literal) → HoleyTerm
  var : (x : ℕ) (args : List (Arg HoleyTerm)) → HoleyTerm
  con : (c : Name) (args : List (Arg HoleyTerm)) → HoleyTerm
  def : (f : Name) (args : List (Arg HoleyTerm)) → HoleyTerm
  lam : (v : Visibility) (holeyAbs : Abs HoleyTerm) → HoleyTerm
  pi : (a : Arg HoleyTerm) (b : Abs HoleyTerm) → HoleyTerm
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
  = strErr "Holey-fied version of goal LHS failed to unify with the original."
  ∷ strErr "Check that every hole has an identical term in it."
  ∷ strErr "Offending term:"
  ∷ termErr goalLhs
  ∷ []

-- Converts a HoleyTerm to a regular term by filling in the hole with some other
-- given term which is a function of the number of binders encountered on the
-- way to the hole.
--
-- Free variables inside the holey term are detected and modified using the
-- provided function, because otherwise they might interact wrongly with
-- surrounding terms in the result.

{-# TERMINATING #-}
fillHoley : (ℕ → ℕ) → ℕ → (ℕ → List (Arg Term) → Term) → HoleyTerm → Term
fillHoley freeVarMod binderDepth filler (hole args) = filler binderDepth args
fillHoley _ _ _ (lit l) = lit l
fillHoley freeVarMod binderDepth filler (var x args) with compare x binderDepth
-- If a variable's De Bruijn index is less than the current binder depth then it
-- is bound and should not be modified.
fillHoley freeVarMod _ filler (var x args) | Ordering.less .x k = var x (map (map-arg (fillHoley freeVarMod (suc (x + k)) filler)) args)
-- If a variable's De Bruijn index is >= the current binder depth then it is
-- free and should be modified.
... | _ = var (freeVarMod x) (map (map-arg (fillHoley freeVarMod binderDepth filler)) args)
fillHoley freeVarMod binderDepth filler (con c args) = con c (map (map-arg (fillHoley freeVarMod binderDepth filler)) args)
fillHoley freeVarMod binderDepth filler (def f args) = def f (map (map-arg (fillHoley freeVarMod binderDepth filler)) args)
fillHoley freeVarMod binderDepth filler (meta x args) = meta x (map (map-arg (fillHoley freeVarMod binderDepth filler)) args)
fillHoley freeVarMod binderDepth filler (lam v (abs s holey)) = lam v (abs s (fillHoley freeVarMod (suc binderDepth) filler holey))
fillHoley freeVarMod binderDepth filler (pi (arg v a) (abs s b)) =
  pi (arg v (fillHoley freeVarMod binderDepth filler a))
     (abs s (fillHoley freeVarMod (suc binderDepth) filler b))
fillHoley _ _ _ unknown = unknown

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
  unlist : ∀ {a b}{A : Set a}{B : Set b} → List (Maybe A × B) → Maybe A × List B
  unlist [] = nothing , []
  unlist (x ∷ xs) with x | unlist xs
  ... | head-term , h | tail-term , hs = tail-term <|> head-term , h ∷ hs

  mapSecond : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c} → (B → C) → A × B → A × C
  mapSecond f (x , y) = x , f y

  pushArg : ∀ {A B : Set} → Arg (A × B) → A × Arg B
  pushArg (arg i (x , y)) = x , arg i y

  mutual
    argHelper : (List (Arg HoleyTerm) → HoleyTerm) → List (Arg Term) → Result HoleyErr (Maybe Term × HoleyTerm)
    argHelper build-holey args =
      traverse ((pushArg <$>_) ∘ traverse termToHoleyHelper) args >>=
      return ∘ mapSecond build-holey ∘ unlist

    {-# TERMINATING #-}
    termToHoleyHelper : Term → Result HoleyErr (Maybe Term × HoleyTerm)
    termToHoleyHelper term with toHole term
    termToHoleyHelper term | just args = ok (just term , hole args)
    termToHoleyHelper (lit l) | nothing = ok (nothing , lit l)
    termToHoleyHelper (var x args) | nothing = argHelper (var x) args
    termToHoleyHelper (con c args) | nothing = argHelper (con c) args
    termToHoleyHelper (def f args) | nothing = argHelper (def f) args
    termToHoleyHelper (meta x args) | nothing = argHelper (meta x) args
    termToHoleyHelper (lam v (abs s t)) | nothing =
      termToHoleyHelper t >>= return ∘ mapSecond (λ h → lam v (abs s h))
    termToHoleyHelper (pi (arg v a) (abs s b)) | nothing =
      termToHoleyHelper a >>=² λ t₁ a′ →
      termToHoleyHelper b >>=² λ t₂ b′ →
      return (t₁ <|> t₂ , pi (arg v a′) (abs s b′))
    termToHoleyHelper unknown | nothing = ok (nothing , unknown)
    ... | _ = err (unsupportedTerm term)

-- If a term has a hole in it, specified by ⌞_⌟ around a subterm, returns a
-- HoleyTerm with the hole removed.

termToHoley : Term → Result HoleyErr HoleyTerm
termToHoley term = proj₂ <$> termToHoleyHelper term

-- A variant of `termToHoley` that also returns the term in the hole. If there
-- are multiple holes, returns only the term in one of them (which is considered
-- to be chosen arbitrarily).

termToHoley′ : Term → Result HoleyErr (Term × HoleyTerm)
termToHoley′ term with termToHoleyHelper term
... | ok (just t , h) = ok (t , h)
-- If there is no hole, the whole thing is the hole
... | ok (nothing , h) = ok (term , hole [])
... | err e = err e

checkedTermToHoley : Term → RTC HoleyErr (Term × HoleyTerm)
checkedTermToHoley term =
  liftResult (termToHoley′ term) >>=² λ hole-term holey →
  liftTC (unify term (fillHoley′ (λ _ → hole-term) holey))
    ⟨ catchRTC ⟩
  throw mismatchedHoleTerms >>= λ _ →
  return (hole-term , holey)

-- A variant of `termToHoley` that also returns the term in the hole, and
-- checks that the holey term is valid by unifying it with the original term.
-- The list of error parts given is thrown as a type error if the term could not
-- be converted to a holey term.

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
