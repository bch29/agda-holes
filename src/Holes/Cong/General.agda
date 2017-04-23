{-

Holey congruence where there is a 'general' `cong` function available, as in one
that works for any given function.

-}

open import Holes.Prelude

-- NOTE: Why can't we accept the actual functions as arguments instead of quoted
-- versions? Because macros don't play nicely with modules.
module Holes.Cong.General
  (quote-≈ : Term)
  (quote-cong : Term)
  (quote-sym : Term)
  where

open Holes.Prelude public using (quote-term)

import Holes.Term as HTerm

-- NOTE: This doesn't work! The place that uses the macros has to import
-- Holes.Term using (⌞_⌟) manually.
-- open HTerm using (⌞_⌟) public

open HTerm

private
  -- If the given term is one that has arguments, returns them.

  getArgs : Term → Maybe (List (Arg Term))
  getArgs (var x args) = just args
  getArgs (con c args) = just args
  getArgs (def f args) = just args
  getArgs (pat-lam cs args) = just args
  getArgs _ = nothing

  -- In a list of arguments, returns the relevant ones for a binary relation.

  ≈relevantArgs : List (Arg Term) → Maybe (Term × Term)
  ≈relevantArgs (_ ∷ _ ∷ arg _ x ∷ arg _ y ∷ []) = just (x , y)
  ≈relevantArgs _ = nothing

-- Given a type of the form `x ≡ y`, returns the pair `x , y`.

  decompose≈ : Term → Maybe (Term × Term)
  decompose≈ = getArgs >=> ≈relevantArgs

  apply≈ : Term → Term → Term
  apply≈ lhs rhs =
    def (quote id)
        ( basicArg quote-≈
        ∷ basicArg lhs
        ∷ basicArg rhs
        ∷ [])

  applyCong : Term → Term → Term
  applyCong lambda inner-equality =
    def (quote id)
        ( basicArg quote-cong
        ∷ basicArg lambda           -- f : A → B
        ∷ basicArg inner-equality   -- x ≈ y
        ∷ [])

  applySym : Term → Term
  applySym equality =
    def (quote id)
        ( basicArg quote-sym
        ∷ basicArg equality    -- i ≈ j
        ∷ [])

  autoCongWithType : Term → Type → TC Term
  autoCongWithType equality-term target-type =
    -- Try to decompose the goal type, which should be of the form `x ≡ y`, into
    -- `x` and `y`. Throw a type error if this is not possible.
    runRTC (λ _ → typeError $ strErr "Term is not of the form x ≈ y:"
                            ∷ termErr target-type
                            ∷ []) (liftMaybe tt (decompose≈ target-type)) >>=² λ goalLhs _ →
    -- Try to make a lambda into the holes of the LHS. Throw a type error if
    -- this is not possible.
    checkedTermToHoley′ (printHoleyErr goalLhs) goalLhs >>=² λ _ lhs-holey →
    -- Apply the `cong` function with our newly constructed lambda and the
    -- provided equality term. Most implicit arguments are left unknown, and
    -- then inferred by Agda when we call `checkType`.
    return (applyCong (holeyToLam lhs-holey) equality-term) >>= λ cong-term →
    -- Try to check the type of the cong term. If it doesn't work, try it
    -- symmetrically. If that doesn't work, try the first again so that the user
    -- gets a nicer error message.
    checkType cong-term target-type
      ⟨ catchTC ⟩
    checkType (applySym cong-term) target-type
      ⟨ catchTC ⟩
    checkType cong-term target-type
    -- `checkType` hopefully returns to us the `cong` call with filled implicit
    -- arguments. Assuming the user's logic is correct, this is what we need to
    -- prove the goal.

  cong!′ : Term → Term → TC ⊤
  cong!′ equality-term target =
    inferType target >>=
    autoCongWithType equality-term >>=
    unify target

macro
  cong! : Term → Term → TC ⊤
  cong! = cong!′
