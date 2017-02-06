{-

Holey congruence where congruence is limited to specific functions.

To use, open the module `AutoCong` with a database that maps function names to
congruences for those functions.

-}

module Holes.Cong.Limited where

open import Holes.Prelude
open import Holes.Term

open Holes.Prelude public using (quote-term)

private
  find : ∀ {a} {A : Set a} → (A → Bool) → List A → Maybe A
  find p [] = nothing
  find p (x ∷ xs) = if p x then just x else find p xs

  last2 : ∀ {ℓ} {A : Set ℓ} → List A → Maybe (A × A)
  last2 (x ∷ y ∷ []) = just (x , y)
  last2 (x ∷ xs) = last2 xs
  last2 _ = nothing

  withArgs : ∀ {ℓ} {A : Set ℓ} → (List (Arg Term) → A) → Term → Maybe A
  withArgs f (con _ args) = just (f args)
  withArgs f (def _ args) = just (f args)
  withArgs f (var _ args) = just (f args)
  withArgs f _ = nothing

  decomposeEquiv : Term → Maybe (Term × Term)
  decomposeEquiv = join ∘ withArgs (fmap (λ {(arg _ x , arg _ y) → x , y}) ∘ last2)

Congruence = Name
ArgPlace = ℕ

private
  data CongErr : Set where
    termsDontMatch : CongErr
    typeNotEquivalence noHole appliedVar : CongErr
    metaOnPath piOnPath lamOnPath : CongErr
    noCongAvailable : Name → ArgPlace → CongErr
    holeyErr : (goalLhs : Term) (holeyErr : HoleyErr) → CongErr

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

  printCongErr : CongErr → List ErrorPart
  printCongErr termsDontMatch = strErr "This is a bug. There was an attempt to create a path based on non-matching terms." ∷ []
  printCongErr typeNotEquivalence = strErr "The goal type does not appear to be a binary relation." ∷ []
  printCongErr noHole = strErr "There is no hole the goal LHS." ∷ []
  printCongErr appliedVar = strErr "Variable applications in the goal LHS are not supported." ∷ []
  printCongErr metaOnPath = strErr "Metavariables in the goal LHS are not supported." ∷ []
  printCongErr piOnPath = strErr "Pi types in the goal LHS are not supported." ∷ []
  printCongErr lamOnPath = strErr "Lambdas in the goal LHS are not supported." ∷ []
  printCongErr (noCongAvailable nm argPlace)
    = strErr "No congruence available for function"
    ∷ nameErr nm
    ∷ strErr "at necessary argument place."
    ∷ []
  printCongErr (holeyErr goalLhs h) = printHoleyErr goalLhs h

  data HolePath : Set where
    hole : HolePath
    app : (nm : Name) (index : ℕ) (allArgs : List (Arg Term)) → HolePath → HolePath

module AutoCong (database : List (Name × ArgPlace × Congruence)) where

  private
    findCong : Name → ArgPlace → Maybe Congruence
    findCong nm argPlace =
      proj₂ ∘ proj₂ <$>
      find ((λ { (nm′ , argPlace′ , _) →
                      (nm =Name? nm′) ∧
                      (argPlace =ℕ? argPlace′) }))
        database

    findOk : ∀ {a e r} {A : Set a} {E : Set e} {R : Set r} → E → (A → Result E R) → List A → Result E (ℕ × R)
    findOk fail f [] = err fail
    findOk fail f (x ∷ xs) with f x
    findOk fail f (x ∷ xs) | ok r = ok (0 , r)
    findOk fail f (x ∷ xs) | err e with findOk fail f xs
    findOk fail f (x ∷ xs) | err e | ok (n , r) = ok (1 + n , r)
    findOk fail f (x ∷ xs) | err e | err _ = err e

    zipArglists : ∀ {A B : Set} → List (Arg A) → List (Arg B) → List (Arg (A × B))
    zipArglists xs ys = map (λ { (arg i x , arg _ y) → arg i (x , y)}) (zip xs ys)

    mutual
      findHole : List (Arg (Term × HoleyTerm)) → Result CongErr (ℕ × HolePath)
      findHole = findOk noHole (λ { (arg i (t , h)) → buildPath t h })

      {-# TERMINATING #-}
      buildPath : Term → HoleyTerm → Result CongErr HolePath
      buildPath original (hole args) = return hole
      buildPath original (lit l) = err noHole
      buildPath original (var _ _) = err appliedVar
      buildPath (con _ originalArgs) (con nm args) =
        findHole (zipArglists originalArgs args) >>=² λ argPlace nextPath →
        return (app nm argPlace originalArgs nextPath)
      buildPath (def _ originalArgs) (def nm args) =
        findHole (zipArglists originalArgs args) >>=² λ argPlace nextPath →
        return (app nm argPlace originalArgs nextPath)
      buildPath original (lam _ _) = err lamOnPath
      buildPath original (pi _ _) = err piOnPath
      buildPath original (meta _ _) = err metaOnPath
      buildPath _ _ = err termsDontMatch

    pathToCong : HolePath → Term → Result CongErr Term
    pathToCong hole eq = return eq
    pathToCong (app nm argPlace allArgs hp) eq =
      liftMaybe (noCongAvailable nm argPlace) (findCong nm argPlace) >>= λ cong →
      pathToCong hp eq >>= λ rec →
      return (def cong (allArgs ++ (basicArg rec ∷ [])))

    autoCong : Term → Term → RTC CongErr ⊤
    autoCong equiv goal =
      liftTC (inferType goal) >>= λ goalType →
      liftMaybe typeNotEquivalence (decomposeEquiv goalType) >>=² λ goalLhs goalRhs →
      liftResult (mapErr (holeyErr goalLhs) (termToHoley goalLhs)) >>= λ holeyLhs →
      liftResult (buildPath goalLhs holeyLhs) >>= λ lhsPath →
      liftResult (pathToCong lhsPath equiv) >>= λ congTerm →
      liftTC (unify congTerm goal)
      -- liftTC (typeError (termErr congTerm ∷ []))

  macro
    cong! : Term → Term → TC ⊤
    cong! equiv = runRtcOrTypeError printCongErr ∘ autoCong equiv
