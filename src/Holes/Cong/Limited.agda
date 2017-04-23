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
    termsDontMatch : ℕ → Term → HoleyTerm → CongErr
    typeNotEquivalence noHole : CongErr
    appliedVar : (varIdx : ℕ) (goalLhs : Term) → CongErr
    metaOnPath piOnPath lamOnPath : CongErr
    noCongAvailable : Name → ArgPlace → CongErr
    holeyErr : (goalLhs : Term) (holeyErr : HoleyErr) → CongErr

  fillErrLhs : Term → CongErr → CongErr
  fillErrLhs lhs (appliedVar v _) = appliedVar v lhs
  fillErrLhs lhs e = e

  natToTerm : ℕ → Term
  natToTerm zero = con (quote zero) []
  natToTerm (suc n) = con (quote suc) (basicArg (natToTerm n) ∷ [])

  fillHoleyHole : HoleyTerm → Term
  fillHoleyHole = fillHoley′ (λ _ → quote-term ⌞_⌟)

  printCongErr : CongErr → List ErrorPart
  printCongErr (termsDontMatch depth original holey)
    = strErr "There was an attempt to create a path based on non-matching terms"
    ∷ termErr original
    ∷ strErr "and"
    ∷ termErr (fillHoleyHole holey)
    ∷ strErr "at depth"
    ∷ termErr (natToTerm depth)
    ∷ strErr "This is a bug in the holes library!"
    ∷ []
  printCongErr typeNotEquivalence = strErr "The goal type does not appear to be a binary relation." ∷ []
  printCongErr noHole = strErr "There is no hole the goal LHS." ∷ []
  printCongErr (appliedVar v goalLhs)
    = strErr "Variable applications on the path to the hole are not supported. The applied variable was"
    ∷ termErr (var v [])
    ∷ strErr "and the goal LHS was:"
    ∷ termErr goalLhs
    ∷ []
  printCongErr metaOnPath = strErr "Metavariables in the goal LHS are not supported." ∷ []
  printCongErr piOnPath = strErr "Pi types in the goal LHS are not supported." ∷ []
  printCongErr lamOnPath = strErr "Lambdas in the goal LHS are not supported." ∷ []
  printCongErr (noCongAvailable nm argPlace)
    = strErr "No congruence available for function"
    ∷ nameErr nm
    ∷ strErr "at required argument place, index"
    ∷ termErr (natToTerm argPlace)
    ∷ []
  printCongErr (holeyErr goalLhs h) = printHoleyErr goalLhs h

  printCongErrs : List CongErr → List ErrorPart
  printCongErrs (e ∷ []) = printCongErr e
  printCongErrs es = strErr "One of these errors happened:\n" ∷ (intercalate (strErr ";\n" ∷ []) ∘ map printCongErr) es

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

    findOk : ∀ {a e r} {A : Set a} {E : Set e} {{errMonoid : RawMonoid E}} {R : Set r} → (A → Result E R) → List A → Result E (ℕ × R)
    findOk f [] = err mempty
    findOk f (x ∷ xs) with f x
    findOk f (x ∷ xs) | ok r = ok (0 , r)
    findOk f (x ∷ xs) | err e with findOk f xs
    findOk f (x ∷ xs) | err e | ok (n , r) = ok (1 + n , r)
    findOk f (x ∷ xs) | err e₁ | err e₂ = err (e₁ <> e₂)

    _=Visibility?_ : Visibility → Visibility → Bool
    visible =Visibility? visible = true
    hidden =Visibility? hidden = true
    instance′ =Visibility? instance′ = true
    x =Visibility? y = false

    _=Relevance?_ : Relevance → Relevance → Bool
    relevant =Relevance? relevant = true
    irrelevant =Relevance? irrelevant = true
    x =Relevance? y = false

    _=ArgInfo?_ : ArgInfo → ArgInfo → Bool
    arg-info x u =ArgInfo? arg-info y v = (x =Visibility? y) ∧ (u =Relevance? v)

    zipArglists : ∀ {A B : Set} → List (Arg A) → List (Arg B) → List (Arg (A × B))
    zipArglists xs ys = map (λ { (arg i x , arg _ y) → arg i (x , y)}) (zip xs ys)

    mutual
      findHole : ℕ → List (Arg (Term × HoleyTerm)) → Result (List CongErr) (ℕ × HolePath)
      findHole depth = findOk (λ { (arg i (t , h)) → buildPath depth t h })

      -- original:
      -- PathAlgebra._+_ dijkstra c (PathAlgebra._+_ dijkstra ⌞ PathAlgebra._+_ dijkstra b d ⌟ e)
      -- holey:
      -- PathAlgebra._+_ dijkstra c (PathAlgebra._+_ dijkstra ⌞_⌟ e)

      {-# TERMINATING #-}
      buildPath : ℕ → Term → HoleyTerm → Result (List CongErr) HolePath
      buildPath depth original (hole _) = return hole
      buildPath depth (lit _) (lit l) = err (noHole ∷ [])
      buildPath depth (var _ _) (var x _) = err (appliedVar x unknown ∷ [])
      buildPath depth (con _ originalArgs) (con nm args) =
        findHole (suc depth) (zipArglists originalArgs args) >>=² λ argPlace nextPath →
        return (app nm argPlace originalArgs nextPath)
      buildPath depth (def _ originalArgs) (def nm args) =
        findHole (suc depth) (zipArglists originalArgs args) >>=² λ argPlace nextPath →
        return (app nm argPlace originalArgs nextPath)
      buildPath depth (lam _ _) (lam _ _) = err (lamOnPath ∷ [])
      buildPath depth (lam _ _) (pi _ _) = err (piOnPath ∷ [])
      buildPath depth (lam _ _) (meta _ _) = err (metaOnPath ∷ [])
      buildPath depth original holey = err (termsDontMatch depth original holey ∷ [])

    pathToCong : HolePath → Term → Result (List CongErr) Term
    pathToCong hole eq = return eq
    pathToCong (app nm argPlace allArgs hp) eq =
      liftMaybe (noCongAvailable nm argPlace ∷ []) (findCong nm argPlace) >>= λ cong →
      pathToCong hp eq >>= λ rec →
      return (def cong (allArgs ++ (basicArg rec ∷ [])))

    fillErrHoley : HoleyTerm → CongErr → CongErr
    fillErrHoley = fillErrLhs ∘ fillHoleyHole

    autoCong : Term → Term → RTC (List CongErr) ⊤
    autoCong equiv goal =
      liftTC (inferType goal) >>= λ goalType →
      liftMaybe (typeNotEquivalence ∷ []) (decomposeEquiv goalType) >>=² λ goalLhs goalRhs →
      liftResult (mapErr ((_∷ []) ∘ holeyErr goalLhs) (termToHoley goalLhs)) >>= λ holeyLhs →
      liftResult (mapErr (map (fillErrHoley holeyLhs)) (buildPath 0 goalLhs holeyLhs)) >>= λ lhsPath →
      liftResult (pathToCong lhsPath equiv) >>= λ congTerm →
      liftTC (unify congTerm goal)

    -- debug version

    getArglist : Term → List (Arg Term)
    getArglist (def _ args) = args
    getArglist (con _ args) = args
    getArglist (var _ args) = args
    getArglist _ = []

    autoCong′ : Term → Term → RTC (List CongErr) ⊤
    autoCong′ equiv goal =
      liftTC (inferType goal) >>= λ goalType →
      liftMaybe (typeNotEquivalence ∷ []) (decomposeEquiv goalType) >>=² λ goalLhs goalRhs →
      liftResult (mapErr ((_∷ []) ∘ holeyErr goalLhs) (termToHoley goalLhs)) >>= λ holeyLhs →

      liftTC (typeError (map (termErr ∘ getArg) (getArglist goalLhs) ++
                         (strErr "and" ∷ []) ++
                         map (termErr ∘ getArg) (getArglist (fillHoleyHole holeyLhs)))) >>= λ (_ : ⊤) →
      -- liftTC (typeError (termErr goalLhs ∷ termErr (fillHoleyHole holeyLhs) ∷ [])) >>= λ (_ : ⊤) →

      liftResult (mapErr (map (fillErrHoley holeyLhs)) (buildPath 0 goalLhs holeyLhs)) >>= λ lhsPath →
      liftResult (pathToCong lhsPath equiv) >>= λ congTerm →
      liftTC (unify congTerm goal)

  macro
    cong! : Term → Term → TC ⊤
    cong! equiv = runRtcOrTypeError printCongErrs ∘ autoCong equiv

    -- debug version

    cong!′ : Term → Term → TC ⊤
    cong!′ equiv = runRtcOrTypeError printCongErrs ∘ autoCong′ equiv
