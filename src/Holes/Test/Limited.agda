module Holes.Test.Limited where

open import Holes.Prelude hiding (_⊛_)
open import Holes.Util
open import Holes.Term
open import Holes.Cong.Limited

open import Agda.Builtin.Equality using (_≡_; refl)

module Contrived where
  infixl 5 _⊕_
  infixl 6 _⊛_
  infix 4 _≈_

  -- A type of expression trees for natural number calculations

  data Expr : Set where
    zero : Expr
    succ : Expr → Expr
    _⊕_ _⊛_ : Expr → Expr → Expr

  -- An unsophisticated 'equality' relation on the expression trees

  data _≈_ : Expr → Expr → Set where
    zero-cong : zero ≈ zero
    succ-cong : ∀ {m n} → m ≈ n → succ m ≈ succ n
    ⊕-cong : ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → a ⊕ b ≈ a′ ⊕ b′
    ⊛-cong : ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → a ⊛ b ≈ a′ ⊛ b′

    ⊕-comm : ∀ a b → a ⊕ b ≈ b ⊕ a

  -- Some lemmas that are necessary to proceed

  ≈-refl : ∀ {n} → n ≈ n
  ≈-refl {zero} = zero-cong
  ≈-refl {succ n} = succ-cong ≈-refl
  ≈-refl {m ⊕ n} = ⊕-cong ≈-refl ≈-refl
  ≈-refl {m ⊛ n} = ⊛-cong ≈-refl ≈-refl

  {-
  Each congruence in the database must have a type with the same shape as the
  below, following these rules:

  - A congruence `c` is for a single _top-level_ function `f`
  - `c` may only be a congruence for _one_ of `f`'s arguments
  - Each explicit argument to `f` must be an explicit argument to `c`
  - The 'rewritten' version of the changing argument must follow as an implicit
    argument to `c`
  - The equation to do the local rewriting must be the next explicit argument
  -}

  open CongSplit _≈_ ≈-refl

  ⊕-cong₁ = two→one₁ ⊕-cong
  ⊕-cong₂ = two→one₂ ⊕-cong
  ⊛-cong₁ = two→one₁ ⊛-cong
  ⊛-cong₂ = two→one₂ ⊛-cong

  succ-cong′ : ∀ n {n′} → n ≈ n′ → succ n ≈ succ n′
  succ-cong′ _ = succ-cong

  {-
  Create the database of congruences.
  - This is a list of (Name × ArgPlace × Congruence) triples.
  - The `Name` is the (reflected) name of the function to which the congruence
    applies.
  - The `ArgPlace` is the index of the argument place that the congruence can
    rewrite at.
  - The `Congruence` is a reflected copy of the congruence function, of type `Term`
  -}

  database
    = (quote _⊕_ , 0 , quote-term ⊕-cong₁)
    ∷ (quote _⊕_ , 1 , quote-term ⊕-cong₂)
    ∷ (quote _⊛_ , 0 , quote-term ⊛-cong₁)
    ∷ (quote _⊛_ , 1 , quote-term ⊛-cong₂)
    ∷ (quote succ , 0 , quote-term succ-cong′)
    ∷ []

  open AutoCong database

  test1 : ∀ a b → succ ⌞ a ⊕ b ⌟ ≈ succ (b ⊕ a)
  test1 a b = cong! (⊕-comm a b)

  test2 : ∀ a b c → succ (⌞ a ⊕ b ⌟ ⊕ c) ≈ succ (b ⊕ a ⊕ c)
  test2 a b c = cong! (⊕-comm a b)

  test3 : ∀ a b c → succ (a ⊕ ⌞ b ⊕ c ⌟) ≈ succ (a ⊕ (c ⊕ b))
  test3 a b c = cong! (⊕-comm b c)

module Propositional (+-comm : ∀ a b → a + b ≡ b + a) where
  +-cong₁ : ∀ a b {a′} → a ≡ a′ → a + b ≡ a′ + b
  +-cong₁ _ _ refl = refl

  +-cong₂ : ∀ a b {b′} → b ≡ b′ → a + b ≡ a + b′
  +-cong₂ _ _ refl = refl

  suc-cong : ∀ n {n′} → n ≡ n′ → suc n ≡ suc n′
  suc-cong _ refl = refl

  database
    = (quote _+_ , 0 , quote-term +-cong₁)
    ∷ (quote _+_ , 1 , quote-term +-cong₂)
    ∷ (quote suc , 0 , quote-term suc-cong)
    ∷ []

  open AutoCong database

  test1 : ∀ a b → suc ⌞ a + b ⌟ ≡ suc (b + a)
  test1 a b = cong! (+-comm a b)

  test2 : ∀ a b c → suc (⌞ a + b ⌟ + c) ≡ suc (b + a + c)
  test2 a b c = cong! (+-comm a b)

  test3 : ∀ a b c → suc (a + ⌞ b + c ⌟) ≡ suc (a + (c + b))
  test3 a b c = cong! (+-comm b c)

  test4 : ∀ a b c a′ → a ≡ a′ → suc (⌞ a ⌟ + b + c) ≡ suc (a′ + b + c)
  test4 _ _ _ _ eq = cong! eq
