module Holes.Util where

open import Holes.Prelude

private
  Rel : ∀ {a} → Set a → ∀ ℓ → Set (a ⊔ lsuc ℓ)
  Rel A ℓ = A → A → Set ℓ

module CongSplit {ℓ x} {X : Set x} (_≈_ : Rel X ℓ) (reflexive : ∀ {x} → x ≈ x) where

  two→one₁ : {_+_ : X → X → X}
            → (∀ {x x′ y y′} → x ≈ x′ → y ≈ y′ → (x + y) ≈ (x′ + y′))
            → (∀ x y {x′} → x ≈ x′ → (x + y) ≈ (x′ + y))
  two→one₁ cong² _ _ eq = cong² eq reflexive

  two→one₂ : {_+_ : X → X → X}
           → (∀ {x x′ y y′} → x ≈ x′ → y ≈ y′ → (x + y) ≈ (x′ + y′))
           → (∀ x y {y′} → y ≈ y′ → (x + y) ≈ (x + y′))
  two→one₂ cong² _ _ eq = cong² reflexive eq
