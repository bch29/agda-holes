module Propositional where

open import Data.Nat
open import Relation.Binary.PropositionalEquality

open import Holes.Term using (⌞_⌟)
open import Holes.Cong.Propositional

open ≡-Reasoning

--------------------------------------------------------------------------------
--  Some easy lemmas
--------------------------------------------------------------------------------

+-zero : ∀ a → a + zero ≡ a
+-zero zero = refl
+-zero (suc a) rewrite +-zero a = refl

+-suc : ∀ a b → a + suc b ≡ suc (a + b)
+-suc zero b = refl
+-suc (suc a) b rewrite +-suc a b = refl

+-assoc : ∀ a b c → a + b + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c rewrite +-assoc a b c = refl

--------------------------------------------------------------------------------
--  Proofs by equational reasoning
--------------------------------------------------------------------------------

-- commutativity of addition proved traditionally

+-comm₁ : ∀ a b → a + b ≡ b + a
+-comm₁ zero b = sym (+-zero b)
+-comm₁ (suc a) b =
  suc ⌞ a + b ⌟   ≡⟨ cong suc (+-comm₁ a b) ⟩
  suc (b + a)     ≡⟨ sym (+-suc b a) ⟩
  b + suc a       ∎

-- commutativity of addition proved with holes

+-comm : ∀ a b → a + b ≡ b + a
+-comm zero b = sym (+-zero b)
+-comm (suc a) b =
  suc ⌞ a + b ⌟   ≡⟨ cong! (+-comm a b) ⟩
  suc (b + a)     ≡⟨ cong! (+-suc b a) ⟩
  b + suc a       ∎

-- distributivity of multiplication over addition proved traditionally

*-distrib-+₁ : ∀ a b c → a * (b + c) ≡ a * b + a * c
*-distrib-+₁ zero b c = refl
*-distrib-+₁ (suc a) b c =
    b + c + a * (b + c)          ≡⟨ cong (λ h → b + c + h) (*-distrib-+₁ a b c) ⟩
    (b + c) + (a * b + a * c)    ≡⟨ sym (+-assoc (b + c) (a * b) (a * c)) ⟩
    ((b + c) + a * b) + a * c    ≡⟨ cong (λ h → h + a * c) (+-assoc b c (a * b)) ⟩
    (b + (c + a * b)) + a * c    ≡⟨ cong (λ h → (b + h) + a * c) (+-comm c (a * b)) ⟩
    (b + (a * b + c)) + a * c    ≡⟨ cong (λ h → h + a * c) (sym (+-assoc b (a * b) c)) ⟩
    ((b + a * b) + c) + a * c    ≡⟨ +-assoc (b + a * b) c (a * c) ⟩
    (b + a * b) + (c + a * c)
  ∎

-- distributivity of multiplication over addition proved with holes

*-distrib-+ : ∀ a b c → a * (b + c) ≡ a * b + a * c
*-distrib-+ zero b c = refl
*-distrib-+ (suc a) b c =
  b + c + ⌞ a * (b + c) ⌟         ≡⟨ cong! (*-distrib-+ a b c) ⟩
  ⌞ (b + c) + (a * b + a * c) ⌟   ≡⟨ cong! (+-assoc (b + c) (a * b) (a * c)) ⟩
  ⌞ (b + c) + a * b ⌟ + a * c     ≡⟨ cong! (+-assoc b c (a * b)) ⟩
  (b + ⌞ c + a * b ⌟) + a * c     ≡⟨ cong! (+-comm c (a * b)) ⟩
  ⌞ b + (a * b + c) ⌟ + a * c     ≡⟨ cong! (+-assoc b (a * b) c) ⟩
  ⌞ ((b + a * b) + c) + a * c ⌟   ≡⟨ cong! (+-assoc (b + a * b) c (a * c)) ⟩
  (b + a * b) + (c + a * c)
  ∎
