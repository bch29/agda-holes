module Holes.Test.General where

open import Holes.Prelude
open PropEq using (_≡_; refl; cong; sym; trans)

open import Holes.Term using (⌞_⌟)
open import Holes.Cong.Propositional

private
  +-zero : ∀ x → x + 0 ≡ x
  +-zero zero = refl
  +-zero (suc x) = cong suc (+-zero x)

  +-suc : ∀ x y → suc (x + y) ≡ x + suc y
  +-suc zero y = refl
  +-suc (suc x) y = cong suc (+-suc x y)

  +-comm : ∀ x y → x + y ≡ y + x
  +-comm zero y = sym (+-zero y)
  +-comm (suc x) y = trans (cong suc (+-comm x y)) (+-suc y x)

  data Fin : ℕ → Set where
    zero : ∀ {n} → Fin (suc n)
    suc : ∀ {n} → Fin n → Fin (suc n)

-- Expressions with free variables
test1 : ∀ x y z → ⌞ x + y ⌟ + z ≡ (y + x) + z
test1 x y z = cong! (+-comm x y)

-- TODO: This works, but if you replace `y` by `_` in the above, there are
-- unsolved metas!
test1′ : ∀ x y z → x + y + z ≡ y + x + z
test1′ x y z = cong (λ h → h + z) (+-comm x _)

-- Multiple holes
test2 : ∀ x y z → x + ⌞ y + z ⌟ * ⌞ y + z ⌟ + y * z ≡ x + (z + y) * (z + y) + y * z
test2 x y z = cong! (+-comm y z)

-- Picking out one instance of a group of identical sub-expressions
test3 : ∀ x y z → x + ⌞ y + z ⌟ * (y + z) + y * z ≡ x + (z + y) * (y + z) + y * z
test3 x y z = cong! (+-comm y z)

-- Automatic symmetry
test4 : ∀ x y z → x + ⌞ y + z ⌟ * (y + z) + y * z ≡ x + (z + y) * (y + z) + y * z
test4 x y z = cong! (+-comm z y)

-- No hole on the LHS ⇒ hole around everything (notice automatic symmetry application)
test5 : ∀ x y → x + y ≡ y + x
test5 x y = cong! (+-comm y x)

-- Works in Π types
test6 : ∀ x y → (Fin ⌞ x + y ⌟ → ℕ) ≡ (Fin ⌞ y + x ⌟ → ℕ)
test6 x y = cong! (+-comm x y)

-- -- Fails with a nice error message when holes contain different terms
-- fail1 : ∀ x y z → y ≡ x → ⌞ x ⌟ + ⌞ y ⌟ + z ≡ x + x + z
-- fail1 x y z eq = cong! eq

-- -- This is only provable in the presence of functional extensionality, so the
-- -- macro should obviously fail here. It would be nice if the error message
-- -- were improved though.
-- fail2 : ∀ (x y : ℕ) → (λ (f : ℕ → ℕ) → ⌞ f x + f y ⌟) ≡ (λ f → f y + f x)
-- fail2 x y = cong! (+-comm _ _)
