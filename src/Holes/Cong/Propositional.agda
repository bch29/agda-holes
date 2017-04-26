{-

Holey congruence for propositional equality.

-}

module Holes.Cong.Propositional where

open import Holes.Prelude
open PropEq using (_≡_; refl; cong; sym; trans)

import Holes.Cong.General as Cong

open Cong (quote-term cong) (quote-term sym) public
  using (cong!)
