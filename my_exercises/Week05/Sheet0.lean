/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false


/-! more useful tactics
  * `suffices P by X` -- To prove the goal, it is enough to prove `P` because of `X`.
  * `observe h: P` -- same as have h: P := by exact? where observe is successful if exact? can find a proof.
  * `plausible` -- Try to find a counter example
  * `cancel_denoms` -- try to cancel denominators of fraction
  * `positivity`-- Tactic solving goals of the form 0 ≤ x, 0 < x and x ≠ 0
  * `zify / qify / rify` -- shift an inequality goal to ℤ / ℚ / ℝ
-/

-- # `suffices P by X`
-- To prove the goal, it is enough to prove `P` because of `X`.
example (A B C : Prop) (hAB : A → B) (hBC : B → C)  (hA : A) :C := by
  suffices A → C by
    apply this
    exact hA
  trans B
  · exact hAB
  · exact hBC

-- c.f. `have` tactics
example (A B C : Prop) (hAB : A → B) (hBC : B → C)  (hA : A) :C := by
  have: A → C := by
    trans B
    · exact hAB
    · exact hBC
  apply this
  exact hA

-- # `observe` tactic
-- if `have` can be proved using exact?, so does `observe`
example (A B C : Prop) (hAB : A → B) (hBC : B → C)  (hA : A) :C := by
  observe: A → C
  apply this
  exact hA

example (a :ℕ) (h: 3 ≤ a) : 0 ≤ a := by
  positivity

-- plasible will try to find a counterexample
--example (a :ℤ) : 0 ≤ a := by
  -- plausible

-- # `cancel_denoms`
-- try to cancel denominators of fraction

example (a b c :ℝ) (h : a / 5 + b / 4 < c) : 4*a + 5*b < 20*c := by
  cancel_denoms at h
  exact h


-- The `zify` tactic is used to shift propositions from ℕ to ℤ.
-- This is often useful since ℤ has well-behaved subtraction.

-- The `qify` tactic is used to shift propositions from ℕ or ℤ to ℚ.
-- This is often useful since ℚ has well-behaved division.

-- The `rify` tactic is used to shift propositions from ℕ or ℤ or ℚ to ℝ.
-- This is often useful when you have ℝ in your goal

-- Example
def f : ℕ → ℤ
  | 0   => 1
  | 1   => 1
  | n+2 => 2*f (n+1) - f n + 2

theorem f_closed_form (n : ℕ) : f n = n^2 - n + 1 := by
  induction n using Nat.twoStepInduction
  · rfl
  · rfl
  · unfold f
    rw [a_1,a]
    zify
    ring
