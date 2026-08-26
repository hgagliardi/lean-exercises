/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic

/-! New tactics
  * `apply` -- Suppose we have `h: P → Q`, which can be from the current assumptions or from the library.
            -- we apply `h` on hypothesis to move assumptions forward and apply on goal to push the goal backward.
  * If we have `hp: P`, then `apply h at hp` yields a new assumption `Q`
  * If the goal is in the form `Q`, then `apply h` changes the goal to `P`
-/

variable (P Q R: Prop)

-- Example 1: Using apply to Transform a Goal
lemma piq (h: P → Q)(h2: P): Q := by
  apply h
  exact h2

-- Example 2: Using apply with Existing Assumptions
example (h: P → Q)(h2: P): Q := by
  apply h at h2
  exact h2

example (h: P → Q)(h2: Q → R): P → R := by
  intro hP
  apply h2
  apply h
  exact hP

/-!
## `apply` is flexible
The apply tactic in Lean can be used not only to transform goals but also to produce subgoals when the hypothesis you are applying has multiple premises.
This is often the case when you have implications or functions that require more than one argument.
-/
example {S: Prop} (h0: P ∧ Q ∧ R)(h: P → Q → R → S): S := by
  obtain ⟨hp,hq,hr⟩ := h0
  apply h
  exact hp
  exact hq
  exact hr






example {S}: P → Q → R → S ↔ ((P ∧ Q ∧ R) → S) := by tauto

/-!
## More examples
-/
#check lt_trans
example (x y z : ℝ) (hab : x < y) (hbc: y < z) : x < z := by
  apply lt_trans
  -- from Infoview: ?b is a meta variable
  -- first supply this meta variable as 'y'
  -- do this by 'case' tactic that selects case b followed by exact y
  case b => exact y
  -- we can solve the goals now
  exact hab
  exact hbc

example (a b c : ℝ) (hab : a < b) (hbc: b < c) : a < c := by
  -- alternatively, one could use 'trans' tactics to do the same thing
  trans b
  exact hab
  exact hbc
