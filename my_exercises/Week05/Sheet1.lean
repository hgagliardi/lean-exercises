/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false

--# Inductive Predicate
-- We have seen inductive types in the previous class. Today, we cover the concept of inductive predicate.
-- Inductive predicate is a proposition that is defined inductively which Lean supports.
-- Let's start with a toy example

/- Even number:
  An even number is defined recursively as follows:
  * 0 is even
  * ∀ n : ℕ, if n is even then n + 2 is even
-/
@[simp] def evenFun (n :ℕ ) : Prop := ∃ k, n = 2*k

inductive IsEven : ℕ → Prop
| zero : IsEven 0
| plus_two (n:ℕ): IsEven n → IsEven (n+2)

-- This gives two (introduction) rules for building a proof that a number is even
#check IsEven.zero
#check IsEven.plus_two

example: IsEven 0 := .zero
example: IsEven 4 := by
  apply IsEven.plus_two
  apply IsEven.plus_two
  exact .zero


/-!  New Tactics for inductive predicate
  `cases h` -- deconstruct the proof `h : IsEven n` into all possible cases `h` can be constructed using introduction rules.
        -- Intuitively, `cases h` where `h : IsEven n` allows us to prove that
        -- for every constructor that an element can be produced, the goal can be proved.
        -- It breaks down into cases based on the constructor and match it to the goal.
-/

example: ¬ (IsEven 3) := by
  by_contra!
  cases this
  rw [show 0 + 1 = 1 from rfl] at a
  cases a

-- let's prove completeness and soundness

-- Case works well when dealing with literals IsEven 0, IsEven 2, IsEven 4
-- If we want to prove IsEven n for all n, we use (rule) induction.
-- Given an hypotehsis `h : IsEven n`, and the goal is `⊢ P n`.
-- We invoke `induction' h` and obtain two subgoals: `IsEven.zero` and `IsEven.plus_two`
-- This is called Rule Induction.

theorem soundness_isEven (n:ℕ ):  IsEven n → evenFun n := by
  intro h
  induction' h
  · simp [evenFun]
  · simp_all only [evenFun]
    obtain ⟨k,hk⟩ := a_ih
    use k+1
    rw [hk]
    omega

/- # Explanation -/
-- We can think of `h: IsEven n ⊢ P n` as case analysis.
-- Let's consider all rules from inductive predicate `IsEven` that can generate this proof `h: IsEven n`
-- case `IsEven.zero`.     In this case, `h: IsEven n`     is generated from `IsEven 0`, so prove `P 0`
-- case `IsEven.plus_two`. In this case, `h: IsEven (n+2)` is generated from `IsEven n`,
--                         we have  to `P (n)` and prove `P (n+2)`

inductive IsEven2 : ℕ → Prop
| zero : IsEven2 0
| plus_two (n:ℕ): IsEven2 n → IsEven2 (n+4)

-- Exercise 1.1
theorem soundness_IsEven2 (n:ℕ ):  IsEven2 n → evenFun n := by sorry

-- Do it together
theorem completeness_isEven (n : ℕ): evenFun n → IsEven n := by sorry

-- Exercise 1.2
theorem incompleteness_isEven2 : ∃ n, evenFun n ∧ ¬ IsEven2 n := by sorry

/- Summary
-- By analogy, the proof strategy for inductive predicates is similar to that of the disjunction.
-- h: P ∨ Q    -- `cases h` will deconstruct `h` into  two cases `h: P` and `h: Q` to prove the goal separately
-- h: IsEven n -- `cases h` will deconstruct `h` into cases that `h` can be proved by the constructors.
               -- `induction h` is similar to `cases h`, but we obtain inductive hypothesis to prove the inductive cases.

-- ⊢ P ∨ Q     -- apply `inl: P` or apply `inr: Q` --> this simplifies to proving P or proving Q.
-- ⊢ IsEven n  -- apply `IsEven.zero: IsEven 0` or apply `IsEven.plus_two: IsEven n → IsEven (n+2)`.
-/


-- # Challenges for induction proofs
-- The arguments for inductive predicates evolves throughout the induction.
-- we can apply `induction h` on h: Even n. However, we cannot apply `induction h` on h: Even (n+1) because in Lean (n+1) is not a variable.
-- Example

-- generalize, replace, rwa tactics
example (m: ℕ) (h: IsEven (m+2)) : IsEven m := by sorry
-- Exercise 1.4
example (m n : ℕ) (h: m = 2*n+1) : ¬ IsEven m := by sorry
