/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
--set_option tactic.hygienic false


/-
# Function Induction
So far, we have seen induction over ℕ. This week we will cover functional induction.
The core idea is that if a function is recursively defined, then you can prove it recursively as long as you show termination.
On the other hand, functional induction formalizes recursive proofs and tells you exactly what is needed to complete the proof.
These two proofs are equivalent, but they may give you different perspective to think about a problem.
-/

-- functional induction
-- Pascal sum

def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

-- Recall induction proof
lemma fact (n :ℕ) : 1 ≤ n ! := by
  induction' n with n ih
  · rfl
  · unfold factorial
    grw [← ih]
    exact NeZero.one_le

def P : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 1
  | a + 1, b + 1 => P (a + 1) b + P a (b + 1)


-- In Lean, every recursively defined function is equipped with functional induction
#check P.induct
#check P.induct_unfolding

#eval [P 0 0]
#eval [P 0 1,P 1 0]
#eval [P 2 0,P 1 1, P 2 0]
#eval [P 3 0,P 2 1, P 1 2, P 0 3]
#eval [P 4 0,P 3 1, P 2 2, P 1 3, P 0 4]

-- Example
lemma P_le_fact ( a b : ℕ ): P a b ≤ (a+b)! := by
  fun_induction P
  all_goals (expose_names)
  · simp only [add_zero]
    exact fact x
  · simp only [Nat.succ_eq_add_one, zero_add]
    exact fact (n + 1)
  · grw [ih1,ih2]
    clear * -; grind [fact,factorial] -- grind for algebraic proofs

-- grind is a powerful automation
-- We will not be using grind for the rest of the week.
lemma P_le_fact'' ( a b : ℕ ): P a b ≤ (a+b)! := by
  fun_induction P <;> all_goals grind only [fact, factorial]

-- This proof is more intuitive than the one-line proof
lemma P_le_fact' ( a b : ℕ ): P a b ≤ (a+b)! := by
  fun_induction P <;> all_goals (try simp_all only [add_zero, fact])
  · expose_names
    calc
      P (a + 1) b + P a (b + 1) ≤ (a + 1 + b) ! + (a + (b + 1)) !                            := by rel [ih1, ih2]
                              _ ≤ (a + b) * (a + b + 1) ! + (a + 1 + b) ! + (a + (b + 1)) !  := by omega
                              _ = ((a + b + 1) + 1) * (a + b + 1)!                           := by ring_nf
                              _ = ((a + b + 1) + 1)!                                         := by bound
                              _ = (a + 1 + (b + 1))!                                         := by ring_nf

--#print P_le_fact'
--#print P_le_fact'._proof_1_5

-- # Exercise 1.1
/-
Define T(m,n):
  T(m,0) = T(0,n) = 1,
  T(m,n) = T(m-1,n) + T(m,n-1)
  Prove that T(m,n) ≤ 2^{m+n}
-/

def T : ℕ → ℕ  → ℕ := sorry
theorem solve_T (m n: ℕ):  T m n ≤ 2^(m+n)  := by sorry
