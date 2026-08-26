/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic

set_option autoImplicit false
set_option tactic.hygienic false


-- # Challenges in applying functional induction to divide-and-conquer algorithms
-- Sometimes, we cannot immediately call funtional induction even though the algoithm is recusive.
-- This is usually because the hypothesis is too specialized.
-- The key idea is to formulate a more general inductive hypothesis

-- In this sheet, we walk through binary search on a sorted array as an example

-- Consider the following formulation of the sorted array
-- This version has fewer proof obligations because we don't have to worry about the indices (out-of-bounds)

structure SortedArrayFun (n :ℕ) where
  get : ℕ → ℕ
  size : ℕ := n
  sorted: Monotone get

#check SortedArrayFun
#check SortedArrayFun.get
#check SortedArrayFun.sorted
-- A function f is monotone if a ≤ b implies f a ≤ f b.
#check Monotone

def contains_bs {n :ℕ }(arr : SortedArrayFun n) (q : ℕ) : Option ℕ :=
  bs_aux 0 (n-1) (by omega)
  where bs_aux (a b :ℕ) (h: a ≤ b): Option ℕ  :=
  if h: a = b then
    if q = arr.get a then some a
    else none
  else
    let mid := (a+b)/(2 :ℕ )
    if      q < arr.get mid then bs_aux a mid  (by omega)
    else if  arr.get mid < q then bs_aux (mid+1) b (by omega)
    else some mid

-- The property we need is: "Searching in the interval [a, b] finds q if and only if q is present in that interval."
#check contains_bs.bs_aux
lemma bs_aux_correctness (n q :ℕ)(arr : SortedArrayFun n) (a b :ℕ)(h_le : a ≤ b) :
  (∃ i, a ≤ i ∧ i ≤ b ∧ arr.get i = q) ↔ (contains_bs.bs_aux arr q a b h_le ≠ none) := by
    fun_induction contains_bs.bs_aux
    · simp_all
      use b_1
    · simp_all
      intro x hx hy
      have: x = b_1 := by omega
      subst this
      aesop
    · rw [← ih1]
      sorry
    · rw [← ih1]
      sorry
    · simp_all
      use mid
      grind

theorem contains_bs_correctness (n q :ℕ)(h: 0 < n)(arr : SortedArrayFun n):
  (∃ i, i < n ∧ arr.get i = q) ↔ (contains_bs arr q ≠ none) := by
  unfold contains_bs
  have: 0 ≤ n-1 := by omega
  have := bs_aux_correctness n q arr 0 (n-1) (by omega)
  grind

/-
-- Hints below
theorem subinterval_to_interval_qlt {n : ℕ} (arr : SortedArrayFun n) (q a mid b: ℕ)
  (h_bounds : a ≤ mid ∧ mid ≤ b)  -- [[a q⁻¹ mid] b]:
  (h_q: q < arr.get mid):
  (∃ i, a ≤ i ∧ i ≤ b ∧ arr.get i = q) ↔ (∃ i, a ≤ i ∧ i ≤ mid ∧ arr.get i = q)  := by sorry

-- Exercise
theorem subinterval_to_interval_qgt {n : ℕ} (arr : SortedArrayFun n) (q a mid b: ℕ)
  (h_bounds : a ≤ mid ∧ mid ≤ b)  -- [a [mid q⁻¹ b]]:
  (h_q: arr.get mid < q ):
  (∃ i, a ≤ i ∧ i ≤ b ∧ arr.get i = q) ↔ (∃ i, (mid+1) ≤ i ∧ i ≤ b ∧ arr.get i = q)  := by sorry
-/
