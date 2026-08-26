/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Lectures.Week06.API

set_option autoImplicit false
set_option tactic.hygienic false


-- In this sheet, we are going to prove the merge lemma

def Merge: List ℕ → List ℕ → List ℕ
  | x, [] => x
  | [], x => x
  | x::xs, y::ys =>
    if x ≤ y then x :: Merge xs (y::ys)
    else y :: Merge (x :: xs) ys

-- Example: Let's prove this by recursion
lemma merge_size_sum (l1 l2 : List ℕ) : (Merge l1 l2).length = l1.length + l2.length  := by
match  l1, l2 with
| x, [] => simp [Merge]
| [], x => unfold Merge; aesop
| x::xs, y::ys =>
  simp +arith +decide only [List.length_cons,Merge]
  split_ifs
  · simp
    apply merge_size_sum
  · simp
    have: xs.length + ys.length + 1 = (xs.length +1 ) + ys.length := by omega
    rw [this]
    apply merge_size_sum

-- Example: Let's prove this by induction
example (l1 l2 : List ℕ) : (Merge l1 l2).length = l1.length + l2.length  := by
fun_induction Merge l1 l2
· simp
· simp
· simp
  rw [ih1]
  simp +arith
· simp
  rw [ih1]
  simp +arith

-- Example: Let's us leverage automation + functional induction
example (l1 l2 : List ℕ) : (Merge l1 l2).length = l1.length + l2.length  := by
fun_induction Merge l1 l2 <;> all_goals grind

-- Example: another theorem with this hammer
theorem mem_either_merge_auto (xs ys : List ℕ) (z : ℕ)
  (hz : z ∈ Merge xs ys) : z ∈ xs ∨ z ∈ ys := by
  fun_induction Merge <;> all_goals grind

-- Let's break down the proof and see how to prove this by ``hand``.
-- Exercise 2.1: try to prove this using either recursion or functional induction (don't use grind on the inductive step)
theorem mem_either_merge (xs ys : List ℕ) (z : ℕ)
  (hz : z ∈ Merge xs ys) : z ∈ xs ∨ z ∈ ys := by sorry

-- Exercise 2.2: use mem_either_merge to prove the following.
#check mem_either_merge
theorem min_all_merge (x : ℕ) (xs ys: List ℕ)
 (hxs : x.MinOfList xs) (hys : x.MinOfList ys) : x.MinOfList (Merge xs ys):= by sorry

-- We are ready to prove the main sorted merge.
-- discuss a proof

theorem sorted_merge(l1 l2 : List ℕ)(hxs: Sorted l1) (hys: Sorted l2): Sorted (Merge l1 l2) := by sorry

-- c.f. with recursive proofs.
theorem sorted_merge_rec(l1 l2 : List ℕ)(hxs: Sorted l1) (hys: Sorted l2): Sorted (Merge l1 l2) := by
  match l1,l2 with
  | x, [] => simpa [Merge]
  | [],x => unfold Merge; aesop
  | x::xs, y::ys =>
    simp [Merge]
    split_ifs with h
    · apply Sorted.cons_min
      apply sorted_min at hxs
      apply sorted_min at hys
      · apply min_all_merge
        · grind
        · grind
      · apply sorted_merge
        · exact sorted_suffix hxs
        · exact hys
    · apply Sorted.cons_min
      apply sorted_min at hxs
      apply sorted_min at hys
      · apply min_all_merge
        · grind
        · grind
      · apply sorted_merge
        · exact hxs
        · exact sorted_suffix hys

-- Exercise 2.3
theorem merge_min_out (x : ℕ) (xs ys : List ℕ) (h_min_in_xs : ∀ y ∈ xs, x ≤ y)
  : Merge (x :: ys) xs = x :: Merge ys xs := by sorry

-- Exercise 2.4
theorem merge_min_out_sym(x : ℕ) (xs ys : List ℕ) (h_min_in_xs : ∀ y ∈ xs, x ≤ y) (h_min_in_ys : ∀ y ∈ ys, x ≤ y) : Merge ys (x ::xs)  = x :: Merge ys xs := by sorry
