/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
import Lectures.Week08.Sheet2
import Lectures.Week08.API

-- Running Time Analysis
set_option autoImplicit false
set_option tactic.hygienic false

-- The following helper lemmas are useful
@[simp] theorem merge_time (xs ys : List ℕ) :
  (merge xs ys).time = xs.length + ys.length := by sorry

@[simp] theorem merge_ret_length_eq_sum (xs ys : List ℕ) :
  (merge xs ys).ret.length = xs.length + ys.length := by sorry

@[simp] theorem mergeSort_same_length (xs : List ℕ) :
  (mergeSort xs).ret.length = xs.length:= by sorry

-- Next, we pave our way towards proving O(n log n) running time of merge sort.

example (xs : List ℕ) (h : ∃ k, xs.length = 2 ^ k) :
  (mergeSort xs).time = xs.length*(Nat.log 2 xs.length)  := by sorry

def MS_REC : ℕ → ℕ
| 0 => 0
| n@(x+1) =>
  if x = 0 then 0
  else
    MS_REC (n/2) + MS_REC ((n-1)/2 + 1) + n

#eval mergeSort [4,1,3,4,5,6]
#eval MS_REC 10

theorem mergeSort_time_eq_MS_REC (xs : List ℕ) :
  (mergeSort xs).time = MS_REC xs.length := by
  fun_induction mergeSort
  · simp only [Pure.pure, pure]
    unfold MS_REC
    simp_all
    grind
  · simp_all only [not_lt, Bind.bind, TimeM.time_of_bind, merge_time, mergeSort_same_length]
    conv =>
      right
      unfold MS_REC
    simp_all
    split
    · simp_all
    · simp_all
      grind

def MS_REC_SIMP : ℕ → ℕ
| 0 => 0
| n@(x+1) =>
  if x = 0 then 0
  else
    2*MS_REC_SIMP (n/2) + n

theorem MS_REC_SIMP_EQ (n : ℕ) :   (MS_REC (2^n))= (MS_REC_SIMP (2^n))  := by
  induction' n  with n ih
  · unfold MS_REC_SIMP MS_REC
    simp only [↓reduceIte]
  · unfold MS_REC_SIMP MS_REC
    split <;> all_goals (simp_all)
    rename_i heq
    split
    next h =>
      subst h
      simp_all only [zero_add, Nat.pow_eq_one, OfNat.ofNat_ne_one, Nat.add_eq_zero, one_ne_zero, and_false, or_self]
    next h =>
      simp_all only [Nat.add_right_cancel_iff]
      rw [← heq]
      grind


theorem MS_REC_SIMP_EQ_CLOSED (n : ℕ) : MS_REC_SIMP (2^n) = 2^n * n := by
  induction' n  with n ih
  · unfold MS_REC_SIMP
    aesop
  · unfold MS_REC_SIMP
    simp_all only
    split
    next heq =>
      simp_all only [Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, Nat.add_eq_zero, one_ne_zero, and_false,
        not_false_eq_true, and_true]
    next heq =>
      simp_all only [Nat.succ_eq_add_one]
      split
      next h =>
        subst h
        simp_all only [zero_add, Nat.pow_eq_one, OfNat.ofNat_ne_one, Nat.add_eq_zero, one_ne_zero, and_false, or_self]
      next h =>
        rw [← heq]
        grind

-- The time is written assuming the length of the list is a power of two (for simplicity).
theorem MStimeBound (xs : List ℕ) (h : ∃ k, xs.length = 2 ^ k) :
  (mergeSort xs).time = xs.length*(Nat.log 2 xs.length)  := by
  rw [mergeSort_time_eq_MS_REC]
  obtain ⟨k,hk⟩ := h
  rw [hk,MS_REC_SIMP_EQ,MS_REC_SIMP_EQ_CLOSED]
  simp only [Nat.lt_add_one, Nat.log_pow]
