/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false


@[simp,grind] def Nat.MinOfList (a :ℕ ) (t: List ℕ) : Prop := ∀ y ∈ t, a ≤ y

-- Let's discuss in English
-- How do define inductively of sortedness

-- inductive predicate
inductive Sorted: List ℕ  → Prop
  | nil : Sorted []
  | single (a : ℕ) : Sorted [a]
  | cons (a b : ℕ) (t : List ℕ ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
  | cons_min (a :ℕ) (t : List ℕ) : a.MinOfList t → Sorted (t) →  Sorted (a :: t)

-- introduction rules/constrtuctor
#check Sorted.single
#check Sorted.nil

-- # Example
example: Sorted [1] := by
  exact Sorted.single 1

#check Sorted.cons

-- # Example
example: Sorted [1,2,3] := by
  apply Sorted.cons
  omega
  apply Sorted.cons
  omega
  exact Sorted.single 3

-- # Example
example: ¬ Sorted [20,3,1] := by
  by_contra!
  cases this
  · omega
  · aesop

-- # Example
example: ¬ Sorted [1,3,2] := by
  by_contra!
  cases this
  · cases a_2
    omega
    aesop
  · cases a_2
    omega
    aesop

-- # Exercise
example: ¬ Sorted [1,2,4,3] := by
  by_contra!
  cases this <;> all_goals cases a_2 <;> all_goals cases a_4 <;> all_goals aesop

-- # Example
#check Sorted
-- Example: Proof by cases
theorem sorted_min {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) :  x.MinOfList xs  := by
  cases hxs
  · simp
  · simp only [Nat.MinOfList, List.mem_cons, forall_eq_or_imp]
    constructor
    · exact a_1
    · apply sorted_min at a_2
      grind
  · exact a_1

-- # Exercise 5.1: Proof by induction
theorem sorted_min' {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) :  x.MinOfList xs  := by
  generalize h_eq : x :: xs = l
  replace hxs : Sorted l := by rwa [← h_eq]
  induction' hxs generalizing xs x
  all_goals grind

-- # Exercise 5.2
theorem sorted_is_preserved_by_min_cons {a : ℕ} {t : List ℕ} (hmin : a.MinOfList t) (ht : Sorted t) : Sorted (a :: t) := by
  exact Sorted.cons_min a t hmin ht

-- # Exercise 5.3
-- Define `merge` function that takes two sorted lists and ouputs a sorted list
-- merge [1, 5, 8] [2, 4, 9] = [1, 2, 4, 5, 8, 9]
-- merge [10,20] [] = [10, 20]
-- merge [2, 4, 4, 8] [1, 5, 8, 9] = [1, 2, 4, 4, 5, 8, 8, 9]

def merge: List ℕ → List ℕ → List ℕ
  | x, [] => x
  | [], x => x
  | x::xs, y::ys =>
    if x ≤ y then x :: merge xs (y::ys)
    else y :: merge (x :: xs) ys
