/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
import Lectures.Week08.API

set_option autoImplicit false
set_option tactic.hygienic false

-- # Q: How to analyze time complexity?
-- We will instrument the code to track the time. However, we do not want to interfere the correctness analysis.
-- We learn an elegant way to do this using Moad
-- # Separation of concerns: the correctness proof and running time proof should not interfere to each other

def len : List ℕ →  ℕ
| [] => 0
| _ :: xs => 1+ len xs

-- lenT with do notations
def lenT : List ℕ → TimeM ℕ
| [] => return 0
| _ :: xs => do
    ✓ 0
    let len_xs ← lenT xs
    ✓ (1 + len_xs)

-- Example usage
#eval lenT []
#eval lenT [3,2,5]
#eval lenT [1,2,3,4,5]


theorem lenT_correctness (xs : List ℕ): (lenT xs).ret = len xs := by
  induction xs
  · rfl
  · simp only [lenT, bind, TimeM.tick, PUnit.zero_eq, TimeM.ret_bind]
    rw [tail_ih]
    rfl

theorem lenT_time (xs : List ℕ ): (lenT xs).time = 2 *(len xs) := by
  induction xs
  · rfl
  · simp only [lenT, bind, TimeM.tick, PUnit.zero_eq, TimeM.time_of_bind]
    rw [tail_ih]
    rw [show len (head :: tail) = 1 + len tail from rfl]
    omega


-- ============================================================================
-- EXERCISE 1: Sum of a list
-- ============================================================================
-- Implement sumT that computes the sum of a list with time tracking
-- Each recursive call should cost 1 time unit
-- Expected time complexity: n where n is the length of the list

def sumT : List ℕ → TimeM ℕ
| [] => sorry
| x :: xs => sorry

def sum : List ℕ → ℕ
| [] => 0
| x :: xs => x + sum xs

-- TODO: Prove correctness
theorem sumT_correctness (xs : List ℕ): (sumT xs).ret = sum xs := by
  sorry

-- TODO: Prove time complexity
theorem sumT_time (xs : List ℕ): (sumT xs).time = xs.length := by
  sorry

-- ============================================================================
-- EXERCISE 2: Reverse a list
-- ============================================================================
-- Implement reverseT that reverses a list with time tracking
-- Each cons operation should cost 1 time unit
-- Expected time complexity: n² where n is the length of the list

def reverseT : List ℕ → TimeM (List ℕ)
| [] => sorry
| x :: xs => sorry

def reverse : List ℕ → List ℕ
| [] => []
| x :: xs => reverse xs ++ [x]

-- TODO: Prove correctness
theorem reverseT_correctness (xs : List ℕ): (reverseT xs).ret = reverse xs := by
  sorry

-- Hint: You'll need a helper lemma about the time of append
-- TODO: Prove time complexity is O(n²)
theorem reverseT_time_quadratic (xs : List ℕ):
  ∃ c, (reverseT xs).time ≤ c * xs.length * xs.length := by
  sorry

-- ============================================================================
-- EXERCISE 3: Tail-recursive reverse with accumulator
-- ============================================================================
-- Implement a tail-recursive reverse using an accumulator
-- Each step should cost 1 time unit
-- Expected time complexity: n (linear, much better than reverseT!)

def reverseTailT : List ℕ → List ℕ → TimeM (List ℕ)
| [], acc => sorry
| x :: xs, acc => sorry

def reverseTail : List ℕ → List ℕ → List ℕ
| [], acc => acc
| x :: xs, acc => reverseTail xs (x :: acc)

-- TODO: Prove correctness
theorem reverseTailT_correctness (xs acc : List ℕ):
  (reverseTailT xs acc).ret = reverseTail xs acc := by
  sorry

-- TODO: Prove linear time complexity
theorem reverseTailT_time (xs acc : List ℕ):
  (reverseTailT xs acc).time = xs.length := by
  sorry
