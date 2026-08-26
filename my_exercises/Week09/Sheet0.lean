/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic

-- # How does Lean know a function terminate?
-- In many cases, Lean can automatically prove termination.

def Merge: List ℕ → List ℕ → List ℕ
  | x, [] => x
  | [], x => x
  | x::xs, y::ys =>
    if x ≤ y then x :: Merge xs (y::ys)
    else y :: Merge (x :: xs) ys

def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)

/- If Lean cannot deduce the termination (especially, in graph algorithms), we need to supply termination proof.
   We prove termination by showing that the recursion is `well-founded`. That is,
   we specify a `well-founed relation` and prove that each recursive call follows the `decreasing order` of the relation. -/

/- A binary relation `≺` is `well-founded` if it has no infinite descending chains `e₀ ≻ e₁ ≻ e₂ ≻ … `.
   Examples of well-bounded relation:
   1. the less-than relation < on ℕ
   2. the proper subsetr relation ⊊ on the set of finite subsets of ℕ
   Non-examples:
   1. the greater-than relation > on ℕ
   2. the less-than relation < on ℤ
-/

#check WellFounded

/-  Lean has convenient tactics to help us prove termination
 # New tactics for proving termination
 * `termination_by` : Specify a termination measure for recursive functions.
    for example, def f (n : ℕ) : ℕ → ℕ → Prop
   `termination_by a b => myMeasure n a b`
 * `decreasing_by`  : Manually prove that termination measure decreases for each recusrive call.
-/

def f₁  (n : ℕ) : ℕ :=
  if n = 0 then 0
  else f₁  (n-1)

def f₂  (n : ℕ) : ℕ →  ℕ
  | 0 => 0
  | x+1 => n + f₂ n x

def A : ℕ → ℕ → ℕ
  | 0,   y   => y+1
  | x+1, 0   => A x 1
  | x+1, y+1 => A x (A (x+1) y)
termination_by x y => (x, y)
decreasing_by
  · refine Prod.Lex.left 1 0 ?_
    omega
  · sorry
  · sorry
-- Lean recognizes the well-foundedness of the lexicographic order on the natural numbers

def div (x y : ℕ ) : ℕ  :=
  if h : 0 < y ∧ y ≤ x then
    div (x - y) y + 1
  else
    0
termination_by x+y
decreasing_by omega

def fib (n : ℕ) : ℕ :=
  if n ≤ 1 then n
  else fib (n - 1) + fib (n - 2)
--  termination_by n
--  decreasing_by omega ;omega

def findHelper (arr : Array α) (p : α → Bool) (i : Nat) : Option (Nat × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (i, x)
    else findHelper arr p (i + 1)
  else none
termination_by arr.size - i
decreasing_by omega
