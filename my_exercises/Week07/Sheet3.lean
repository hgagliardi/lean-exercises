/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false

-- # do notations

-- Divide two numbers, returning None on division by zero
def safeDivide (x y : ℕ) : Option ℕ :=
  if y = 0 then none else some (x / y)

-- Compute ((100 / 2) / 5) + 3 using bind
def example3 : Option ℕ :=
  safeDivide 100 2 >>= fun r1 =>   -- r1 = 50
  safeDivide r1 5 >>= fun r2 =>    -- r2 = 10
  pure (r2 + 3)                     -- Wrap result back in box

#eval example3  -- some 13

-- Lean offers a special syntax called do-notation that makes writing and reading monadic code simpler and more intuitive.
-- ============================================
-- Example 4: Same thing with do notation
-- ============================================

-- Compute ((100 / 2) / 5) + 3 using bind
def example3' : Option ℕ := do
  let r1 ← safeDivide 100 2   -- Unbox r1 = 50
  let r2 ← safeDivide r1 5    -- Unbox r2 = 10
  pure (r2 + 3)
            -- Wrap result: some 13
#eval example3'  -- some 13

-- # When the first statement of the do block is 'let x ← E' expression.

-- do let r1 ← E
--    Stmt
--    ...
--    En

-- Translates to

-- E >>= fun r1 =>
-- do Stmt
--    ...
--    En

def example3__ : Option ℕ := do
  let r1 ← safeDivide 100 2   -- Unbox r1 = 50
  let r2 ← safeDivide r1 5    -- Unbox r2 = 10
  pure (r2 + 3)
            -- Wrap result: some 13
#eval example3'  -- some 13

-- Compute ((100 / 2) / 5) + 3 using bind
def example3''' : Option ℕ := do
  safeDivide 100 2 >>= fun r1 ↦ do
  let r2 ← safeDivide r1 5
  pure (r2 + 3)


-- # When the first statement of the do block is an expression 'E1'

-- do E1
--    Stmt
--    ...
--    En

-- Translates to

-- E1 >>= fun () =>
-- do Stmt
--    ...
--    En

-- # Finally, when the first statement of the do block is let x := E1'

-- do let x := E1
--    Stmt
--    ...
--    En

-- Translates to

-- let x := E1
-- do Stmt
--    ...
--    En

-- ============================================
-- Example 5: Write this using do notation
-- ============================================

-- Compute (a / b + c / d) / e
def div_plus_div_div (a b c d e : ℕ) : Option ℕ := do
  let x ← safeDivide a b     -- Unbox x
  let y ← safeDivide c d     -- Unbox y
  let sum := x + y           -- Regular computation (no box)
  let result ← safeDivide sum e  -- Unbox result
  pure result                -- Wrap final answer

-- Translates to:
def complexCompute'' (a b c d e : ℕ) : Option ℕ :=
  safeDivide a b >>= fun x =>
  safeDivide c d >>= fun y =>
  let sum := x + y
  safeDivide sum e >>= fun result =>
  pure result


-- ============================================
-- EXERCISE: More Complex Expression
-- ============================================

/-
Implement a function that computes: (a / b) * (c / d) + (e / f)

Requirements:
1. Divide a by b (use safeDivide)
2. Divide c by d (use safeDivide)
3. Multiply the two results
4. Divide e by f (use safeDivide)
5. Add the multiplication result and the division result
6. Return none if any division fails

You'll need this helper:
-/

def safeMult (x y : ℕ) : Option ℕ :=
  some (x * y)  -- Multiplication always succeeds for natural numbers

def safeAdd (x y : ℕ) : Option ℕ :=
  some (x + y)  -- Addition always succeeds for natural numbers

/-
Part A: Implement using do notation
-/

def computeExpr (a b c d e f : ℕ) : Option ℕ := do
  sorry  -- Your code here

/-
Part B: Implement the SAME function WITHOUT do notation
(translate your do notation to explicit >>= operators)
-/

def computeExpr' (a b c d e f : ℕ) : Option ℕ :=
  sorry  -- Your code here


-- Test cases (uncomment after implementing):
-- #eval computeExpr 20 4 15 3 10 2    -- some 30  because (20/4) * (15/3) + (10/2) = 5 * 5 + 5 = 30
-- #eval computeExpr 20 0 15 3 10 2    -- none     (division by zero in first division)
-- #eval computeExpr 20 4 15 0 10 2    -- none     (division by zero in second division)
-- #eval computeExpr 20 4 15 3 10 0    -- none     (division by zero in third division)
-- #eval computeExpr 12 3 8 2 6 3      -- some 18  because (12/3) * (8/2) + (6/3) = 4 * 4 + 2 = 18


namespace FAA

class LawfulMonad (m : Type → Type)
  extends Pure m, Bind m where
  pure_bind {α β : Type} (a : α) (f : α → m β) :
    (pure a >>= f) = f a
  bind_pure {α : Type} (ma : m α) :
    (ma >>= pure) = ma
  bind_assoc {α β γ : Type} (f : α → m β) (g : β → m γ)
      (ma : m α) :
    ((ma >>= f)>>=  g) = (ma >>= (fun a ↦ f a >>= g))

-- The structure takes over the fields and syntax extensions from the Bind and Pure structures,
-- which define the bind and pure operations for m and provide related syntactic conveniences.

-- To use this definition with a specific monad,
-- we need to provide the type constructor m (for example, Option),
-- along with the bind and pure functions, and verify that they satisfy the required monad laws.


--------------------------------------------------------------------------------
-- Exercise 1: Identity Monad (Warm-up)
--------------------------------------------------------------------------------
-- The identity monad just wraps a value with no additional structure.
-- Our first monad is the trivial monad `m := id` (i.e., `m := (fun α ↦ α)`). -/

def id.pure {α : Type} : α → id α
  | a => a

def id.bind {α β : Type} : id α → (α → id β) → id β
  | a, f => f a

-- Exercise: Prove that Id is a lawful monad

instance id.LawfulMonad : LawfulMonad id :=
  { pure       := id.pure
    bind       := id.bind
    pure_bind  :=
      by sorry
    bind_pure  :=
      by sorry
    bind_assoc :=
      by sorry
         }

--------------------------------------------------------------------------------
-- Exercise 2: Option Monad
--------------------------------------------------------------------------------
-- Already defined in Lean, but let's prove the laws explicitly.


def Option.pure {α : Type} : α → Option α :=
  Option.some

def Option.bind {α β : Type} :
  Option α → (α → Option β) → Option β
  | Option.none,   _ => Option.none
  | Option.some a, f => f a

instance Option.LawfulMonad : LawfulMonad Option :=
  { pure       := Option.pure
    bind       := Option.bind
    pure_bind  :=
      by sorry
    bind_pure  :=
      by sorry
    bind_assoc :=
      by sorry }

-- Hint: You'll need to case split on Option values (none vs some)
-- Use: cases ma with | none => ... | some a => ...

--------------------------------------------------------------------------------
-- Exercise 3: State Monad
--------------------------------------------------------------------------------

/- ## Mutable State
The state monad offers a way to model stateful computations. -/

def Action (σ α : Type) : Type :=
  σ → α × σ

def Action.read {σ : Type} : Action σ σ
  | s => (s, s)

def Action.write {σ : Type} (s : σ) : Action σ Unit
  | _ => ((), s)

/- `Action.pure` leaves the state unchanged, similar to a `return` statement.
   `Action.bind` sequences two operations, threading state from one to the next. -/

def Action.pure {σ α : Type} (a : α) : Action σ α
  | s => (a, s)

def Action.bind {σ : Type} {α β : Type} (ma : Action σ α)
      (f : α → Action σ β) :
    Action σ β
  | s =>
    match ma s with
    | (a, s') => f a s'

instance Action.LawfulMonad {σ : Type} :
  LawfulMonad (Action σ) :=
  { pure       := Action.pure
    bind       := Action.bind
    pure_bind  :=
      by sorry
    bind_pure  :=
      by sorry
    bind_assoc :=
      by sorry}
