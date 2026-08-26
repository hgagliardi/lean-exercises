/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false

section Monad

-- ## Motivating Example

-- Divide two numbers, returning None on division by zero
def safeDivide (x y : ℕ) : Option ℕ :=
  if y = 0 then none else some (x / y)

-- Compute (a / b) / c without monad
def compute1 (a b c : ℕ) : Option ℕ :=
  match safeDivide a b with
  | none => none
  | some r1 =>
      match safeDivide r1 c with
      | none => none
      | some r2 => some r2

-- Gets worse with more steps!
def compute2 (a b c d : ℕ) : Option ℕ :=
  match safeDivide a b with
  | none => none
  | some r1 =>
      match safeDivide r1 c with
      | none => none
      | some r2 =>
          match safeDivide r2 d with
          | none => none
          | some r3 => some r3

-- Same computation with do notation
def compute1' (a b c : ℕ) : Option ℕ := do
  let r1 ← safeDivide a b
  let r2 ← safeDivide r1 c
  return r2

def compute2' (a b c d : ℕ) : Option ℕ := do
  let r1 ← safeDivide a b
  let r2 ← safeDivide r1 c
  let r3 ← safeDivide r2 d
  return r3

#eval compute2' 100 2 5 2
#eval compute2' 100 0 5 2
#eval compute2' 100 2 0 2

-- Monad allows us to focus on the main logic while handling side-effect seperately,
-- enabling separation of concerns.

-- ## What is Monad?
#check Monad
#print Monad

-- Intuitively, the monad is like duct tape. It ``glues`` things together. More preciesly, it ``composes`` things.
-- High-level Explanation

def HalfExact (x : ℕ) : Option ℕ :=
  if Even x then some (x/2) else none

#check HalfExact

#eval HalfExact 2
#eval HalfExact 3
--#eval HalfExact (some 2)

-- using bind operation
#eval some 10 >>= HalfExact
#eval some 3 >>= HalfExact
#eval pure 6 >>= HalfExact >>= HalfExact >>= HalfExact
#eval none >>= HalfExact


namespace FAA

-- Type constructor is f: Type → Type
-- Monad is a type constructor m : Type → Type equipped with two operations

class Monad (m : Type → Type) where
  pure {α : Type} : α → m α
  bind {α β :Type}: m α → (α → m β) → m β

#check Monad

-- In lean, a class is a structure parameterized by some types (in this case, a type constructor)
-- the implementation of each operation depends on specific instantiation of the type
-- deferred to `instantiate` using `typeclass resolution`, which automatically synthesize the specific instance.

#check Monad.pure
#check Monad.bind

-- Here, the sqaure brackets indiates that the instance of type : Monad m is `instance implicit`.

-- For example, we want to instantiate Monad instance for Option
-- Monad instance for Option
#check Monad Option
-- We can register the instances by:
instance : Monad Option where
  pure x := some x
  bind opt f :=
    match opt with
    | none => none
    | some x => f x

/- Think the monad as a box with content a : α
In short, `pure a` just wraps the value a in a box,
while    `bind ma f` (written as `ma >>= f`) takes a monad `ma`, and a function `f` that returms a monad, and it returns a monad.
-/

#print safeDivide

-- Try safeDivide
#eval safeDivide 4 2
#eval safeDivide 4 0
#eval some 4 >>= (fun r => safeDivide r 2)

-- ============================================
-- Example 1: Using bind directly (with >>=)
-- ============================================

-- Compute (20 / 4) / 2 using bind
def example1 : Option ℕ :=
  safeDivide 20 4 >>= fun r1 =>    -- r1 = 5, still in box
  safeDivide r1 2                   -- 5 / 2 = 2

#eval example1  -- some 2

-- Step by step what happens:
-- 1. safeDivide 20 4        → some 5        (20/4 = 5)
-- 2. bind (some 5) (fun r1 => safeDivide r1 2)
--    - "unbox" 5 from some 5
--    - apply function: safeDivide 5 2 → some 2
-- 3. Result: some 2

-- With failure:
def example2 : Option ℕ :=
  safeDivide 20 0 >>= fun r1 =>    -- Division by zero!
  safeDivide r1 2

#eval example2  -- None

-- What happens:
-- 1. safeDivide 20 0        → none
-- 2. bind none (fun r1 => ...)
--    - Match on none → return none immediately
--    - Never executes the function!

-- ============================================
-- Example 3: Chaining multiple operations
-- ============================================

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
