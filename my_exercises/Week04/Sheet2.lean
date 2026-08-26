/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false


/-! Inductive Type

In Lean 4, an inductive type is a way to define a new type by specifying its constructors,
which describe all possible ways to create values of that type.

* An inductive type is defined by listing its constructors.
  Each constructor can take arguments, allowing the creation of more complex structures.
* Inductive types can be recursive, meaning a constructor can include the type itself as part of its arguments.
  This enables defining structures like lists or trees.

-/

-- # Simple Inductive Type: Enumeration
inductive Color
| Red : Color
| Green : Color
| Blue : Color

#check Color
#check Color.Red

-- Lean can infer the type of the constructor
inductive Color'
| Red
| Green
| Blue

def favoriteColor : Color → String
| Color.Red   => "Red is lovely"
| Color.Green => "Green is calming."
| Color.Blue  => "Blue is clear."

def favoriteColor2 (c : Color) : String := match c with
| .Red   => "Red is lovely"
| .Green => "Green is calming."
| .Blue  => "Blue is clear."

#eval favoriteColor Color.Red
#check favoriteColor2

-- # Inductive type: Atomic element and a function
inductive OptionNat
| none
| some : ℕ → OptionNat

#check OptionNat

#check OptionNat.none
#check OptionNat.some
#check OptionNat.some 1
#check OptionNat.some 100

-- Here, If OptionNat is a set, then it contains {.none, .some 1, .some 2, .some 3, ...}

-- ℕ can be generalized to a type α
-- Now, let's define a new type called `MyOption` parameterized by a type α.
inductive MyOption (α : Type)
| none
| some : α → MyOption α

#check MyOption.some 50

#check MyOption.some "mystring"

-- Alternatively, some : α → MyOption α  can be written as some (a : α)
inductive MyOption' (α : Type)
| none
| some (a : α)

#check MyOption'.some 1
#check (MyOption'.some 1 : MyOption' ℕ)

#check MyOption ℕ
#check (MyOption.none : MyOption ℕ)
#check MyOption.some 2

-- Option can be used to implement to get some element
def getOrElse {α : Type} (opt : MyOption α) (default : α) : α :=
  match opt with
  | .none   => default
  | .some x => x

-- # Recursive Inductive Type: Nat
inductive nat
| zero
| succ (n: nat)
-- If nat is a set, then zero ∈ nat
-- If zero ∈ nat, then succ (zero) ∈ nat, and then succ (succ (zero)) ∈ nat
-- So, nat = {z,sz,ssz,sssz}

#check nat.zero
#check nat.succ (.zero)
#check nat.succ (.succ (.zero))

inductive nat2
| zero : nat2
| succ : nat2 → nat2

-- basecase : 0 ∈ S
-- inductive: if x ∈ S, then x+1 ∈ S

-- {0, succ(0), succ (succ (0))} ..
-- {0, 00, 000,0000, ...}

#check nat.zero
#check nat.zero.succ.succ

-- # Recursive Inductive Type: List
namespace MyList

inductive List (α : Type)
| nil
| cons (a : α) (l : List α )

-- the type List α is either
-- 1. an empty list (nil) or
-- 2. cons x xs where x : α and xs : List α
-- {[], [x], [x₁ x₂], [x₁ x₂ x₃] … }
#check List ℕ
#check (List.nil : List ℕ)
-- []
#check (List.cons 1 .nil)
-- [1]
#check (List.cons 2 (.cons 1 (.nil)))
-- [2 1]

-- Equivalently, it can be written this way in the functional form (Haskell-like)
inductive ListF (α : Type)
| nil : ListF α
| cons : α → ListF α → ListF α

#check List
#check List.nil
#check List.cons

-- # Exercise 2.1
-- Define a type of binary tree
-- it is a leaf or a node with two subtrees

-- correct
inductive BinaryTree (α : Type)
| nil
| node  (l: BinaryTree α)(a : α) (r: BinaryTree α)


-- Incorrect one
inductive BinaryTree_no_node (α : Type)
| leaf
| node (left : BinaryTree_no_node α) (right : BinaryTree_no_node α)

end MyList
