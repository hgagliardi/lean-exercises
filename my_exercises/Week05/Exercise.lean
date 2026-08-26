/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false


-- # Exercise: Define IsPalindrome
-- This should be true if and only if it can be read in forward and reverse direction
-- e.g., 'a', 'aba', 'aabbcbbaa'

inductive IsPalindrome {α : Type} : List α → Prop
--  | nil :  ??
--  | single (a : α) :  ??
--  | cons_eq (a : α) (l : List α) :  ??

theorem IsPalindrome_imp_eq_reverse {α : Type} (l : List α) :
  IsPalindrome l → l = List.reverse l := by sorry

theorem IsPalindrome_pmi_eq_reverse {α : Type} (l : List α) :
  l = List.reverse l → IsPalindrome l  := by sorry

theorem IsPalindrome_reverse {α : Type} (l : List α) (h: IsPalindrome l) :
   IsPalindrome l.reverse  := by sorry

-- # Exercise: Binary Tree, Mirror and Complete Binary Tree
-- Define BinaryTree as follows

inductive BinaryTree
  | nil
  | node (left : BinaryTree) (key : ℕ) (right : BinaryTree)

-- Define mirror operation as reversing the tree
def mirror : BinaryTree → BinaryTree
  | BinaryTree.nil        => BinaryTree.nil
  | BinaryTree.node l key r => BinaryTree.node (mirror r) key (mirror l)

--  Prove that mirror of mirror of a tree is the tree itself.
theorem mirror_mirror (t : BinaryTree) :
    mirror (mirror t) = t := by sorry

--  Prove that mirror of mirror of a tree is the tree itself.
theorem mirror_nil_iff (r : BinaryTree): mirror r = BinaryTree.nil ↔ r = BinaryTree.nil := by sorry

-- A binary tree is complete if every node has either two non-empty subtrees or two empty subtrees.
-- We can define it using inductive predicate as follows.

inductive Complete : BinaryTree  → Prop
  | leaf : Complete BinaryTree.nil
  | node  (l : BinaryTree) (key : ℕ) (r : BinaryTree)
      (hl : Complete l) (hr : Complete r)
      (hiff : l = BinaryTree.nil ↔ r = BinaryTree.nil) :
    Complete (BinaryTree.node l key r)

-- Prove that if t is complete then its mirroring is also complete.
theorem complete_mirror  (t : BinaryTree)
      (ht : Complete t) :
    Complete (mirror t) := by sorry
