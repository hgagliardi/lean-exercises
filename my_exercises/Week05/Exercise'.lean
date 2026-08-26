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
  | nil : IsPalindrome ([])
  | single (a : α) : IsPalindrome ([a])
  | cons_eq (a : α) (l : List α) :  IsPalindrome (l) → IsPalindrome (a::l ++[a])

theorem IsPalindrome_imp_eq_reverse {α : Type} (l : List α) :
  IsPalindrome l → l = List.reverse l := by
  intro h
  induction' h
  · simp only [List.reverse_nil]
  · simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
  · simpa

-- Challenging one :)
theorem IsPalindrome_pmi_eq_reverse {α : Type} (l : List α) :
  l = List.reverse l → IsPalindrome l  := by sorry

theorem IsPalindrome_reverse {α : Type} (l : List α) (h: IsPalindrome l) :
   IsPalindrome l.reverse  := by
  induction' h
  · simp only [List.reverse_nil]
    exact IsPalindrome.nil
  · simp
    exact IsPalindrome.single a
  · rw [← IsPalindrome_imp_eq_reverse (a :: l_1 ++ [a]) ?_]
    all_goals
    apply IsPalindrome.cons_eq
    exact a_1



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
    mirror (mirror t) = t := by
    fun_induction mirror t
    · aesop
    · grind [mirror]

--  Prove that mirror of mirror of a tree is the tree itself.
theorem mirror_nil_iff (r : BinaryTree): mirror r = BinaryTree.nil ↔ r = BinaryTree.nil := by
  induction' r
  · simp only [mirror]
  · simp only [mirror, reduceCtorEq]

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
    Complete (mirror t) := by
    induction' ht
    · exact Complete.leaf
    · simp only [mirror]
      apply Complete.node
      · exact hr_ih
      · exact hl_ih
      · rw [mirror_nil_iff,mirror_nil_iff]
        symm at hiff
        exact hiff
