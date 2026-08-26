/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Walk


namespace FAA

structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Symmetric Adj
  loopless : Irreflexive Adj

namespace SimpleGraph

variable {ι : Sort*} {V : Type u} (G : SimpleGraph V) {a b c u v w : V}

#check G

/-- `G.neighborSet v` is the set of vertices adjacent to `v` in `G`. -/
-- def neighborSet (v : V) : Set V := {w | G.Adj v w}

inductive Walk : V → V → Type u
  | nil {u : V} : Walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w

def Reachable (u v : V) : Prop := Nonempty (G.Walk u v)
def PreConnected : Prop := ∀ u v : V, G.Reachable u v

namespace Walk

variable {G}

/-- The length of a walk is the number of edges/darts along it. -/
def length {u v : V} : G.Walk u v → ℕ
  | nil => 0
  | cons _ q => q.length + 1

def triangle : SimpleGraph (Fin 3) where
  Adj := fun u v =>
    (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨  -- edge 0-1
    (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) ∨  -- edge 1-2
    (u = 2 ∧ v = 0) ∨ (u = 0 ∧ v = 2)    -- edge 2-0
  symm := by aesop_graph
  loopless := by simp_all [Irreflexive]

#check triangle

def triangle_walk : triangle.Walk 0 2 :=
  SimpleGraph.Walk.cons (by simp [triangle] : triangle.Adj 0 1)
 (SimpleGraph.Walk.cons (by simp [triangle] : triangle.Adj 1 2)
  SimpleGraph.Walk.nil)

#eval length triangle_walk

/-- The concatenation of two compatible walks. -/
@[trans]
def append {u v w : V} : G.Walk u v → G.Walk v w → G.Walk u w
  | nil, q => q
  | cons h p, q => cons h (p.append q)

/-- The concatenation of the reverse of the first walk with the second walk. -/
def reverseAux {u v w : V} : G.Walk u v → G.Walk u w → G.Walk v w
  | nil, q => q
  | cons h p, q => Walk.reverseAux p (cons (G.symm h) q)

/-- The walk in reverse. -/
@[symm]
def reverse {u v : V} (w : G.Walk u v) : G.Walk v u := w.reverseAux nil

lemma length_reverse_aux {u v : V} (p : G.Walk u v)
 (q : G.Walk u w): (p.reverseAux q).length = p.length + q.length := by
  fun_induction reverseAux
  · aesop
  · expose_names
    rw [ih1]
    simp [length]
    omega

/-- Example : The reverse of a walk has the same length -/
lemma length_reverse {u v : V} (p : G.Walk u v) : p.reverse.length = p.length := by
  simp [reverse]
  apply length_reverse_aux


/-- Exercise : The length of appended walks is the sum of their lengths -/
lemma length_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).length = p.length + q.length := sorry



@[symm]
theorem reachable_symm {v w : V} (hvw : G.Reachable v w) :
    G.Reachable w v := by
    exact (Nonempty.congr (fun a ↦ id a.reverse) fun a ↦ id a.reverse).mpr hvw

#check Nonempty
#check Nonempty.intro

-- Do it together.
@[trans]
theorem reachable_trans {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w) :
    G.Reachable u w := by
    cases huv
    cases hvw
    simp [Reachable]
    refine Nonempty.intro ?_
    (expose_names; exact val.append val_1)


-- Example
lemma connected_iff_exists_forall_reachable [nonempty : Nonempty V]: G.PreConnected ↔ ∃ v, ∀ w, G.Reachable v w := by
  constructor
  · sorry
  · intro h
    obtain ⟨v,h⟩ := h
    simp [PreConnected]
    sorry

-- Exercise
lemma preconnected_iff_forall_reachable :
    G.PreConnected ↔ ∀ u v : V, G.Reachable u v := by
  sorry

-- Exercise
lemma exists_central_vertex_if_connected [Fintype V] [Nonempty V]
    (hG : G.PreConnected) :
    ∃ v : V, ∀ w : V, ∃ (p : G.Walk v w), p.length ≤ Fintype.card V - 1 := by
  sorry


end Walk
end SimpleGraph
end FAA
