/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Metric



structure FinSimpleGraph (V : Type u) [Fintype V] [DecidableEq V]  extends SimpleGraph V

noncomputable
instance  fintypeFinSimpleGraph {V : Type u} [Fintype V] [DecidableEq V] (G : FinSimpleGraph V) (v : V): Fintype (G.neighborSet v) :=  Fintype.ofFinite ↑(G.neighborSet v)

open Finset SimpleGraph

variable  {V : Type*} [Fintype V] [DecidableEq V]


noncomputable
def bfs_rec
(G : FinSimpleGraph V)
(queue : List V)
(visited : Finset V)
  :=
  match queue with
  | [] => visited
  | v :: queue =>
    let new_neighbors := (G.neighborFinset v) \ visited
    let queue' := queue ++ new_neighbors.toList
    let visited' := visited ∪ new_neighbors
    bfs_rec G queue' visited'
    termination_by (Fintype.card V - #visited, queue.length) decreasing_by sorry

#check bfs_rec.induct

noncomputable def bfs
  (G : FinSimpleGraph V)
  (s : V)
  : Finset V :=
  bfs_rec G {s} {s}

/-
Lemma 1 : s ∈ bfs G s
-/

lemma lemma_1_s_in_bfs_s {s} {G : FinSimpleGraph V} : s ∈ bfs G s := by sorry

-- The key insight: Strengthen the statement to make it provable by induction.
-- Instead of proving the specific case s ∈ bfs_rec G [s] {s}, we prove a more general invariant that:

-- 1. Holds at the start
-- 2. Is preserved by each recursive call
-- 3. Implies what we want

/-
Lemma 2 : u ∈ bfs G s ∧ v ∈ G.neighborFinset u → v ∈ bfs G s
-/

lemma lemma2_u_bfs_so_are_neighbors (G : FinSimpleGraph V) (s u v) : u ∈ bfs G s ∧ v ∈ G.neighborSet u → v ∈ bfs G s := by sorry
