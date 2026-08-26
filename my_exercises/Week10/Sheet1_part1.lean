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


/- We will use the following notion of graph distance -/
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Metric.html#SimpleGraph.dist

-- The extended distance between two vertices is the length of the shortest walk between them. It is ⊤ if no such walk exists.
#check SimpleGraph.edist
#print SimpleGraph.edist


/-
Lemma 1 : s ∈ bfs G s
-/

lemma lemma_1_s_in_bfs_s {s} {G : FinSimpleGraph V} : s ∈ bfs G s := sorry

/-
Lemma 2 : u ∈ bfs G s ∧ v ∈ G.neighborFinset u → v ∈ bfs G s
-/

lemma lemma2_u_bfs_so_are_neighbors (G : FinSimpleGraph V) (s u v) : u ∈ bfs G s ∧ v ∈ G.neighborSet u → v ∈ bfs G s := sorry


/-- A helper lemma for you to use-/
theorem edist_le_of_reachable {G : FinSimpleGraph (V)} {s : V} (v : V) (h_neq : ¬s = v)(h: G.Reachable s v) :
  let n := Fintype.card V
  G.edist s v ≤ n -1  := by
  have d0: G.edist s v < ⊤ := by
    by_contra!
    rw [@top_le_iff] at this
    rw [← @edist_ne_top_iff_reachable] at h
    contradiction
  have d1: G.dist s v ≠ 0:= by
    by_contra!
    rw [propext (Reachable.dist_eq_zero_iff h)] at this
    subst this
    exact h_neq rfl

  apply Reachable.exists_path_of_dist at h
  obtain ⟨p,hp1,hp2⟩ := h
  apply Walk.IsPath.length_lt at hp1
  intro n
  observe: p.length ≤ n-1
  have: G.dist s v = G.edist s v := Eq.symm ((fun {m} {n} hn ↦ (ENat.toNat_eq_iff hn).mp) d1 rfl)
  rw [← this]
  norm_cast
  aesop

-- Exercise
theorem exists_eq_cons_of_ne'.{u} {V : Type u} {G : SimpleGraph V} {u v : V} (hne : u ≠ v) :
    ∀ (p : G.Walk u v), ∃ (w : V) (p' : G.Walk u w) (h : G.Adj w v) , p =  p'.concat h := by
    sorry

/-- A helper lemma for you to use-/
theorem exists_edist_le_and_of_edist_eq {G : FinSimpleGraph (V)} {s : V} (k : ℕ) (v : V)
  (h : G.edist s v = ↑(k + 1)) : ∃ w, G.edist s w ≤ ↑k ∧ G.Adj w v := by
  have sneqv: s ≠ v := by
    by_contra!
    subst this
    simp at h
    absurd h
    exact ne_of_beq_false rfl
  apply exists_walk_of_edist_eq_coe at h
  obtain ⟨p,hp⟩ := h
  apply exists_eq_cons_of_ne' at sneqv
  specialize sneqv p
  obtain ⟨w,p',h1,hp2⟩ := sneqv
  use w
  refine ⟨?_,h1⟩
  have lp': p'.length = p.length -1 := by
    subst hp2
    simp_all only [ne_eq, Walk.length_concat, Nat.add_right_cancel_iff, add_tsub_cancel_right]
  calc
    G.edist s w ≤ p'.length  := Walk.edist_le p'
    _ = p.length -1  := by exact congrArg Nat.cast lp'
    _ = k := by norm_cast;omega


/--
Lemma 3: If a node `v` is reachable from `s`, then `v` will be in the list returned by `bfs G s`.
(This implies BFS is complete for the connected component of `s`).
-/
lemma bfs_visits_all_reachable (v : V) : G.Reachable s v → v ∈ bfs G s := by
  if h:s = v then
    subst h
    intro h
    unfold bfs
    apply lemma_1_s_in_bfs_s
  else
    intro h'
    let n := Fintype.card V
    have: G.edist s v ≤ n-1 := edist_le_of_reachable v h h'
    apply bfs_dist_k_reachable (n-1) v this

-- Translate the informal proof into Lean proof
  where bfs_dist_k_reachable (k :ℕ) (v : V): G.edist s v ≤ k → v ∈ bfs G s := by
  {
    sorry
  }


-- Exercise: Show that BFS solves the connectivity problem

#check connected_iff_exists_forall_reachable
#check reachable_comm
#check Reachable.trans

theorem spanning_iff_connected (G : FinSimpleGraph V)(s : V): #(bfs G s) = Fintype.card V ↔ G.Connected := by
  constructor
  · sorry -- Done in the previous week; no need to prove this here
  · -- If G is connected, every node is reachable from s.
    have s_reaches_all_nodes : ∀ (v : V), G.Reachable s v := by sorry
    have all_nodes_in_bfs_list : ∀ (v : V), v ∈ bfs G s := by sorry
    sorry
