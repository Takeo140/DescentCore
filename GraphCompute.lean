/-
# GraphCompute

Computation for graph reachability, with a correctness proof.

`GraphDescent` shows that reachability within a bound `k` is a
well-behaved predicate. This file turns it into a computation:
`reachBool g k a t` decides, by recursion on the bound, whether `t`
can be reached from `a` in exactly `k` steps — at each step, follow
every outgoing edge of the current vertex and continue with one less
step of budget.

For any graph, this file proves — as theorems, not axioms:

* **Soundness.** If the computation says `true`, the reachability
  predicate holds: `reachBool g k a t = true → ReachIn g k a t`.
* **Completeness.** If the predicate holds, the computation says
  `true`: `ReachIn g k a t → reachBool g k a t = true`.
* **The decision theorem.** Together: `reachBool g k a t = true ↔
  ReachIn g k a t`. The computable function and the inductive
  predicate decide exactly the same relation.

The worked examples at the bottom are checked by `decide`: in the
example graph, `0` reaches `3` in exactly three steps and in no
fewer, and reaches `4` in one step.

Everything is proved in core Lean: no Mathlib, no `sorry`. The file is
self-contained and restates the bounded-reachability predicate it
needs.

Author: Takeo Yamamoto
License: Apache-2.0
-/

namespace GraphCompute

/-- A finite graph: a list of directed edges between vertices. -/
abbrev Graph := List (Nat × Nat)

/-- Reachability in exactly `k` steps: a chain of precisely `k` edges
leads from `a` to `t`. -/
inductive ReachIn (g : Graph) : Nat → Nat → Nat → Prop
  | zero (a : Nat) : ReachIn g 0 a a
  | succ {k a b c : Nat} : (a, b) ∈ g → ReachIn g k b c → ReachIn g (k + 1) a c

/-- The neighbours of a vertex: the endpoints of its outgoing edges. -/
def neighbors (g : Graph) (a : Nat) : List Nat :=
  (g.filter (fun e => decide (e.1 = a))).map Prod.snd

/-- A vertex is a neighbour exactly when the edge is in the graph. -/
theorem mem_neighbors {g : Graph} {a b : Nat} :
    b ∈ neighbors g a ↔ (a, b) ∈ g := by
  constructor
  · intro h
    rw [neighbors, List.mem_map] at h
    obtain ⟨e, he, hb⟩ := h
    rw [List.mem_filter] at he
    obtain ⟨heg, hp⟩ := he
    have hfst : e.1 = a := of_decide_eq_true hp
    have : e = (a, b) := by
      cases e with
      | mk x y => exact Prod.ext hfst hb
    rw [this] at heg
    exact heg
  · intro h
    rw [neighbors, List.mem_map]
    exact ⟨(a, b), List.mem_filter.mpr ⟨h, by simp⟩, rfl⟩

/-- The decision procedure: can `t` be reached from `a` in exactly
`k` steps? Recursion on the budget `k`; at each step, try every
outgoing edge. -/
def reachBool (g : Graph) : Nat → Nat → Nat → Bool
  | 0, a, t => a == t
  | k + 1, a, t => (neighbors g a).any (fun b => reachBool g k b t)

/-- Soundness: a `true` answer is a genuine chain of edges. -/
theorem reachBool_sound {g : Graph} :
    ∀ {k a t : Nat}, reachBool g k a t = true → ReachIn g k a t := by
  intro k
  induction k with
  | zero =>
    intro a t h
    have hEq : a = t := beq_iff_eq.mp h
    subst hEq
    exact ReachIn.zero a
  | succ k ih =>
    intro a t h
    rw [reachBool] at h
    rw [List.any_eq_true] at h
    obtain ⟨b, hb, hb2⟩ := h
    exact ReachIn.succ (mem_neighbors.mp hb) (ih hb2)

/-- Completeness: every genuine chain of edges is found. -/
theorem reachBool_complete {g : Graph} {k a t : Nat}
    (h : ReachIn g k a t) : reachBool g k a t = true := by
  induction h with
  | zero a => simp [reachBool]
  | succ he _ ih =>
    rw [reachBool, List.any_eq_true]
    exact ⟨_, mem_neighbors.mpr he, ih⟩

/-- The decision theorem: the computation and the predicate agree. -/
theorem reachBool_iff {g : Graph} {k a t : Nat} :
    reachBool g k a t = true ↔ ReachIn g k a t :=
  ⟨reachBool_sound, reachBool_complete⟩

/-- A concrete graph: the chain `0 → 1 → 2 → 3` and a spur `0 → 4`. -/
def exampleGraph : Graph := [(0, 1), (1, 2), (2, 3), (0, 4)]

/-- `0` reaches `3` in exactly three steps. -/
theorem example_three_steps : reachBool exampleGraph 3 0 3 = true := by decide

/-- But not in two: the budget matters. -/
theorem example_not_two_steps : reachBool exampleGraph 2 0 3 = false := by decide

/-- The spur: `0` reaches `4` in one step. -/
theorem example_spur : reachBool exampleGraph 1 0 4 = true := by decide

end GraphCompute
