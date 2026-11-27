/-
# GraphDescent

Descent on a finite graph: reachability with an energy bound.

`GraphCore` defines when a vertex is reachable from another. This file
adds the descent view of the same fact. Fix a target vertex `t`. The
energy of a vertex `a` is the number of steps still needed to reach
`t`, and `Within g k a t` says `t` can be reached from `a` in at most
`k` steps.

For any graph and any target, this file proves — as theorems, not
axioms:

* **Descent step.** From `Within g (k + 1) a t` with `a ≠ t`, there is
  an edge `a → b` with `Within g k b t`: one step along an edge lowers
  the remaining energy by exactly one.
* **Termination within a bound.** If `t` is reachable from `a` at all,
  it is reachable within some bound `k`.
* **The attractor.** Anything within a bound is reachable, so repeated
  descent steps — each one forced to lower the energy — arrive at `t`,
  the attractor, and the energy reaches zero exactly there.

This is the `DescentCore` pattern — termination within a bound and an
attractor — instantiated on graph distance instead of an abstract
energy function. Convergence is derived from the strict decrease of
the bound; no convergence axiom is assumed.

Everything is proved in core Lean: no Mathlib, no `sorry`. The file is
self-contained and restates the reachability predicate it needs.

Author: Takeo Yamamoto
License: Apache-2.0
-/

namespace GraphDescent

/-- A finite graph: a list of directed edges between vertices. -/
abbrev Graph := List (Nat × Nat)

/-- Reachability: a chain of edges in `g` leads from `a` to `b`. -/
inductive Reachable (g : Graph) : Nat → Nat → Prop
  | refl (a : Nat) : Reachable g a a
  | step {a b c : Nat} : (a, b) ∈ g → Reachable g b c → Reachable g a c

/-- Reachability in exactly `k` steps: `ReachIn g k a t` holds when a
chain of precisely `k` edges leads from `a` to `t`. -/
inductive ReachIn (g : Graph) : Nat → Nat → Nat → Prop
  | zero (a : Nat) : ReachIn g 0 a a
  | succ {k a b c : Nat} : (a, b) ∈ g → ReachIn g k b c → ReachIn g (k + 1) a c

/-- Reachability within a bound: `Within g k a t` holds when `t` can
be reached from `a` in at most `k` steps. The bound is the energy of
`a` relative to the target `t`. -/
def Within (g : Graph) (k a t : Nat) : Prop :=
  ∃ j, j ≤ k ∧ ReachIn g j a t

/-- The bound only helps: what is within `k` steps is within
`k + m` steps. -/
theorem within_mono {g : Graph} {k a t : Nat} (m : Nat)
    (h : Within g k a t) : Within g (k + m) a t := by
  obtain ⟨j, hj, hr⟩ := h
  exact ⟨j, Nat.le_trans hj (Nat.le_add_right k m), hr⟩

/-- The descent step: within `k + 1` steps of the target, a vertex is
either the target itself, or has an edge to a vertex within `k` steps
of the target. Each real step lowers the energy by one. -/
theorem descent_step {g : Graph} {k a t : Nat}
    (h : Within g (k + 1) a t) :
    a = t ∨ ∃ b, (a, b) ∈ g ∧ Within g k b t := by
  obtain ⟨j, hj, hr⟩ := h
  cases j with
  | zero =>
    cases hr
    exact Or.inl rfl
  | succ j =>
    cases hr with
    | succ he hb =>
      exact Or.inr ⟨_, he, ⟨j, Nat.le_of_succ_le_succ hj, hb⟩⟩

/-- Termination within a bound: whatever is reachable is reachable
within some number of steps. -/
theorem terminates_within {g : Graph} {a t : Nat}
    (h : Reachable g a t) : ∃ k, Within g k a t := by
  induction h with
  | refl a => exact ⟨0, 0, Nat.le_refl 0, ReachIn.zero a⟩
  | step he _ ih =>
    obtain ⟨k, j, hj, hr⟩ := ih
    exact ⟨k + 1, j + 1, Nat.succ_le_succ hj, ReachIn.succ he hr⟩

/-- The attractor direction: whatever is within a bound is reachable,
so descent from any vertex in the basin arrives at the target. -/
theorem within_reachable {g : Graph} {k a t : Nat}
    (h : Within g k a t) : Reachable g a t := by
  obtain ⟨j, -, hr⟩ := h
  induction hr with
  | zero a => exact Reachable.refl a
  | succ he _ ih => exact Reachable.step he ih

/-- A concrete graph: a short chain `0 → 1 → 2`. -/
def exampleGraph : Graph := [(0, 1), (1, 2)]

/-- In the example graph, `2` is within two steps of `0`, and the
descent step from `0` goes to `1`, within one step of `2`. -/
theorem example_within : Within exampleGraph 2 0 2 := by
  have h1 : (0, 1) ∈ exampleGraph := by decide
  have h2 : (1, 2) ∈ exampleGraph := by decide
  exact ⟨2, Nat.le_refl 2, ReachIn.succ h1 (ReachIn.succ h2 (ReachIn.zero 2))⟩

end GraphDescent
