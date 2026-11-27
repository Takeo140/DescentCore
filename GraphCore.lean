/-
# GraphCore

A verified core for computation on finite graphs.

A graph here is a finite list of directed edges between natural-number
vertices. On top of that, this file builds the two standard views of a
path and proves that they agree:

* **Reachability** — an inductive predicate: `b` is reachable from `a`
  when a chain of edges leads from `a` to `b`.
* **Paths as data** — a path is a list of vertices whose consecutive
  pairs are edges, with explicit start and end points.

For any graph, this file proves — as theorems, not axioms:

* **Transitivity.** Reachability composes: a chain from `a` to `b`
  followed by a chain from `b` to `c` is a chain from `a` to `c`.
* **The bridge.** `b` is reachable from `a` exactly when a vertex list
  witnesses it: `Reachable g a b ↔ ∃ l, Steps g a b l`.
* **Concatenation.** Paths join end to end, and the joined length is
  the sum of the two lengths minus the shared endpoint.

Everything is proved in core Lean: no Mathlib, no `sorry`. The file is
self-contained; `GraphDescent` and `GraphCompute` restate the small
definitions they need, in the manner of the other cores in this
repository.

Author: Takeo Yamamoto
License: Apache-2.0
-/

namespace GraphCore

/-- A finite graph: a list of directed edges between vertices. -/
abbrev Graph := List (Nat × Nat)

/-- Reachability: `Reachable g a b` holds when a chain of edges in `g`
leads from `a` to `b`. The empty chain reaches every vertex from
itself. -/
inductive Reachable (g : Graph) : Nat → Nat → Prop
  | refl (a : Nat) : Reachable g a a
  | step {a b c : Nat} : (a, b) ∈ g → Reachable g b c → Reachable g a c

/-- Reachability is transitive: a chain from `a` to `b` followed by a
chain from `b` to `c` is a chain from `a` to `c`. -/
theorem Reachable.trans {g : Graph} {a b c : Nat}
    (h₁ : Reachable g a b) (h₂ : Reachable g b c) : Reachable g a c := by
  revert h₂
  induction h₁ with
  | refl _ => intro h₂; exact h₂
  | step he _ ih => intro h₂; exact Reachable.step he (ih h₂)

/-- A path as data: `Steps g a b l` says the vertex list `l` starts at
`a`, ends at `b`, and every consecutive pair of vertices in `l` is an
edge of `g`. -/
inductive Steps (g : Graph) : Nat → Nat → List Nat → Prop
  | one (a : Nat) : Steps g a a [a]
  | cons {a b c : Nat} {l : List Nat} :
      (a, b) ∈ g → Steps g b c l → Steps g a c (a :: l)

/-- Every path list is nonempty. -/
theorem steps_length_pos {g : Graph} {a b : Nat} {l : List Nat}
    (h : Steps g a b l) : 0 < l.length := by
  induction h with
  | one _ => exact Nat.succ_pos 0
  | cons _ _ => rw [List.length_cons]; exact Nat.succ_pos _

/-- From a path as data to reachability: the relational view. -/
theorem reachable_of_steps {g : Graph} {a b : Nat} {l : List Nat}
    (h : Steps g a b l) : Reachable g a b := by
  induction h with
  | one _ => exact Reachable.refl _
  | cons he _ ih => exact Reachable.step he ih

/-- From reachability to a path as data: some vertex list witnesses
every chain of edges. -/
theorem steps_of_reachable {g : Graph} {a b : Nat}
    (h : Reachable g a b) : ∃ l, Steps g a b l := by
  induction h with
  | refl a => exact ⟨[a], Steps.one a⟩
  | step he _ ih =>
    obtain ⟨l, hl⟩ := ih
    exact ⟨_ :: l, Steps.cons he hl⟩

/-- The bridge theorem: the two views of a path coincide. -/
theorem reachable_iff_steps {g : Graph} {a b : Nat} :
    Reachable g a b ↔ ∃ l, Steps g a b l :=
  ⟨steps_of_reachable, fun ⟨_, h⟩ => reachable_of_steps h⟩

/-- Paths concatenate: a path from `a` to `b` and a path from `b` to
`c` join into a path from `a` to `c`, and the joined length is the sum
of the two lengths minus one, for the shared endpoint `b`. -/
theorem steps_append {g : Graph} {a b c : Nat} {l₁ l₂ : List Nat}
    (h₁ : Steps g a b l₁) (h₂ : Steps g b c l₂) :
    ∃ l, Steps g a c l ∧ l.length + 1 = l₁.length + l₂.length := by
  revert h₂
  induction h₁ with
  | one _ =>
    intro h₂
    exact ⟨l₂, h₂, by show l₂.length + 1 = 1 + l₂.length; exact Nat.add_comm _ _⟩
  | cons he _ ih =>
    intro h₂
    obtain ⟨l, hl, hlen⟩ := ih h₂
    refine ⟨_ :: l, Steps.cons he hl, ?_⟩
    simp only [List.length_cons]
    omega

/-- A concrete graph: a short chain `0 → 1 → 2 → 3`. -/
def exampleGraph : Graph := [(0, 1), (1, 2), (2, 3)]

/-- In the example graph, `3` is reachable from `0`. -/
theorem example_reachable : Reachable exampleGraph 0 3 := by
  have h1 : (0, 1) ∈ exampleGraph := by decide
  have h2 : (1, 2) ∈ exampleGraph := by decide
  have h3 : (2, 3) ∈ exampleGraph := by decide
  exact Reachable.step h1 (Reachable.step h2 (Reachable.step h3 (Reachable.refl 3)))

end GraphCore
