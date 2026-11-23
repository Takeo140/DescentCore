/-
# NewAI — a blueprint, in code, for a self-improving system

This file is the Lean blueprint of the **NewAI**, one of the 2026
blueprints named in `DescentCore.lean`: an artificial system that
improves itself by descent. Where `RSI.lean` develops a concrete
self-improving system, this file states the **design interface** — what
a builder must supply, and what the design then guarantees.

A blueprint design is a state space with:

* an `improve` operator the system applies to its own state,
* a natural-number `defect` measuring how far a state is from
  self-consistent,
* a `spec` — the builder's own predicate for what a finished,
  self-consistent state must satisfy,

under two design conditions: while the defect is positive, one
self-application of `improve` strictly lowers it; and a defect-zero
state is a fixed point that already satisfies the `spec`.

For any design meeting that interface, this file proves — as theorems,
not axioms:

* **Settling within a bound.** From any state, iterated
  self-improvement reaches a state satisfying the `spec` within
  `defect s` rounds (`settle_spec`).
* **The self-consistent attractor.** The settled state is a fixed
  point of `improve`, and further rounds never move it
  (`settle_fixed`, `settle_stays`).
* **Monotonicity.** Self-improvement never makes the defect worse.
* **Closure under self-acceleration.** The design whose operator is
  the original applied twice is again a design under the same
  interface, with the same defect and spec, and its `n`-round run
  equals the original `2n`-round run (`accelerate`,
  `iter_accelerate`).

The worked design is a self-correcting weight vector: a list of
natural-number weights that repeatedly halves every weight. Its
defect is the total weight; the blueprint proves it settles, and that
the settled vector is all zeros (`weights_settled`).

What the blueprint does not do is say what intelligence is: the
`spec` is the builder's, and the theorems guarantee the settling,
not the meaning. Convergence is derived from strict defect descent.
No convergence axiom is assumed. Core Lean only, no Mathlib,
no `sorry`.

Author: Takeo Yamamoto
License: Apache-2.0
-/

namespace NewAI

/-! ## The descent kernel (restated)

The shared kernel of this repository, in the form of `DescentCore.lean`,
restated so this file is self-contained: a descent system is a state
space with an energy into the natural numbers and a step that strictly
lowers positive energy and fixes zero-energy states. -/

/-- A descent system: states, an energy into the natural numbers, and a
step that strictly lowers positive energy and fixes zero-energy states. -/
structure DescentSystem (State : Type) where
  energy : State → Nat
  step : State → State
  dec : ∀ s, energy s ≠ 0 → energy (step s) < energy s
  rest : ∀ s, energy s = 0 → step s = s

/-- `iter step n s` is the state reached after `n` steps from `s`. -/
def iter {State : Type} (step : State → State) : Nat → State → State
  | 0, s => s
  | n + 1, s => iter step n (step s)

theorem iter_succ {State : Type} (step : State → State) (n : Nat) (s : State) :
    iter step (n + 1) s = iter step n (step s) :=
  rfl

/-- A rest state never moves, however many steps are taken. -/
theorem iter_of_rest {State : Type} (step : State → State) {t : State}
    (h : step t = t) : ∀ n, iter step n t = t
  | 0 => rfl
  | n + 1 => by
      rw [iter_succ, h]
      exact iter_of_rest step h n

/-- Iterations compose: `m + n` steps are `n` steps followed by `m`. -/
theorem iter_add {State : Type} (step : State → State) :
    ∀ (m n : Nat) (s : State), iter step (m + n) s = iter step m (iter step n s) := by
  intro m n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      have h : m + (n + 1) = (m + n) + 1 := by omega
      rw [h, iter_succ, ih, iter_succ]

/-- Fuel induction: if the energy of `s` is at most `k`, the orbit of `s`
reaches an energy-zero state within `energy s` steps. -/
theorem reaches_zero_aux {State : Type} (sys : DescentSystem State) :
    ∀ k s, sys.energy s ≤ k →
      ∃ n, n ≤ sys.energy s ∧ sys.energy (iter sys.step n s) = 0 := by
  intro k
  induction k with
  | zero =>
      intro s hs
      have h0 : sys.energy s = 0 := Nat.eq_zero_of_le_zero hs
      exact ⟨0, Nat.zero_le _, h0⟩
  | succ k ih =>
      intro s hs
      by_cases h0 : sys.energy s = 0
      · exact ⟨0, Nat.zero_le _, h0⟩
      · have hdec : sys.energy (sys.step s) < sys.energy s := sys.dec s h0
        have hle : sys.energy (sys.step s) ≤ k := by omega
        obtain ⟨n, hn1, hn2⟩ := ih (sys.step s) hle
        refine ⟨n + 1, by omega, ?_⟩
        rw [iter_succ]
        exact hn2

/-- Termination with an explicit bound: from any state, the orbit reaches
an energy-zero state within `energy s` steps. -/
theorem terminates_within {State : Type} (sys : DescentSystem State) (s : State) :
    ∃ n, n ≤ sys.energy s ∧ sys.energy (iter sys.step n s) = 0 :=
  reaches_zero_aux sys (sys.energy s) s (Nat.le_refl _)

/-- Running for exactly `energy s` steps lands on an energy-zero state:
the orbit arrives within the bound and then stays at rest. -/
theorem iter_energy_at_bound {State : Type} (sys : DescentSystem State) (s : State) :
    sys.energy (iter sys.step (sys.energy s) s) = 0 := by
  obtain ⟨n, hn_le, hn0⟩ := terminates_within sys s
  have hsplit : sys.energy s = (sys.energy s - n) + n := by omega
  rw [hsplit, iter_add, iter_of_rest sys.step (sys.rest _ hn0)]
  exact hn0

/-! ## The design interface

A `BlueprintAI` is the blueprint's unit of design: the three things a
builder supplies, and the two conditions the design must meet. Every
guarantee below is inherited by any structure meeting this interface. -/

/-- A self-improving design: an `improve` operator applied to the
system's own state, a `defect` into the natural numbers, and the
builder's `spec` for a finished state — under the design conditions
that `improve` strictly lowers a positive defect, fixes defect-zero
states, and that defect-zero states satisfy the `spec`. -/
structure BlueprintAI (S : Type) where
  improve : S → S
  defect : S → Nat
  spec : S → Prop
  progress : ∀ s, defect s ≠ 0 → defect (improve s) < defect s
  consistent : ∀ s, defect s = 0 → improve s = s
  spec_of_zero : ∀ s, defect s = 0 → spec s

/-- A design is a descent system with energy `defect` and step
`improve`: the blueprint stands on the kernel. -/
def BlueprintAI.toSystem {S : Type} (A : BlueprintAI S) : DescentSystem S where
  energy := A.defect
  step := A.improve
  dec := A.progress
  rest := A.consistent

/-- The settled state from `s`: run self-improvement for `defect s`
rounds — always enough, by the bound. -/
def settle {S : Type} (A : BlueprintAI S) (s : S) : S :=
  iter A.improve (A.defect s) s

/-- Settling reaches the spec: from any state, the settled state
satisfies the builder's specification. -/
theorem settle_spec {S : Type} (A : BlueprintAI S) (s : S) :
    A.spec (settle A s) :=
  A.spec_of_zero _ (iter_energy_at_bound A.toSystem s)

/-- The settled state is a fixed point: the system no longer rewrites
itself. -/
theorem settle_fixed {S : Type} (A : BlueprintAI S) (s : S) :
    A.improve (settle A s) = settle A s :=
  A.consistent _ (iter_energy_at_bound A.toSystem s)

/-- And it stays: further rounds of self-improvement never move a
settled state. -/
theorem settle_stays {S : Type} (A : BlueprintAI S) (s : S) :
    ∀ m, iter A.improve m (settle A s) = settle A s :=
  iter_of_rest _ (settle_fixed A s)

/-- One round of self-improvement never increases the defect. -/
theorem defect_improve_le {S : Type} (A : BlueprintAI S) (s : S) :
    A.defect (A.improve s) ≤ A.defect s := by
  by_cases h0 : A.defect s = 0
  · rw [A.consistent s h0]
    exact Nat.le_refl _
  · exact Nat.le_of_lt (A.progress s h0)

/-- Self-acceleration, at the level of the design: applying the
operator twice per round is again a design under the same interface,
with the same defect and the same spec. -/
def accelerate {S : Type} (A : BlueprintAI S) : BlueprintAI S where
  improve := fun s => A.improve (A.improve s)
  defect := A.defect
  spec := A.spec
  progress := by
    intro s hs
    show A.defect (A.improve (A.improve s)) < A.defect s
    by_cases h1 : A.defect (A.improve s) = 0
    · have h2 : A.improve (A.improve s) = A.improve s := A.consistent _ h1
      rw [h2, h1]
      exact Nat.pos_of_ne_zero hs
    · have g1 : A.defect (A.improve (A.improve s)) < A.defect (A.improve s) :=
        A.progress _ h1
      have g2 : A.defect (A.improve s) < A.defect s := A.progress _ hs
      omega
  consistent := by
    intro s hs
    show A.improve (A.improve s) = s
    have h1 : A.improve s = s := A.consistent s hs
    rw [h1]
    exact h1
  spec_of_zero := A.spec_of_zero

/-- The accelerated design's `n`-round run is the original design's
`2n`-round run. -/
theorem iter_accelerate {S : Type} (A : BlueprintAI S) (n : Nat) (s : S) :
    iter (accelerate A).improve n s = iter A.improve (2 * n) s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      show iter (accelerate A).improve n ((accelerate A).improve s)
          = iter A.improve (2 * (n + 1)) s
      have happ : (accelerate A).improve s = A.improve (A.improve s) := rfl
      have h2 : iter A.improve 2 s = A.improve (A.improve s) := rfl
      have h : 2 * (n + 1) = 2 * n + 2 := by omega
      rw [happ, ih, h, iter_add, h2]

/-! ## The worked design: a self-correcting weight vector

The state is a list of natural-number weights; one round of
self-improvement halves every weight; the defect is the total weight;
the spec is a total weight of zero. The design conditions are proved
below, not assumed. -/

theorem sum_map_halve_le (l : List Nat) :
    (l.map (fun w => w / 2)).sum ≤ l.sum := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons w l ih =>
      show w / 2 + (l.map (fun w => w / 2)).sum ≤ w + l.sum
      have h1 : w / 2 ≤ w := by omega
      omega

theorem sum_map_halve_lt : ∀ (l : List Nat), l.sum ≠ 0 →
    (l.map (fun w => w / 2)).sum < l.sum := by
  intro l
  induction l with
  | nil => intro h; exact (h rfl).elim
  | cons w l ih =>
      intro h
      rw [List.sum_cons] at h
      by_cases hw : w = 0
      · subst hw
        have hl : l.sum ≠ 0 := by
          by_cases hl : l.sum = 0
          · exfalso
            apply h
            omega
          · exact hl
        show (0 / 2 + (l.map (fun w => w / 2)).sum) < (0 + l.sum)
        rw [Nat.zero_div, Nat.zero_add, Nat.zero_add]
        exact ih hl
      · have hw' : 0 < w := Nat.pos_of_ne_zero hw
        have h1 : w / 2 < w := by omega
        have h2 : (l.map (fun w => w / 2)).sum ≤ l.sum := sum_map_halve_le l
        show w / 2 + (l.map (fun w => w / 2)).sum < w + l.sum
        omega

theorem map_halve_of_sum_zero : ∀ (l : List Nat), l.sum = 0 →
    l.map (fun w => w / 2) = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons w l ih =>
      intro h
      rw [List.sum_cons] at h
      have hw : w = 0 := by omega
      have hl : l.sum = 0 := by omega
      show (w / 2) :: (l.map (fun w => w / 2)) = w :: l
      rw [hw, Nat.zero_div, ih hl]

theorem sum_eq_zero_all : ∀ (l : List Nat), l.sum = 0 → ∀ w ∈ l, w = 0 := by
  intro l
  induction l with
  | nil => intro _ w hw; simp at hw
  | cons a l ih =>
      intro h w hw
      rw [List.sum_cons] at h
      have ha : a = 0 := by omega
      have hl : l.sum = 0 := by omega
      have hw2 : w = a ∨ w ∈ l := List.mem_cons.mp hw
      cases hw2 with
      | inl hwa => rw [hwa]; exact ha
      | inr hwl => exact ih hl w hwl

/-- The weight-vector design, as a `BlueprintAI`. -/
def weightsAI : BlueprintAI (List Nat) where
  improve := fun l => l.map (fun w => w / 2)
  defect := fun l => l.sum
  spec := fun l => l.sum = 0
  progress := by
    intro l hl
    exact sum_map_halve_lt l hl
  consistent := by
    intro l hl
    exact map_halve_of_sum_zero l hl
  spec_of_zero := by
    intro l hl
    exact hl

/-- The settled weight vector is all zeros: self-correction runs to
completion, in the strong sense that no weight remains. -/
theorem weights_settled (l : List Nat) : ∀ w ∈ settle weightsAI l, w = 0 := by
  have h0 : (settle weightsAI l).sum = 0 :=
    iter_energy_at_bound weightsAI.toSystem l
  exact sum_eq_zero_all _ h0

/-! ## Examples, by exact computation -/

theorem weights_example : settle weightsAI [3, 5, 8] = [0, 0, 0] := by decide

theorem weights_example_2 : settle weightsAI [7, 1] = [0, 0] := by decide

end NewAI
