/-
# DescentCore

A verified kernel for descent systems.

A descent system is a set of states carrying a natural-number energy and a
step function, such that the energy strictly decreases at every step while
it is positive, and a state of energy zero never moves.

For any such system, this file proves — as theorems, not axioms:

* **Termination within a bound.** From any state `s`, the orbit reaches an
  energy-zero state within `energy s` steps.
* **The attractor.** The state reached is a rest state: the step fixes it,
  and once the orbit arrives there it stays there forever.

This is the shared pattern underneath the ExtremalMachine line of work and
the 2026 blueprints OSBlueprint, NewComputer, NewAI and YamamotoEvolution:
each of them is a descent system in the sense defined here. DescentCore
states and proves the common kernel once, so the instances do not have to
repeat the argument.

Convergence here is derived from strict energy descent. No convergence
axiom is assumed.

The halving machine at the bottom is a small concrete instance: repeated
halving of a natural number reaches zero within `n` steps.

Author: Takeo Yamamoto
License: Apache-2.0
-/

namespace DescentCore

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

/-- The attractor theorem: from any state, the orbit reaches a rest state,
and a rest state is an attractor — once reached, the orbit stays there. -/
theorem reaches_rest {State : Type} (sys : DescentSystem State) (s : State) :
    ∃ t, (∃ n, iter sys.step n s = t) ∧ sys.energy t = 0 ∧ sys.step t = t ∧
      ∀ m, iter sys.step m t = t := by
  obtain ⟨n, -, hn⟩ := terminates_within sys s
  refine ⟨iter sys.step n s, ⟨n, rfl⟩, hn, sys.rest _ hn, ?_⟩
  intro m
  exact iter_of_rest sys.step (sys.rest _ hn) m

/-- The halving machine: energy is the number itself, a step halves it.
A concrete descent system. -/
def halving : DescentSystem Nat where
  energy := fun n => n
  step := fun n => n / 2
  dec := by
    intro n hn
    have hn' : n ≠ 0 := hn
    show n / 2 < n
    omega
  rest := by
    intro n hn
    have hn' : n = 0 := hn
    show n / 2 = n
    rw [hn']

/-- Repeated halving reaches zero within `n` steps. -/
theorem halving_reaches_zero (n : Nat) :
    ∃ k, k ≤ n ∧ iter halving.step k n = 0 := by
  obtain ⟨k, hk1, hk2⟩ := terminates_within halving n
  exact ⟨k, hk1, hk2⟩

end DescentCore
