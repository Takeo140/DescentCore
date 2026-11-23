/-
# NewComputer — a blueprint, in code, for a computer that computes by descent

This file is the Lean blueprint of the **NewComputer**, one of the 2026
blueprints named in `DescentCore.lean`: a computer whose computation is
a descent. A computation is loaded as a state carrying a natural-number
energy; the machine steps, the energy strictly falls while it is
positive, and the answer is read off the state the machine comes to
rest on — the attractor. There is no separate halting problem to solve
for such a machine: halting is a property of the design.

This is a blueprint, not a hardware implementation. What is proved
here is that the design carries its guarantees:

* **Termination within a bound.** From any loaded state, the machine
  reaches an energy-zero state within `energy` steps (the descent
  kernel, restated here so the file is self-contained, as elsewhere in
  this repository).
* **The attractor readout.** The state the answer is read from is a
  rest state: the step fixes it, and running the machine further
  changes nothing. Reading the output of a rest state is the state
  itself, unchanged (`compute_of_rest`).
* **A worked design.** The Euclidean machine: a two-register machine
  whose registers hold a pair of natural numbers, whose step is one
  Euclidean step, and whose energy is `a + 2b` off the rest states.
  For this machine the blueprint proves the full specification:
  `compute euclidMachine (a, b) = Nat.gcd a b` — the machine computes
  the greatest common divisor, for all inputs, as a theorem.

Convergence is derived from strict energy descent. No convergence
axiom is assumed. Core Lean only, no Mathlib, no `sorry`.

Author: Takeo Yamamoto
License: Apache-2.0
-/

namespace NewComputer

/-! ## The descent kernel (restated)

The shared kernel of this repository, in the form of `DescentCore.lean`:
a descent system is a state space with an energy into the natural
numbers and a step that strictly lowers positive energy and fixes
zero-energy states. -/

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

/-! ## The machine

A descent machine is the blueprint's unit of design: a way to load an
input as a state, a descent system that computes, and a way to read an
output off a state. To compute is to run the system for `energy` steps
— always enough, by the bound above — and read. -/

/-- A descent machine: `load` an input as a state, let the descent
system `sys` compute, `read` the output off the rest state. -/
structure DescentMachine (State Input Output : Type) where
  load : Input → State
  sys : DescentSystem State
  read : State → Output

/-- The machine's computation: run for `energy (load i)` steps and read
the output off the state reached. -/
def compute {State Input Output : Type} (M : DescentMachine State Input Output)
    (i : Input) : Output :=
  M.read (iter M.sys.step (M.sys.energy (M.load i)) (M.load i))

/-- The state a computation reads its answer from is a rest state. -/
theorem compute_state_rest {State Input Output : Type}
    (M : DescentMachine State Input Output) (i : Input) :
    M.sys.energy (iter M.sys.step (M.sys.energy (M.load i)) (M.load i)) = 0 ∧
    M.sys.step (iter M.sys.step (M.sys.energy (M.load i)) (M.load i))
      = iter M.sys.step (M.sys.energy (M.load i)) (M.load i) :=
  ⟨iter_energy_at_bound M.sys (M.load i),
   M.sys.rest _ (iter_energy_at_bound M.sys (M.load i))⟩

/-- If the loaded state is already at rest, the machine returns its
readout unchanged: the design does no work on a finished input. -/
theorem compute_of_rest {State Input Output : Type}
    (M : DescentMachine State Input Output) (i : Input)
    (h : M.sys.energy (M.load i) = 0) : compute M i = M.read (M.load i) := by
  unfold compute
  rw [h]
  rfl

/-! ## The worked design: the Euclidean machine

Two registers holding `(a, b)`. One step is one Euclidean step:
`(a, b) ↦ (b, a mod b)`, resting when `b = 0`. The energy is `a + 2b`
off the rest states — one Euclidean step strictly lowers it, since
`a mod b` is below `b` and at most `a`, so `b + 2(a mod b) < a + 2b`.
The readout is the first register. -/

/-- One Euclidean step; rest when the second register is zero. -/
def euclidStep : Nat × Nat → Nat × Nat
  | (a, b) => if b = 0 then (a, b) else (b, a % b)

/-- The energy of the Euclidean machine: zero exactly on the rest
states, `a + 2b` elsewhere. -/
def euclidEnergy : Nat × Nat → Nat
  | (a, b) => if b = 0 then 0 else a + 2 * b

/-- The Euclidean machine as a descent system: the design conditions
are proved, not assumed. -/
def euclidSys : DescentSystem (Nat × Nat) where
  energy := euclidEnergy
  step := euclidStep
  dec := by
    intro s hs
    obtain ⟨a, b⟩ := s
    show euclidEnergy (euclidStep (a, b)) < euclidEnergy (a, b)
    by_cases hb : b = 0
    · subst hb
      simp [euclidEnergy] at hs
    · have hE : euclidEnergy (a, b) = a + 2 * b := by simp [euclidEnergy, hb]
      have hstep : euclidStep (a, b) = (b, a % b) := by simp [euclidStep, hb]
      rw [hstep]
      by_cases hm : a % b = 0
      · have h0 : euclidEnergy (b, a % b) = 0 := by simp [euclidEnergy, hm]
        rw [h0, hE]
        have hb' : 0 < b := Nat.pos_of_ne_zero hb
        omega
      · have hE2 : euclidEnergy (b, a % b) = b + 2 * (a % b) := by
          simp [euclidEnergy, hm]
        rw [hE2, hE]
        have h1 : a % b < b := Nat.mod_lt a (Nat.pos_of_ne_zero hb)
        have h2 : a % b ≤ a := Nat.mod_le a b
        omega
  rest := by
    intro s hs
    obtain ⟨a, b⟩ := s
    show euclidStep (a, b) = (a, b)
    have hb : b = 0 := by
      by_cases hb : b = 0
      · exact hb
      · exfalso
        have hE : euclidEnergy (a, b) = a + 2 * b := by simp [euclidEnergy, hb]
        rw [hE] at hs
        have hb' : 0 < b := Nat.pos_of_ne_zero hb
        omega
    subst hb
    simp [euclidStep]

/-- Energy zero means the second register is zero: the machine rests
exactly when the Euclidean algorithm is done. -/
theorem euclidEnergy_eq_zero {s : Nat × Nat} (h : euclidEnergy s = 0) :
    s.2 = 0 := by
  obtain ⟨a, b⟩ := s
  by_cases hb : b = 0
  · exact hb
  · exfalso
    have hE : euclidEnergy (a, b) = a + 2 * b := by simp [euclidEnergy, hb]
    rw [hE] at h
    have hb' : 0 < b := Nat.pos_of_ne_zero hb
    omega

/-- One Euclidean step preserves the gcd of the registers. -/
theorem euclid_gcd_step (s : Nat × Nat) :
    Nat.gcd (euclidStep s).1 (euclidStep s).2 = Nat.gcd s.1 s.2 := by
  obtain ⟨a, b⟩ := s
  by_cases hb : b = 0
  · subst hb
    simp [euclidStep]
  · have hstep : euclidStep (a, b) = (b, a % b) := by simp [euclidStep, hb]
    rw [hstep]
    show Nat.gcd b (a % b) = Nat.gcd a b
    rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec b a, Nat.gcd_comm b a]

/-- So the gcd is invariant along the whole computation. -/
theorem euclid_gcd_iter (n : Nat) (s : Nat × Nat) :
    Nat.gcd (iter euclidStep n s).1 (iter euclidStep n s).2
      = Nat.gcd s.1 s.2 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [iter_succ, ih, euclid_gcd_step]

/-- The Euclidean machine as a descent machine: load is the identity,
readout is the first register. -/
def euclidMachine : DescentMachine (Nat × Nat) (Nat × Nat) Nat where
  load := id
  sys := euclidSys
  read := Prod.fst

/-- The blueprint's specification, proved in full: the Euclidean
machine computes the greatest common divisor of its two registers. -/
theorem euclid_computes_gcd (a b : Nat) :
    compute euclidMachine (a, b) = Nat.gcd a b := by
  have h0 : euclidEnergy (iter euclidStep (euclidEnergy (a, b)) (a, b)) = 0 :=
    iter_energy_at_bound euclidSys (a, b)
  have h2 : (iter euclidStep (euclidEnergy (a, b)) (a, b)).2 = 0 :=
    euclidEnergy_eq_zero h0
  have hg : Nat.gcd (iter euclidStep (euclidEnergy (a, b)) (a, b)).1
      (iter euclidStep (euclidEnergy (a, b)) (a, b)).2 = Nat.gcd a b :=
    euclid_gcd_iter _ _
  rw [h2, Nat.gcd_zero_right] at hg
  show (iter euclidStep (euclidEnergy (a, b)) (a, b)).1 = Nat.gcd a b
  exact hg

/-! ## Examples, by exact computation -/

theorem euclid_example_1 : compute euclidMachine (12, 18) = 6 := by decide
theorem euclid_example_2 : compute euclidMachine (7, 13) = 1 := by decide
set_option maxRecDepth 8192 in
theorem euclid_example_3 : compute euclidMachine (100, 75) = 25 := by decide
theorem euclid_example_4 : compute euclidMachine (0, 9) = 9 := by decide

end NewComputer
