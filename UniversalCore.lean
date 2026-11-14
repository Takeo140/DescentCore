/-
# UniversalCore

A universal computational core with a verified termination guarantee,
in Lean 4 (core Lean only — no Mathlib).

The file has three layers.

1. **The descent kernel.** A descent system — states, a natural-number
   energy, and a step that strictly lowers positive energy and fixes
   zero-energy states — always reaches a rest state (an attractor) within
   `energy s` steps, and stays there. Convergence is a theorem, not an
   axiom. (This is the DescentCore kernel, included here so that this
   file is self-contained.)

2. **A universal machine.** A register machine — increment, conditional
   decrement-and-branch, jump, halt — over finitely many instructions and
   unboundedly many registers holding natural numbers. Register machines
   are a standard Turing-complete model of computation.

3. **The guarantee.** Any program of this machine that is equipped with a
   measure decreasing at every step (between non-halting states) is
   *proved* to halt: the machine, instantiated as a descent system,
   reaches a halting state within a bound computed from the measure, and
   never moves again. A verified example (a program that counts a
   register down to zero) closes the file, with its final state proved
   correct, not just halting.

Scope, stated plainly: the termination guarantee and the example's
correctness are proved in this file. The Turing completeness of the
register-machine model is the classical result for this model and is
not re-proved here.

Author: Takeo Yamamoto
License: Apache-2.0
-/

namespace UniversalCore

/-! ## Part 1 — the descent kernel -/

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

/-! ## Part 2 — the universal machine -/

/-- Instructions of the register machine. Registers are indexed by
natural numbers and hold natural numbers. -/
inductive Instr where
  | inc (r : Nat)
  | dec (r tgt : Nat)
  | jmp (tgt : Nat)
  | halt
  deriving DecidableEq, Repr

/-- A machine state: a program counter and a register file. -/
structure MState where
  pc : Nat
  regs : Nat → Nat

/-- The instruction at `pc`. Running off the end of the program halts. -/
def fetch : List Instr → Nat → Instr
  | [], _ => Instr.halt
  | i :: _, 0 => i
  | _ :: t, n + 1 => fetch t n

/-- Update one register by a function of its old value. -/
def upd (regs : Nat → Nat) (r : Nat) (f : Nat → Nat) : Nat → Nat :=
  fun r' => if r' = r then f (regs r') else regs r'

theorem upd_self (regs : Nat → Nat) (r : Nat) (f : Nat → Nat) :
    upd regs r f r = f (regs r) :=
  ite_eq_left rfl

theorem upd_other (regs : Nat → Nat) (r r' : Nat) (f : Nat → Nat)
    (h : r' ≠ r) : upd regs r f r' = regs r' :=
  ite_eq_right h

/-- One step of the machine. A halting state does not change. -/
def step (prog : List Instr) (s : MState) : MState :=
  match fetch prog s.pc with
  | .inc r => { s with pc := s.pc + 1, regs := upd s.regs r (· + 1) }
  | .dec r tgt =>
      if s.regs r = 0 then { s with pc := tgt }
      else { s with pc := s.pc + 1, regs := upd s.regs r (· - 1) }
  | .jmp tgt => { s with pc := tgt }
  | .halt => s

/-- A state is halting when the instruction at its program counter
is `halt`. -/
def halted (prog : List Instr) (s : MState) : Prop :=
  fetch prog s.pc = Instr.halt

theorem step_of_halted (prog : List Instr) (s : MState) (h : halted prog s) :
    step prog s = s := by
  unfold step halted at *
  rw [h]

/-! ## Part 3 — the guarantee -/

/-- The machine, seen as a descent system. The energy is zero exactly on
halting states; elsewhere it is the given measure plus one, so that the
final step *into* a halting state also decreases the energy. Only steps
between two non-halting states need the measure to decrease. -/
def machineSystem (prog : List Instr) (μ : MState → Nat)
    (hdec : ∀ s, ¬ halted prog s → ¬ halted prog (step prog s) →
      μ (step prog s) < μ s) : DescentSystem MState where
  energy := fun s => if fetch prog s.pc = Instr.halt then 0 else μ s + 1
  step := step prog
  dec := by
    intro s hs
    by_cases h1 : fetch prog s.pc = Instr.halt
    · exfalso
      exact hs (ite_eq_left h1)
    · have hne : ¬ halted prog s := h1
      show (if fetch prog (step prog s).pc = Instr.halt then 0 else μ (step prog s) + 1)
          < (if fetch prog s.pc = Instr.halt then 0 else μ s + 1)
      rw [ite_eq_right h1]
      by_cases h2 : fetch prog (step prog s).pc = Instr.halt
      · rw [ite_eq_left h2]
        omega
      · rw [ite_eq_right h2]
        have := hdec s hne h2
        omega
  rest := by
    intro s hs
    by_cases h1 : fetch prog s.pc = Instr.halt
    · exact step_of_halted prog s h1
    · exfalso
      exact absurd hs (by rw [ite_eq_right h1]; omega)

/-- The termination guarantee: if a program has a measure that decreases
at every step between non-halting states, then from any starting state
the machine reaches a halting state within `μ s + 1` steps, and stays
there forever. -/
theorem machine_halts (prog : List Instr) (μ : MState → Nat)
    (hdec : ∀ s, ¬ halted prog s → ¬ halted prog (step prog s) →
      μ (step prog s) < μ s) (s : MState) :
    ∃ t, (∃ n, n ≤ μ s + 1 ∧ iter (step prog) n s = t) ∧ halted prog t ∧
      ∀ m, iter (step prog) m t = t := by
  obtain ⟨n, hn_bound, hn_zero⟩ := terminates_within (machineSystem prog μ hdec) s
  have hn_zero' : (if fetch prog (iter (step prog) n s).pc = Instr.halt
      then 0 else μ (iter (step prog) n s) + 1) = 0 := hn_zero
  have hrest : step prog (iter (step prog) n s) = iter (step prog) n s :=
    (machineSystem prog μ hdec).rest _ hn_zero
  refine ⟨iter (step prog) n s, ⟨n, ?_, rfl⟩, ?_, ?_⟩
  · by_cases h1 : fetch prog s.pc = Instr.halt
    · have he : (machineSystem prog μ hdec).energy s = 0 := ite_eq_left h1
      omega
    · have he : (machineSystem prog μ hdec).energy s = μ s + 1 := ite_eq_right h1
      omega
  · by_cases h1 : fetch prog (iter (step prog) n s).pc = Instr.halt
    · exact h1
    · exfalso
      rw [ite_eq_right h1] at hn_zero'
      omega
  · exact iter_of_rest _ hrest

/-! ## Part 4 — a verified example -/

/-- The example program: count register 0 down to zero, then halt.

* pc 0: if register 0 is zero, jump to the halt at pc 2;
  otherwise decrement it and fall through.
* pc 1: jump back to pc 0.
* pc 2: halt. -/
def progZero : List Instr := [.dec 0 2, .jmp 0, .halt]

/-- The measure for `progZero`: three times register 0, plus a phase
weight (2 at pc 1, 1 elsewhere), so the jump back also decreases it. -/
def μZero (s : MState) : Nat := 3 * s.regs 0 + (if s.pc = 1 then 2 else 1)

theorem fetch_zero_0 : fetch progZero 0 = Instr.dec 0 2 := rfl

theorem fetch_zero_1 : fetch progZero 1 = Instr.jmp 0 := rfl

theorem fetch_zero_2 : fetch progZero 2 = Instr.halt := rfl

theorem fetch_zero_add (m : Nat) : fetch progZero (m + 3) = Instr.halt := rfl

/-- A step of `progZero` at pc 0 is the decrement branch. -/
theorem step_zero_dec (s : MState) (hpc : s.pc = 0) :
    step progZero s = if s.regs 0 = 0 then { s with pc := 2 }
      else { s with pc := s.pc + 1, regs := upd s.regs 0 (· - 1) } := by
  unfold step
  rw [hpc, fetch_zero_0]

/-- A step of `progZero` at pc 1 is the jump back to pc 0. -/
theorem step_one_jmp (s : MState) (hpc : s.pc = 1) :
    step progZero s = { s with pc := 0 } := by
  unfold step
  rw [hpc, fetch_zero_1]

/-- The measure decreases at every step between non-halting states. -/
theorem μZero_dec : ∀ s, ¬ halted progZero s → ¬ halted progZero (step progZero s) →
    μZero (step progZero s) < μZero s := by
  intro s hs hs2
  have hpc : s.pc = 0 ∨ s.pc = 1 := by
    by_cases h0 : s.pc = 0
    · exact Or.inl h0
    · by_cases h1 : s.pc = 1
      · exact Or.inr h1
      · exfalso
        apply hs
        show fetch progZero s.pc = Instr.halt
        by_cases h2 : s.pc = 2
        · rw [h2]
          exact fetch_zero_2
        · have hge : 3 ≤ s.pc := by omega
          have hpc3 : s.pc = (s.pc - 3) + 3 := (Nat.sub_add_cancel hge).symm
          rw [hpc3]
          exact fetch_zero_add _
  rcases hpc with h0 | h1
  · -- pc = 0: the decrement step
    by_cases hr : s.regs 0 = 0
    · exfalso
      apply hs2
      have hstep : step progZero s = { s with pc := 2 } := by
        rw [step_zero_dec s h0, ite_eq_left hr]
      rw [hstep]
      exact fetch_zero_2
    · have hstep : step progZero s
          = { s with pc := s.pc + 1, regs := upd s.regs 0 (· - 1) } := by
        rw [step_zero_dec s h0, ite_eq_right hr]
      have hμstep : μZero (step progZero s) = 3 * (s.regs 0 - 1) + 2 := by
        rw [hstep]
        show 3 * (upd s.regs 0 (· - 1)) 0 + (if s.pc + 1 = 1 then 2 else 1)
          = 3 * (s.regs 0 - 1) + 2
        rw [upd_self, h0]
        rfl
      have hμs : μZero s = 3 * s.regs 0 + 1 := by
        show 3 * s.regs 0 + (if s.pc = 1 then 2 else 1) = 3 * s.regs 0 + 1
        rw [ite_eq_right (by omega : s.pc ≠ 1)]
      omega
  · -- pc = 1: the jump back
    have hstep : step progZero s = { s with pc := 0 } := step_one_jmp s h1
    have hμstep : μZero (step progZero s) = 3 * s.regs 0 + 1 := by
      rw [hstep]
      show 3 * s.regs 0 + (if (0 : Nat) = 1 then 2 else 1) = 3 * s.regs 0 + 1
      rw [ite_eq_right (by decide)]
    have hμs : μZero s = 3 * s.regs 0 + 2 := by
      show 3 * s.regs 0 + (if s.pc = 1 then 2 else 1) = 3 * s.regs 0 + 2
      rw [ite_eq_left h1]
    omega

/-- `progZero` terminates from any starting state, by the general
guarantee applied to its measure. -/
theorem progZero_terminates (s : MState) :
    ∃ t, (∃ n, n ≤ μZero s + 1 ∧ iter (step progZero) n s = t) ∧ halted progZero t ∧
      ∀ m, iter (step progZero) m t = t :=
  machine_halts progZero μZero μZero_dec s

theorem iter_zero {State : Type} (step : State → State) (s : State) :
    iter step 0 s = s :=
  rfl

/-- Two steps consume a pair: from a state at pc 0, two steps of
`iter` reach the second successor state. -/
theorem iter_two {State : Type} (step : State → State) (s : State) :
    iter step 2 s = step (step s) := by
  rw [iter_succ, iter_succ, iter_zero]

/-- Two steps of `progZero` from pc 0 with a positive register 0:
decrement the register and return to pc 0. -/
theorem progZero_pair (s : MState) (hpc : s.pc = 0) (hr : s.regs 0 ≠ 0) :
    iter (step progZero) 2 s = { s with regs := upd s.regs 0 (· - 1) } := by
  obtain ⟨pc, regs⟩ := s
  have hpc' : pc = 0 := hpc
  subst hpc'
  have e1 : step progZero ⟨0, regs⟩
      = { (⟨0, regs⟩ : MState) with pc := 0 + 1, regs := upd regs 0 (· - 1) } := by
    rw [step_zero_dec _ rfl, ite_eq_right hr]
  rw [iter_two, e1]
  have hmid : ({ (⟨0, regs⟩ : MState) with pc := 0 + 1, regs := upd regs 0 (· - 1) }
      : MState) = ⟨1, upd regs 0 (· - 1)⟩ := rfl
  rw [hmid]
  have e2 : step progZero ⟨1, upd regs 0 (· - 1)⟩
      = { (⟨1, upd regs 0 (· - 1)⟩ : MState) with pc := 0 } :=
    step_one_jmp _ rfl
  rw [e2]

/-- Iterating `m + 2` steps is iterating 2 steps and then `m` more. -/
theorem iter_add_two {State : Type} (step : State → State) (m : Nat)
    (s : State) :
    iter step (m + 2) s = iter step m (iter step 2 s) := by
  show iter step (m + 1 + 1) s = iter step m (iter step 2 s)
  rw [iter_succ, iter_succ, iter_two]

/-- The countdown, run in full: from pc 0, `progZero` reaches pc 2 with
register 0 equal to zero — a halting state — in `2 * regs 0 + 1` steps. -/
theorem progZero_countdown (regs : Nat → Nat) :
    ∀ k, regs 0 = k →
      ∃ t, iter (step progZero) (2 * k + 1) ⟨0, regs⟩ = t ∧ t.pc = 2 ∧
        t.regs 0 = 0 ∧ halted progZero t := by
  intro k
  induction k generalizing regs with
  | zero =>
      intro hr
      refine ⟨⟨2, regs⟩, ?_, rfl, hr, fetch_zero_2⟩
      have h1 : iter (step progZero) (2 * 0 + 1) ⟨0, regs⟩
          = step progZero ⟨0, regs⟩ := rfl
      have hbridge : ({ (⟨0, regs⟩ : MState) with pc := 2 } : MState)
          = ⟨2, regs⟩ := rfl
      rw [h1, step_zero_dec _ rfl, ite_eq_left hr, hbridge]
  | succ k ih =>
      intro hr
      have hr' : regs 0 ≠ 0 := by omega
      have hcount : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
      have hpair : iter (step progZero) 2 ⟨0, regs⟩
          = ⟨0, upd regs 0 (· - 1)⟩ := progZero_pair ⟨0, regs⟩ rfl hr'
      rw [hcount, iter_add_two, hpair]
      have hreg : (upd regs 0 (· - 1)) 0 = k := by
        have hupd : (upd regs 0 (· - 1)) 0 = regs 0 - 1 := upd_self regs 0 (· - 1)
        omega
      exact ih _ hreg

/-- The example, closed: from any initial register file, `progZero`
reaches a halting state whose register 0 is zero. -/
theorem progZero_final (regs : Nat → Nat) :
    ∃ t, (∃ n, iter (step progZero) n ⟨0, regs⟩ = t) ∧ halted progZero t ∧
      t.regs 0 = 0 := by
  obtain ⟨t, ht, -, h0, hhalt⟩ := progZero_countdown regs (regs 0) rfl
  exact ⟨t, ⟨2 * regs 0 + 1, ht⟩, hhalt, h0⟩

end UniversalCore
