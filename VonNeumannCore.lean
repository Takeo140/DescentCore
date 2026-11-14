/-
# VonNeumannCore

The stored-program form of the universal core, in Lean 4 (core Lean
only — no Mathlib).

Parts 1–4 are the UniversalCore: a descent kernel whose convergence is
a theorem rather than an axiom; a universal register machine; a proved
termination guarantee for programs equipped with a decreasing measure;
and a verified example program.

Part 5 adds the von Neumann step: **the program as data**. Instructions
are encoded into a memory (three cells per instruction: opcode and two
arguments), and a single fetch–decode–execute interpreter runs whatever
program the memory holds. The encoding is proved faithful
(`decode_encode`, `encodeMem_encodes`); the interpreter is proved to
simulate the direct machine step for step (`vsim`, `vsim_iter`); and
the termination guarantee is proved to transfer to the interpreted
execution (`interpreter_halts`). The example program is then run *from
memory* to its proved final state (`progZero_interpreted`).

Scope, stated plainly: the simulation and the transfer are proved here.
The interpreter is the machine's fetch–decode–execute cycle reading its
program from memory; an interpreter written as a program in the
machine's own instruction set (full self-interpretation), and von
Neumann's universal constructor with self-reproduction, remain above
this file.

Author: Takeo Yamamoto
License: Apache-2.0
-/


namespace VonNeumannCore

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

/-! ## Part 5 — the von Neumann step: the program as data -/

/-- The opcode of an instruction, as stored in memory. -/
def tag : Instr → Nat
  | .inc _ => 0
  | .dec _ _ => 1
  | .jmp _ => 2
  | .halt => 3

/-- The first argument of an instruction, as stored in memory. -/
def arg1 : Instr → Nat
  | .inc r => r
  | .dec r _ => r
  | .jmp t => t
  | .halt => 0

/-- The second argument of an instruction, as stored in memory. -/
def arg2 : Instr → Nat
  | .inc _ => 0
  | .dec _ t => t
  | .jmp _ => 0
  | .halt => 0

/-- Decode one instruction from its three memory cells. Any opcode
other than 0, 1 or 2 decodes to `halt`. -/
def decode (op a1 a2 : Nat) : Instr :=
  match op with
  | 0 => .inc a1
  | 1 => .dec a1 a2
  | 2 => .jmp a1
  | _ => .halt

/-- Decoding is the inverse of encoding, for every instruction. -/
theorem decode_encode (x : Instr) : decode (tag x) (arg1 x) (arg2 x) = x := by
  cases x <;> rfl

/-- A memory encodes a program when the three cells of every
instruction decode back to that instruction. Instruction `i` lives in
cells `3 * i` (opcode), `3 * i + 1` and `3 * i + 2` (arguments). -/
def Encodes (mem : Nat → Nat) (prog : List Instr) : Prop :=
  ∀ i, i < prog.length →
    decode (mem (3 * i)) (mem (3 * i + 1)) (mem (3 * i + 2)) = fetch prog i

/-- The canonical memory holding a program: cell `a` holds the opcode
or an argument of instruction `a / 3`, according to `a % 3`. -/
def encodeMem (prog : List Instr) : Nat → Nat := fun a =>
  if a % 3 = 0 then tag (fetch prog (a / 3))
  else if a % 3 = 1 then arg1 (fetch prog (a / 3))
  else arg2 (fetch prog (a / 3))

/-- The canonical memory does encode the program. -/
theorem encodeMem_encodes (prog : List Instr) : Encodes (encodeMem prog) prog := by
  intro i _
  have h0 : (encodeMem prog) (3 * i) = tag (fetch prog i) := by
    have hm : (3 * i) % 3 = 0 := by omega
    have hd : (3 * i) / 3 = i := by omega
    unfold encodeMem
    rw [hm, hd]
    exact ite_eq_left rfl
  have h1 : (encodeMem prog) (3 * i + 1) = arg1 (fetch prog i) := by
    have hm : (3 * i + 1) % 3 = 1 := by omega
    have hd : (3 * i + 1) / 3 = i := by omega
    unfold encodeMem
    rw [hm, hd, ite_eq_right (by decide : ¬ (1 : Nat) = 0), ite_eq_left rfl]
  have h2 : (encodeMem prog) (3 * i + 2) = arg2 (fetch prog i) := by
    have hm : (3 * i + 2) % 3 = 2 := by omega
    have hd : (3 * i + 2) / 3 = i := by omega
    unfold encodeMem
    rw [hm, hd, ite_eq_right (by decide : ¬ (2 : Nat) = 0),
      ite_eq_right (by decide : ¬ (2 : Nat) = 1)]
  rw [h0, h1, h2]
  exact decode_encode _

/-- Beyond the end of the program, `fetch` halts. -/
theorem fetch_beyond (prog : List Instr) (n : Nat) (h : prog.length ≤ n) :
    fetch prog n = Instr.halt := by
  induction prog generalizing n with
  | nil => rfl
  | cons i t ih =>
      cases n with
      | zero =>
          have hl : (i :: t).length = t.length + 1 := rfl
          omega
      | succ m =>
          exact ih m (by
            have hl : (i :: t).length = t.length + 1 := rfl
            omega)

/-- The interpreter's state: a program counter, a register file, and
the memory that holds the program as data. -/
structure VState where
  pc : Nat
  regs : Nat → Nat
  mem : Nat → Nat

/-- One fetch–decode–execute cycle of the stored-program interpreter.
The instruction is read from the memory at the program counter and
decoded; a program counter outside the stored program, or a decoded
`halt`, leaves the state unchanged. The memory itself is never
written. -/
def vstep (len : Nat) (s : VState) : VState :=
  if s.pc < len then
    match decode (s.mem (3 * s.pc)) (s.mem (3 * s.pc + 1)) (s.mem (3 * s.pc + 2)) with
    | .inc r => { s with pc := s.pc + 1, regs := upd s.regs r (· + 1) }
    | .dec r tgt =>
        if s.regs r = 0 then { s with pc := tgt }
        else { s with pc := s.pc + 1, regs := upd s.regs r (· - 1) }
    | .jmp tgt => { s with pc := tgt }
    | .halt => s
  else s

/-- The simulation theorem, one step: if the memory encodes the
program, then one interpreter cycle from a state corresponding to `s`
lands on the state corresponding to one direct step of `s` — same
program counter, same registers, memory untouched. -/
theorem vsim (prog : List Instr) (mem : Nat → Nat) (henc : Encodes mem prog)
    (v : VState) (s : MState)
    (hpc : v.pc = s.pc) (hregs : v.regs = s.regs) (hmem : v.mem = mem) :
    (vstep prog.length v).pc = (step prog s).pc ∧
    (vstep prog.length v).regs = (step prog s).regs ∧
    (vstep prog.length v).mem = mem := by
  obtain ⟨vpc, vregs, vmem⟩ := v
  obtain ⟨spc, sregs⟩ := s
  dsimp only at hpc hregs hmem
  subst hpc
  subst hregs
  subst hmem
  by_cases hlt : vpc < prog.length
  · have hdec : decode (vmem (3 * vpc)) (vmem (3 * vpc + 1)) (vmem (3 * vpc + 2))
        = fetch prog vpc := henc vpc hlt
    unfold vstep step
    rw [ite_eq_left hlt, hdec]
    cases hfetch : fetch prog vpc with
    | inc r => exact ⟨rfl, rfl, rfl⟩
    | dec r tgt =>
        dsimp only
        by_cases hr : vregs r = 0
        · rw [ite_eq_left hr, ite_eq_left hr]
          exact ⟨rfl, rfl, rfl⟩
        · rw [ite_eq_right hr, ite_eq_right hr]
          exact ⟨rfl, rfl, rfl⟩
    | jmp tgt => exact ⟨rfl, rfl, rfl⟩
    | halt => exact ⟨rfl, rfl, rfl⟩
  · have hfetch : fetch prog vpc = Instr.halt :=
      fetch_beyond prog vpc (by omega)
    unfold vstep step
    rw [ite_eq_right hlt, hfetch]
    exact ⟨rfl, rfl, rfl⟩

/-- The simulation theorem, iterated: at every step count, the
interpreted execution and the direct execution agree on the program
counter and the registers, and the memory is untouched. -/
theorem vsim_iter (prog : List Instr) (mem : Nat → Nat) (henc : Encodes mem prog)
    (v : VState) (s : MState)
    (hpc : v.pc = s.pc) (hregs : v.regs = s.regs) (hmem : v.mem = mem) :
    ∀ n,
    (iter (vstep prog.length) n v).pc = (iter (step prog) n s).pc ∧
    (iter (vstep prog.length) n v).regs = (iter (step prog) n s).regs ∧
    (iter (vstep prog.length) n v).mem = mem := by
  intro n
  induction n generalizing v s with
  | zero => exact ⟨hpc, hregs, hmem⟩
  | succ n ih =>
      rw [iter_succ, iter_succ]
      obtain ⟨h1, h2, h3⟩ := vsim prog mem henc v s hpc hregs hmem
      exact ih (vstep prog.length v) (step prog s) h1 h2 h3

/-- An interpreter state that has halted — program counter outside the
program, or a decoded `halt` — never moves. -/
theorem vstep_of_halted (prog : List Instr) (w : VState)
    (hhalt : ¬ w.pc < prog.length ∨
      decode (w.mem (3 * w.pc)) (w.mem (3 * w.pc + 1)) (w.mem (3 * w.pc + 2))
        = Instr.halt) :
    vstep prog.length w = w := by
  unfold vstep
  rcases hhalt with h | h
  · rw [ite_eq_right h]
  · by_cases hlt : w.pc < prog.length
    · rw [ite_eq_left hlt, h]
    · rw [ite_eq_right hlt]

/-- The termination guarantee transfers to the interpreter: if a
program has a decreasing measure, then the stored-program execution of
that program from memory reaches, within the same bound, a state the
interpreter cannot leave — program counter outside the program, or a
decoded `halt`. -/
theorem interpreter_halts (prog : List Instr) (mem : Nat → Nat)
    (henc : Encodes mem prog) (μ : MState → Nat)
    (hdec : ∀ s, ¬ halted prog s → ¬ halted prog (step prog s) →
      μ (step prog s) < μ s) (s : MState) :
    ∃ v, (∃ n, n ≤ μ s + 1 ∧ iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩ = v) ∧
      (¬ v.pc < prog.length ∨
        decode (v.mem (3 * v.pc)) (v.mem (3 * v.pc + 1)) (v.mem (3 * v.pc + 2))
          = Instr.halt) ∧
      ∀ m, iter (vstep prog.length) m v = v := by
  obtain ⟨t, ⟨n, hn, ht⟩, hhalt, -⟩ := machine_halts prog μ hdec s
  obtain ⟨hpc_eq, hregs_eq, hmem_eq⟩ :=
    vsim_iter prog mem henc ⟨s.pc, s.regs, mem⟩ s rfl rfl rfl n
  rw [ht] at hpc_eq hregs_eq
  have hdv : ∀ (hlt : (iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩).pc
        < prog.length),
      decode ((iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩).mem
          (3 * (iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩).pc))
        ((iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩).mem
          (3 * (iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩).pc + 1))
        ((iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩).mem
          (3 * (iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩).pc + 2))
        = Instr.halt := by
    intro hlt
    have hdec2 : decode (mem (3 * (iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩).pc))
        (mem (3 * (iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩).pc + 1))
        (mem (3 * (iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩).pc + 2))
        = fetch prog (iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩).pc :=
      henc _ hlt
    rw [hmem_eq, hdec2, hpc_eq]
    exact hhalt
  have hhaltv : ¬ (iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩).pc < prog.length ∨
      decode ((iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩).mem
          (3 * (iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩).pc))
        ((iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩).mem
          (3 * (iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩).pc + 1))
        ((iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩).mem
          (3 * (iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩).pc + 2))
        = Instr.halt := by
    by_cases hlt : (iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩).pc < prog.length
    · exact Or.inr (hdv hlt)
    · exact Or.inl hlt
  refine ⟨iter (vstep prog.length) n ⟨s.pc, s.regs, mem⟩, ⟨n, hn, rfl⟩, hhaltv, ?_⟩
  exact iter_of_rest _ (vstep_of_halted prog _ hhaltv)

/-- The example, run from memory: the interpreter, executing the
encoded `progZero` out of its memory, reaches program counter 2 with
register 0 equal to zero — the same proved final state as the direct
execution — with the memory untouched. -/
theorem progZero_interpreted (regs : Nat → Nat) :
    ∃ v, iter (vstep progZero.length) (2 * regs 0 + 1)
        ⟨0, regs, encodeMem progZero⟩ = v ∧
      v.pc = 2 ∧ v.regs 0 = 0 ∧ v.mem = encodeMem progZero := by
  obtain ⟨h1, h2, h3⟩ := vsim_iter progZero (encodeMem progZero) (encodeMem_encodes progZero)
    ⟨0, regs, encodeMem progZero⟩ ⟨0, regs⟩ rfl rfl rfl (2 * regs 0 + 1)
  obtain ⟨t, ht, hpc_t, h0_t, -⟩ := progZero_countdown regs (regs 0) rfl
  refine ⟨iter (vstep progZero.length) (2 * regs 0 + 1) ⟨0, regs, encodeMem progZero⟩,
    rfl, ?_, ?_, h3⟩
  · rw [h1, ht]
    exact hpc_t
  · rw [h2, ht]
    exact h0_t

end VonNeumannCore
