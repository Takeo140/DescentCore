/-
# QuantumCore — Discrete Quantum Computation for Digital Machines

Quantum computation in a fully discrete, exact form, designed to be used
on digital machines.

The usual state-vector model works over the complex numbers, and a digital
computer can only approximate its amplitudes in floating point. This file
takes the discrete route instead:

* **Amplitudes are exact ring elements with integer components.** An
  amplitude is a quadruple of integers `(u, v, w, z)`, read as
  `(u + v·√2) + i·(w + z·√2)` — an element of the ring `ℤ[√2, i]`. No
  floating point anywhere. The `√2` components are necessary, not
  decorative: the `T` gate multiplies one component of a pair by
  `(1 + i)/√2` and the other by `1`, so a single shared scale can only
  absorb the `√2` denominator if the numerators themselves can carry a
  factor of `√2`. Gaussian integers cannot; `ℤ[√2, i]` can.
* **A state carries a scale.** The actual amplitude of a basis state is
  `A / (√2)^scale`, where `scale` is a natural number stored alongside
  the amplitude list. Every gate of the standard universal set
  `{X, Z, S, T, H, CNOT}` is exact in this representation: `X`, `Z`, `S`
  and `CNOT` are integer operations at the same scale, and `H` and `T`
  are integer operations that raise the scale by one.
* **Circuits are data.** A circuit is a list of instructions, executed by
  a fold. Execution is ordinary integer arithmetic on lists — the model
  runs as-is on a digital computer, and its behaviour is proved here.

For any circuit, this file proves — as theorems, not axioms:

* **Length preservation.** Gates and whole circuits never change the
  length of the amplitude list: a register of `2^n` amplitudes stays a
  register of `2^n` amplitudes.
* **Composition.** Running two circuits in sequence is the same as
  running their concatenation.

And it verifies the standard examples by computation (`decide`), exactly,
with no rounding:

* `H` on `|0⟩` gives `(|0⟩ + |1⟩)/√2`.
* `H` then `CNOT` on `|00⟩` gives the Bell state `(|00⟩ + |11⟩)/√2`,
  whose total weight is `2 = 2^scale`: the state is normalized, and each
  outcome has probability exactly `1/2`.
* `H`, `CNOT`, `CNOT` on `|000⟩` gives the GHZ state.
* `H` twice on `|0⟩` returns to `|0⟩`: the amplitudes are `(2, 0)` at
  scale `2`, and `2/(√2)^2 = 1` — interference, computed in integers.
* `T` on `|1⟩` gives the phase `(1 + i)/√2`, and `T` on the superposition
  `(|0⟩ + |1⟩)/√2` gives `(|0⟩ + e^{iπ/4}|1⟩)/√2`, still normalized —
  the case that forces the `√2` components.

Probabilities are exact in this model: the squared norm of an amplitude
`A` is the `ℤ[√2]` element `|A|² = p + q·√2`, the weight of a state is
the sum of these, and a state is normalized when its weight is exactly
`(2^scale, 0)`. The probability of an outcome is `|A|² / 2^scale`.

Author: Takeo Yamamoto
License: Apache-2.0
-/

namespace QuantumCore

/-- An exact amplitude `(u + v·√2) + i·(w + z·√2)`: an element of the
    ring `ℤ[√2, i]`, stored as four integers. All arithmetic on
    amplitudes is integer arithmetic. -/
structure Ampl where
  u : Int
  v : Int
  w : Int
  z : Int
deriving DecidableEq, Repr

namespace Ampl

def zero : Ampl := ⟨0, 0, 0, 0⟩
def one : Ampl := ⟨1, 0, 0, 0⟩

instance : Inhabited Ampl := ⟨zero⟩

def add (a b : Ampl) : Ampl := ⟨a.u + b.u, a.v + b.v, a.w + b.w, a.z + b.z⟩
def neg (a : Ampl) : Ampl := ⟨-a.u, -a.v, -a.w, -a.z⟩
def sub (a b : Ampl) : Ampl := ⟨a.u - b.u, a.v - b.v, a.w - b.w, a.z - b.z⟩

/-- Multiply by `i`: `i·((u + v√2) + i(w + z√2)) = -(w + z√2) + i(u + v√2)`. -/
def mulI (a : Ampl) : Ampl := ⟨-a.w, -a.z, a.u, a.v⟩

/-- Multiply by `√2`: `√2·(u + v√2) = 2v + u√2`, and likewise for the
    imaginary part. -/
def mulSqrt2 (a : Ampl) : Ampl := ⟨2 * a.v, a.u, 2 * a.z, a.w⟩

/-- Multiply by `1 + i`. -/
def mulOnePlusI (a : Ampl) : Ampl :=
  ⟨a.u - a.w, a.v - a.z, a.w + a.u, a.z + a.v⟩

/-- The squared norm `|A|²` as an element of `ℤ[√2]`, returned as the
    pair `(p, q)` standing for `p + q·√2`:
    `|A|² = (u² + 2v² + w² + 2z²) + 2(uv + wz)·√2`. -/
def absSq (a : Ampl) : Int × Int :=
  (a.u * a.u + 2 * a.v * a.v + a.w * a.w + 2 * a.z * a.z,
   2 * (a.u * a.v + a.w * a.z))

end Ampl

/-- The partner of index `i` at qubit `q`: the index that differs from `i`
    only in bit `q`. -/
def partner (i q : Nat) : Nat :=
  if Nat.testBit i q then i - 2 ^ q else i + 2 ^ q

/-- Apply a one-qubit gate, given as its action on the pair of amplitudes
    `(a, b)` whose indices differ only in bit `q` (`a` at bit `0`, `b` at
    bit `1`), to qubit `q` of a register. -/
def applyGate (g : Ampl → Ampl → Ampl × Ampl) (q : Nat) (amps : List Ampl) :
    List Ampl :=
  (List.range amps.length).map fun i =>
    let p := partner i q
    let a := if Nat.testBit i q then amps[p]! else amps[i]!
    let b := if Nat.testBit i q then amps[i]! else amps[p]!
    if Nat.testBit i q then (g a b).2 else (g a b).1

/-- Apply a CNOT gate with control qubit `c` and target qubit `t`. -/
def applyCNOT (c t : Nat) (amps : List Ampl) : List Ampl :=
  (List.range amps.length).map fun i =>
    if Nat.testBit i c then amps[partner i t]! else amps[i]!

/-- The one-qubit gates as pair operations. `gateH` and `gateT` are the
    unnormalized numerators; the matching `√2` goes into the scale. For
    `gateT` the bit-`0` component is multiplied by `√2` and the bit-`1`
    component by `1 + i`, so that at scale `+1` the pair represents
    `(a, (1 + i)/√2 · b)` exactly. -/
def gateX (a b : Ampl) : Ampl × Ampl := (b, a)
def gateZ (a b : Ampl) : Ampl × Ampl := (a, b.neg)
def gateS (a b : Ampl) : Ampl × Ampl := (a, b.mulI)
def gateH (a b : Ampl) : Ampl × Ampl := (a.add b, a.sub b)
def gateT (a b : Ampl) : Ampl × Ampl := (a.mulSqrt2, b.mulOnePlusI)

/-- A quantum state: a scale and a list of exact amplitudes. The actual
    amplitude of basis state `k` is `amps[k] / (√2)^scale`. -/
structure QState where
  scale : Nat
  amps : List Ampl
deriving DecidableEq, Repr

/-- One circuit instruction. Qubits are numbered from `0`; qubit `0` is
    the least significant bit of the basis index. -/
inductive Instr where
  | X (q : Nat)
  | Z (q : Nat)
  | S (q : Nat)
  | T (q : Nat)
  | H (q : Nat)
  | CNOT (c t : Nat)

/-- One execution step. `H` and `T` raise the scale by one; the other
    gates keep it. -/
def step (s : QState) : Instr → QState
  | .X q => ⟨s.scale, applyGate gateX q s.amps⟩
  | .Z q => ⟨s.scale, applyGate gateZ q s.amps⟩
  | .S q => ⟨s.scale, applyGate gateS q s.amps⟩
  | .T q => ⟨s.scale + 1, applyGate gateT q s.amps⟩
  | .H q => ⟨s.scale + 1, applyGate gateH q s.amps⟩
  | .CNOT c t => ⟨s.scale, applyCNOT c t s.amps⟩

/-- Run a whole circuit: a fold of `step` over the instruction list. -/
def run (s : QState) (circuit : List Instr) : QState :=
  circuit.foldl step s

/-- The basis state `|k⟩` of an `n`-qubit register, at scale `0`. -/
def basis (n k : Nat) : QState :=
  ⟨0, (List.range (2 ^ n)).map (fun i => if i = k then Ampl.one else Ampl.zero)⟩

/-- The total weight of a state: the sum of the squared norms of its
    amplitudes, as an element of `ℤ[√2]` written as a pair `(p, q)` for
    `p + q·√2`. The probability of outcome `k` is
    `absSq amps[k] / 2^scale`. -/
def weight (s : QState) : Int × Int :=
  s.amps.foldl (fun acc a => (acc.1 + (a.absSq).1, acc.2 + (a.absSq).2)) (0, 0)

/-- A state is normalized when its weight is exactly `(2^scale, 0)`,
    i.e. its outcome probabilities sum to exactly `1`. -/
@[reducible]
def normalized (s : QState) : Prop :=
  weight s = ((2 ^ s.scale : Int), 0)

/-! ## Theorems -/

theorem applyGate_length (g : Ampl → Ampl → Ampl × Ampl) (q : Nat)
    (amps : List Ampl) : (applyGate g q amps).length = amps.length := by
  simp [applyGate]

theorem applyCNOT_length (c t : Nat) (amps : List Ampl) :
    (applyCNOT c t amps).length = amps.length := by
  simp [applyCNOT]

theorem step_length (s : QState) (i : Instr) :
    (step s i).amps.length = s.amps.length := by
  cases i <;> simp [step, applyGate_length, applyCNOT_length]

theorem run_length (s : QState) (circuit : List Instr) :
    (run s circuit).amps.length = s.amps.length := by
  induction circuit generalizing s with
  | nil => rfl
  | cons i rest ih =>
      show (run (step s i) rest).amps.length = s.amps.length
      rw [ih, step_length]

theorem run_append (s : QState) (c₁ c₂ : List Instr) :
    run s (c₁ ++ c₂) = run (run s c₁) c₂ := by
  simp [run, List.foldl_append]

/-! ## Verified examples (by exact integer computation) -/

/-- `X` flips `|0⟩` to `|1⟩`. -/
theorem x_flips : run (basis 1 0) [.X 0] = basis 1 1 := by decide

/-- `H` on `|0⟩` gives `(|0⟩ + |1⟩)/√2`: amplitudes `(1, 1)` at scale `1`. -/
theorem h_superposition :
    run (basis 1 0) [.H 0] = ⟨1, [⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]⟩ := by decide

/-- The superposition is normalized: its weight is `(2, 0) = 2^1`. -/
theorem h_normalized : normalized (run (basis 1 0) [.H 0]) := by decide

/-- `H` then `CNOT` on `|00⟩` gives the Bell state
    `(|00⟩ + |11⟩)/√2`: amplitudes `(1, 0, 0, 1)` at scale `1`. -/
theorem bell_state :
    run (basis 2 0) [.H 0, .CNOT 0 1]
      = ⟨1, [⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]⟩ := by
  decide

/-- The Bell state is normalized, and the weight of outcome `|00⟩` is
    `(1, 0)` out of a total weight of `(2, 0)`: probability exactly `1/2`. -/
theorem bell_normalized :
    normalized (run (basis 2 0) [.H 0, .CNOT 0 1]) := by decide

theorem bell_outcome_weight :
    ((run (basis 2 0) [.H 0, .CNOT 0 1]).amps[0]!).absSq = (1, 0) := by decide

/-- `H`, `CNOT`, `CNOT` on `|000⟩` gives the GHZ state
    `(|000⟩ + |111⟩)/√2`. -/
theorem ghz_state :
    run (basis 3 0) [.H 0, .CNOT 0 1, .CNOT 1 2]
      = ⟨1, [⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
             ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]⟩ := by
  decide

/-- Interference: `H` twice on `|0⟩` returns to `|0⟩`. The amplitudes are
    `(2, 0)` at scale `2`, and `2/(√2)^2 = 1`. -/
theorem h_twice :
    run (basis 1 0) [.H 0, .H 0] = ⟨2, [⟨2, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]⟩ := by
  decide

/-- `T` on `|1⟩` gives the phase `(1 + i)/√2`: amplitude `(1, 0, 1, 0)` at
    scale `1`. -/
theorem t_phase :
    run (basis 1 1) [.T 0] = ⟨1, [⟨0, 0, 0, 0⟩, ⟨1, 0, 1, 0⟩]⟩ := by decide

/-- `T` on a superposition: `H` then `T` on `|0⟩` gives
    `(|0⟩ + e^{iπ/4}|1⟩)/√2`. At scale `2` the amplitudes are `√2` and
    `1 + i` — the case that forces the `√2` components of the amplitude
    ring. -/
theorem t_superposition :
    run (basis 1 0) [.H 0, .T 0]
      = ⟨2, [⟨0, 1, 0, 0⟩, ⟨1, 0, 1, 0⟩]⟩ := by decide

/-- And that state is normalized: its weight is `(4, 0) = 2^2`. -/
theorem t_superposition_normalized :
    normalized (run (basis 1 0) [.H 0, .T 0]) := by decide

/-- `S` on `|1⟩` gives the phase `i`: amplitude `(0, 0, 1, 0)` at
    scale `0`. -/
theorem s_phase :
    run (basis 1 1) [.S 0] = ⟨0, [⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩]⟩ := by decide

end QuantumCore
