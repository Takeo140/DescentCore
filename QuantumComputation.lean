/-
# QuantumComputation — Pure Discrete Quantum Computation (Core Lean Only)

Direct implementation of discrete quantum computation itself over `ℤ[√2, i]`
with denominator `(√2)^scale`, using integer arithmetic with zero
floating-point rounding.

Covers the core mechanics of quantum computation:
* Exact amplitudes in `ℤ[√2, i]` and squared norm in `ℤ[√2]`.
* Quantum state (`QState`), basis states (`|0⟩`, `|1⟩`, `|k⟩`), and
  single/multi-qubit gate evolution (`X`, `Z`, `S`, `T`, `H`, `CNOT`).
* Superposition, relative/global phase, interference, entanglement, and
  measurement (`measureWeight`, `project`).

Core Lean only, no Mathlib, no `sorry`.

Author: Takeo Yamamoto
License: Apache-2.0
-/

namespace QuantumComputation

/-- Exact amplitude `(u + v·√2) + i·(w + z·√2)` in `ℤ[√2, i]`. -/
structure Ampl where
  u : Int
  v : Int
  w : Int
  z : Int
deriving DecidableEq, Repr

/-- Element `p + q·√2` of `ℤ[√2]`. -/
abbrev ZSqrt2 := Int × Int

namespace ZSqrt2

def zero : ZSqrt2 := (0, 0)
def add (x y : ZSqrt2) : ZSqrt2 := (x.1 + y.1, x.2 + y.2)
def pow2 (k : Nat) : ZSqrt2 := ((2 ^ k : Nat : Int), 0)

end ZSqrt2

namespace Ampl

def zero : Ampl := ⟨0, 0, 0, 0⟩
def one : Ampl := ⟨1, 0, 0, 0⟩

instance : Inhabited Ampl := ⟨zero⟩
instance : Zero Ampl := ⟨zero⟩
instance : One Ampl := ⟨one⟩

def add (a b : Ampl) : Ampl := ⟨a.u + b.u, a.v + b.v, a.w + b.w, a.z + b.z⟩
def neg (a : Ampl) : Ampl := ⟨-a.u, -a.v, -a.w, -a.z⟩
def sub (a b : Ampl) : Ampl := ⟨a.u - b.u, a.v - b.v, a.w - b.w, a.z - b.z⟩
def mulI (a : Ampl) : Ampl := ⟨-a.w, -a.z, a.u, a.v⟩
def mulSqrt2 (a : Ampl) : Ampl := ⟨2 * a.v, a.u, 2 * a.z, a.w⟩
def mulOnePlusI (a : Ampl) : Ampl :=
  ⟨a.u - a.w, a.v - a.z, a.w + a.u, a.z + a.v⟩

/-- Squared norm `|A|² = (u² + 2v² + w² + 2z²) + 2(uv + wz)·√2` in `ℤ[√2]`. -/
def absSq (a : Ampl) : ZSqrt2 :=
  (a.u * a.u + 2 * a.v * a.v + a.w * a.w + 2 * a.z * a.z,
   2 * (a.u * a.v + a.w * a.z))

instance : Add Ampl := ⟨add⟩
instance : Neg Ampl := ⟨neg⟩
instance : Sub Ampl := ⟨sub⟩

end Ampl

/-- Flip bit `q` of basis index `i`. -/
def partner (i q : Nat) : Nat :=
  if Nat.testBit i q then i - 2 ^ q else i + 2 ^ q

/-- Apply a 1-qubit gate `(a, b) ↦ g a b` to qubit `q`. -/
def applyGate (g : Ampl → Ampl → Ampl × Ampl) (q : Nat) (amps : List Ampl) :
    List Ampl :=
  (List.range amps.length).map fun i =>
    let p := partner i q
    let a := if Nat.testBit i q then amps[p]! else amps[i]!
    let b := if Nat.testBit i q then amps[i]! else amps[p]!
    if Nat.testBit i q then (g a b).2 else (g a b).1

/-- Apply `CNOT` with control qubit `c` and target qubit `t`. -/
def applyCNOT (c t : Nat) (amps : List Ampl) : List Ampl :=
  (List.range amps.length).map fun i =>
    if Nat.testBit i c then amps[partner i t]! else amps[i]!

def gateX (a b : Ampl) : Ampl × Ampl := (b, a)
def gateZ (a b : Ampl) : Ampl × Ampl := (a, b.neg)
def gateS (a b : Ampl) : Ampl × Ampl := (a, b.mulI)
def gateH (a b : Ampl) : Ampl × Ampl := (a.add b, a.sub b)
def gateT (a b : Ampl) : Ampl × Ampl := (a.mulSqrt2, b.mulOnePlusI)

/-- Quantum state: denominator scale `(√2)^scale` and amplitude list. -/
structure QState where
  scale : Nat
  amps : List Ampl
deriving DecidableEq, Repr

/-- Basic quantum gates. -/
inductive Gate where
  | X (q : Nat)
  | Z (q : Nat)
  | S (q : Nat)
  | T (q : Nat)
  | H (q : Nat)
  | CNOT (c t : Nat)
deriving DecidableEq, Repr

/-- Single quantum gate step. -/
def applyStep (s : QState) : Gate → QState
  | .X q => ⟨s.scale, applyGate gateX q s.amps⟩
  | .Z q => ⟨s.scale, applyGate gateZ q s.amps⟩
  | .S q => ⟨s.scale, applyGate gateS q s.amps⟩
  | .T q => ⟨s.scale + 1, applyGate gateT q s.amps⟩
  | .H q => ⟨s.scale + 1, applyGate gateH q s.amps⟩
  | .CNOT c t => ⟨s.scale, applyCNOT c t s.amps⟩

/-- Sequential quantum computation over a list of gates. -/
def evolve (s : QState) (gates : List Gate) : QState :=
  gates.foldl applyStep s

/-- Computational basis state `|k⟩` on `n` qubits. -/
def ket (n k : Nat) : QState :=
  ⟨0, (List.range (2 ^ n)).map (fun i => if i = k then Ampl.one else Ampl.zero)⟩

/-- Total squared-norm weight `Σ |A_k|²` in `ℤ[√2]`. -/
def weight (s : QState) : ZSqrt2 :=
  s.amps.foldl (fun acc a => ZSqrt2.add acc a.absSq) ZSqrt2.zero

@[reducible]
def normalized (s : QState) : Prop :=
  weight s = ZSqrt2.pow2 s.scale

/-- Measurement weight for qubit `q` yielding `outcome` (`false` = `0`, `true` = `1`). -/
def measureWeight (s : QState) (q : Nat) (outcome : Bool) : ZSqrt2 :=
  ((List.range s.amps.length).filter (fun i => decide (Nat.testBit i q = outcome))).foldl
    (fun acc i => ZSqrt2.add acc (s.amps[i]!).absSq) ZSqrt2.zero

/-- State projection onto qubit `q` having value `outcome`. -/
def project (s : QState) (q : Nat) (outcome : Bool) : QState :=
  ⟨s.scale,
    (List.range s.amps.length).map fun i =>
      if Nat.testBit i q = outcome then s.amps[i]! else Ampl.zero⟩

/-! ## Core Properties & Exact Checks -/

theorem evolve_length (s : QState) (gates : List Gate) :
    (evolve s gates).amps.length = s.amps.length := by
  induction gates generalizing s with
  | nil => rfl
  | cons g rest ih =>
      show (evolve (applyStep s g) rest).amps.length = s.amps.length
      rw [ih]
      cases g <;> simp [applyStep, applyGate, applyCNOT]

theorem evolve_append (s : QState) (g₁ g₂ : List Gate) :
    evolve s (g₁ ++ g₂) = evolve (evolve s g₁) g₂ := by
  simp [evolve, List.foldl_append]

/-- Superposition: `H|0⟩ = (|0⟩ + |1⟩) / √2`. -/
theorem superposition_check :
    evolve (ket 1 0) [.H 0] = ⟨1, [⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]⟩ := by decide

/-- Interference: `H(H|0⟩)` cancels the `|1⟩` component and returns to `|0⟩` (up to scale `2`). -/
theorem interference_check :
    evolve (ket 1 0) [.H 0, .H 0] = ⟨2, [⟨2, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]⟩ := by decide

/-- Entanglement: `CNOT(H|0⟩ ⊗ |0⟩)` produces the Bell state `(|00⟩ + |11⟩) / √2`. -/
theorem entanglement_check :
    evolve (ket 2 0) [.H 0, .CNOT 0 1]
      = ⟨1, [⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]⟩ := by
  decide

/-- Measurement and projection on the Bell state. -/
theorem measurement_check :
    let s := evolve (ket 2 0) [.H 0, .CNOT 0 1]
    measureWeight s 0 false = (1, 0) ∧
    measureWeight s 0 true = (1, 0) ∧
    project s 0 false = ⟨1, [⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]⟩ := by
  decide

end QuantumComputation
