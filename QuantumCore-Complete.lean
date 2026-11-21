/-
# QuantumCore — Discrete Quantum Computation for Digital Machines (Complete Version)

Exact discrete quantum computation over the ring `ℤ[√2, i]` with an explicit
`scale : Nat` representing denominator `(√2)^scale`, designed for digital
machines using integer arithmetic with zero floating-point rounding.

This complete version provides:
* Ring and squared-norm (`absSq : Ampl → ZSqrt2`, representing `p + q·√2`)
  algebraic lemmas in `ℤ[√2, i]` and `ℤ[√2]`.
* Exact Clifford+T gate evolution (`X, Z, S, T, H, CNOT`) on state vectors.
* Circuit structural theorems (`step_length`, `run_length`, `run_append`) and
  measurement / projection operations (`measureWeight`, `project`).
* Verified examples by exact computation (`decide`), covering single-qubit
  superposition, interference (`H` twice), `S` and `T` phases, Bell and GHZ
  entangled states, and measurement weights/projections.

Core Lean only, no Mathlib, no `sorry`.

Author: Takeo Yamamoto
License: Apache-2.0
-/

namespace QuantumCore

/-- An exact amplitude `(u + v·√2) + i·(w + z·√2)` in `ℤ[√2, i]`. -/
structure Ampl where
  u : Int
  v : Int
  w : Int
  z : Int
deriving DecidableEq, Repr

/-- An element `p + q·√2` of the real subring `ℤ[√2]`. -/
abbrev ZSqrt2 := Int × Int

namespace ZSqrt2

def zero : ZSqrt2 := (0, 0)
def add (x y : ZSqrt2) : ZSqrt2 := (x.1 + y.1, x.2 + y.2)
def sub (x y : ZSqrt2) : ZSqrt2 := (x.1 - y.1, x.2 - y.2)

/-- Multiplication in `ℤ[√2]`: `(p₁ + q₁√2)(p₂ + q₂√2) = (p₁p₂ + 2q₁q₂) + (p₁q₂ + q₁p₂)√2`. -/
def mul (x y : ZSqrt2) : ZSqrt2 :=
  (x.1 * y.1 + 2 * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- Power of `2` viewed as `(2^k, 0)` in `ℤ[√2]`. -/
def pow2 (k : Nat) : ZSqrt2 := ((2 ^ k : Nat : Int), 0)

theorem ext {x y : ZSqrt2} (h1 : x.1 = y.1) (h2 : x.2 = y.2) : x = y := by
  cases x; cases y; simp_all

theorem add_comm (x y : ZSqrt2) : add x y = add y x := by
  apply ext <;> simp [add, Int.add_comm]

theorem add_assoc (x y z : ZSqrt2) : add (add x y) z = add x (add y z) := by
  apply ext <;> simp [add, Int.add_assoc]

theorem add_zero (x : ZSqrt2) : add x zero = x := by
  apply ext <;> simp [add, zero]

theorem zero_add (x : ZSqrt2) : add zero x = x := by
  apply ext <;> simp [add, zero]

theorem pow2_succ (k : Nat) : pow2 (k + 1) = add (pow2 k) (pow2 k) := by
  apply ext
  · simp [pow2, add, Nat.pow_succ, Int.ofNat_mul, Int.two_mul]
  · simp [pow2, add]

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
def conj (a : Ampl) : Ampl := ⟨a.u, a.v, -a.w, -a.z⟩

/-- Multiply by `i`: `i·((u + v√2) + i(w + z√2)) = -(w + z√2) + i(u + v√2)`. -/
def mulI (a : Ampl) : Ampl := ⟨-a.w, -a.z, a.u, a.v⟩

/-- Multiply by `√2`: `√2·(u + v√2) = 2v + u√2` on real and imaginary parts. -/
def mulSqrt2 (a : Ampl) : Ampl := ⟨2 * a.v, a.u, 2 * a.z, a.w⟩

/-- Multiply by `1 + i`. -/
def mulOnePlusI (a : Ampl) : Ampl :=
  ⟨a.u - a.w, a.v - a.z, a.w + a.u, a.z + a.v⟩

/-- Squared norm `|A|² = (u² + 2v² + w² + 2z²) + 2(uv + wz)·√2` in `ℤ[√2]`. -/
def absSq (a : Ampl) : ZSqrt2 :=
  (a.u * a.u + 2 * a.v * a.v + a.w * a.w + 2 * a.z * a.z,
   2 * (a.u * a.v + a.w * a.z))

instance : Add Ampl := ⟨add⟩
instance : Neg Ampl := ⟨neg⟩
instance : Sub Ampl := ⟨sub⟩

theorem ext {a b : Ampl} (hu : a.u = b.u) (hv : a.v = b.v)
    (hw : a.w = b.w) (hz : a.z = b.z) : a = b := by
  cases a; cases b; simp_all

theorem add_comm (a b : Ampl) : a + b = b + a := by
  apply ext <;> simp [add, Int.add_comm]

theorem add_assoc (a b c : Ampl) : (a + b) + c = a + (b + c) := by
  apply ext <;> simp [add, Int.add_assoc]

theorem add_zero (a : Ampl) : a + 0 = a := by
  apply ext <;> simp [add, zero]

theorem zero_add (a : Ampl) : 0 + a = a := by
  apply ext <;> simp [add, zero]

theorem sub_eq_add_neg (a b : Ampl) : a - b = a + (-b) := by
  apply ext <;> simp [sub, add, neg, Int.sub_eq_add_neg]

theorem neg_neg (a : Ampl) : -(-a) = a := by
  apply ext <;> simp [neg]

theorem add_neg_cancel (a : Ampl) : a + (-a) = 0 := by
  apply ext <;> simp [add, neg, zero]

theorem neg_add_cancel (a : Ampl) : (-a) + a = 0 := by
  rw [add_comm]; exact add_neg_cancel a

theorem conj_conj (a : Ampl) : a.conj.conj = a := by
  apply ext <;> simp [conj]

theorem absSq_zero : (0 : Ampl).absSq = ZSqrt2.zero := by
  simp [zero, absSq, ZSqrt2.zero]

theorem absSq_neg (a : Ampl) : (-a).absSq = a.absSq := by
  apply ZSqrt2.ext
  · simp [neg, absSq, Int.neg_mul, Int.mul_neg, Int.neg_neg]
  · simp [neg, absSq, Int.neg_mul, Int.mul_neg, Int.neg_neg]

theorem absSq_mulI (a : Ampl) : a.mulI.absSq = a.absSq := by
  apply ZSqrt2.ext
  · simp only [mulI, absSq, Int.neg_mul, Int.mul_neg, Int.neg_neg,
      Int.add_comm, Int.add_left_comm]
  · simp only [mulI, absSq, Int.neg_mul, Int.mul_neg, Int.neg_neg,
      Int.mul_comm, Int.mul_left_comm, Int.add_comm]

end Ampl

/-- Partner index of `i` obtained by flipping bit `q`. -/
def partner (i q : Nat) : Nat :=
  if Nat.testBit i q then i - 2 ^ q else i + 2 ^ q

theorem partner_of_false {i q : Nat} (h : Nat.testBit i q = false) :
    partner i q = i + 2 ^ q := by
  simp [partner, h]

theorem partner_of_true {i q : Nat} (h : Nat.testBit i q = true) :
    partner i q = i - 2 ^ q := by
  simp [partner, h]

/-- Apply a 1-qubit gate `(a, b) ↦ g a b` to qubit `q` of `amps`. -/
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

/-- One-qubit Clifford+T gates as pair operations (`(bit0_amp, bit1_amp)`). -/
def gateX (a b : Ampl) : Ampl × Ampl := (b, a)
def gateZ (a b : Ampl) : Ampl × Ampl := (a, b.neg)
def gateS (a b : Ampl) : Ampl × Ampl := (a, b.mulI)
def gateH (a b : Ampl) : Ampl × Ampl := (a.add b, a.sub b)
def gateT (a b : Ampl) : Ampl × Ampl := (a.mulSqrt2, b.mulOnePlusI)

/-- A discrete quantum state: denominator scale `(√2)^scale` and amplitudes. -/
structure QState where
  scale : Nat
  amps : List Ampl
deriving DecidableEq, Repr

/-- Circuit instruction (`q = 0` is least significant bit). -/
inductive Instr where
  | X (q : Nat)
  | Z (q : Nat)
  | S (q : Nat)
  | T (q : Nat)
  | H (q : Nat)
  | CNOT (c t : Nat)
deriving DecidableEq, Repr

/-- Execute one instruction on a state. -/
def step (s : QState) : Instr → QState
  | .X q => ⟨s.scale, applyGate gateX q s.amps⟩
  | .Z q => ⟨s.scale, applyGate gateZ q s.amps⟩
  | .S q => ⟨s.scale, applyGate gateS q s.amps⟩
  | .T q => ⟨s.scale + 1, applyGate gateT q s.amps⟩
  | .H q => ⟨s.scale + 1, applyGate gateH q s.amps⟩
  | .CNOT c t => ⟨s.scale, applyCNOT c t s.amps⟩

/-- Execute a circuit left-to-right from an initial state. -/
def run (s : QState) (circuit : List Instr) : QState :=
  circuit.foldl step s

/-- Basis state `|k⟩` of an `n`-qubit register at `scale = 0`. -/
def basis (n k : Nat) : QState :=
  ⟨0, (List.range (2 ^ n)).map (fun i => if i = k then Ampl.one else Ampl.zero)⟩

/-- Total squared-norm weight `Σ |A_k|²` as an element of `ℤ[√2]`. -/
def weight (s : QState) : ZSqrt2 :=
  s.amps.foldl (fun acc a => ZSqrt2.add acc a.absSq) ZSqrt2.zero

/-- A state is normalized when `weight s = (2^scale, 0)` in `ℤ[√2]`. -/
@[reducible]
def normalized (s : QState) : Prop :=
  weight s = ZSqrt2.pow2 s.scale

/-- Measurement outcome weight for qubit `q` having value `outcome` (`false` = `0`, `true` = `1`). -/
def measureWeight (s : QState) (q : Nat) (outcome : Bool) : ZSqrt2 :=
  ((List.range s.amps.length).filter (fun i => decide (Nat.testBit i q = outcome))).foldl
    (fun acc i => ZSqrt2.add acc (s.amps[i]!).absSq) ZSqrt2.zero

/-- Project a state onto outcomes where qubit `q` equals `outcome`. -/
def project (s : QState) (q : Nat) (outcome : Bool) : QState :=
  ⟨s.scale,
    (List.range s.amps.length).map fun i =>
      if Nat.testBit i q = outcome then s.amps[i]! else Ampl.zero⟩

/-! ## Core Theorems -/

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

theorem basis_length (n k : Nat) : (basis n k).amps.length = 2 ^ n := by
  simp [basis]

theorem project_length (s : QState) (q : Nat) (outcome : Bool) :
    (project s q outcome).amps.length = s.amps.length := by
  simp [project]

/-! ## Verified Examples (Exact Discrete Computation) -/

theorem x_flips : run (basis 1 0) [.X 0] = basis 1 1 := by decide

theorem h_superposition :
    run (basis 1 0) [.H 0] = ⟨1, [⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]⟩ := by decide

theorem h_normalized : normalized (run (basis 1 0) [.H 0]) := by decide

theorem bell_state :
    run (basis 2 0) [.H 0, .CNOT 0 1]
      = ⟨1, [⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]⟩ := by
  decide

theorem bell_normalized :
    normalized (run (basis 2 0) [.H 0, .CNOT 0 1]) := by decide

theorem bell_measure_weights :
    let s := run (basis 2 0) [.H 0, .CNOT 0 1]
    measureWeight s 0 false = (1, 0) ∧ measureWeight s 0 true = (1, 0) := by
  decide

theorem bell_project_zero :
    let s := run (basis 2 0) [.H 0, .CNOT 0 1]
    project s 0 false = ⟨1, [⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]⟩ := by
  decide

theorem ghz_state :
    run (basis 3 0) [.H 0, .CNOT 0 1, .CNOT 1 2]
      = ⟨1, [⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩,
             ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]⟩ := by
  decide

theorem h_twice :
    run (basis 1 0) [.H 0, .H 0] = ⟨2, [⟨2, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]⟩ := by
  decide

theorem t_phase :
    run (basis 1 1) [.T 0] = ⟨1, [⟨0, 0, 0, 0⟩, ⟨1, 0, 1, 0⟩]⟩ := by decide

theorem t_superposition :
    run (basis 1 0) [.H 0, .T 0]
      = ⟨2, [⟨0, 1, 0, 0⟩, ⟨1, 0, 1, 0⟩]⟩ := by decide

theorem t_superposition_normalized :
    normalized (run (basis 1 0) [.H 0, .T 0]) := by decide

theorem s_phase :
    run (basis 1 1) [.S 0] = ⟨0, [⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩]⟩ := by decide

end QuantumCore
