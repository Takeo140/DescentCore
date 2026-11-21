/-
# LinearCore — Discrete Complex Linear Algebra (Basic Complete Version)

Linear algebra over the complex numbers, in a fully discrete, exact form,
designed to be used on digital machines.

The scalars are the **Gaussian rationals** `ℚ(i)`: a scalar is a pair of
rationals `(re, im)`, read as `re + i·im`. This is a field — every nonzero
scalar has an inverse, computed exactly — and it is discrete: no floating
point, no limits, no rounding anywhere. Vectors are lists of scalars,
matrices are lists of rows, and every operation is exact rational
arithmetic, so the whole development runs as-is on a digital computer
(the companion `linear.py` runs the same structure, including Gaussian
elimination over `ℚ(i)`).

This file is the **basic complete version**: the field laws of the
scalars, the vector operations with the inner product, the matrix
operations with transpose and conjugate transpose, the identity matrix
laws, determinants and inverses, and exact solving — with the algebraic
laws proved as theorems, not assumed. The scope is stated honestly:

* Scalar field laws are proved in full, including
  `a * a⁻¹ = 1` under the hypothesis `normSq a ≠ 0` (for a concrete
  nonzero scalar this is discharged by `decide`).
* Vector laws and the inner-product laws are proved for all lengths.
* Matrix addition, transpose and conjugate-transpose laws are proved for
  all shapes (rectangular where needed). The identity laws
  `I * A = A` and `A * I = A` are proved for rectangular matrices.
* Matrix multiplication is defined for all shapes; its associativity is
  proved here for the `2 × 2` case, by exact componentwise computation
  on the `M2` record together with a bridge to the list matrices.
  Determinants are the classical formulas for orders 2 and 3, the
  adjugate inverse satisfies `A * A⁻¹ = A⁻¹ * A = I` for order 2 under
  `det A ≠ 0`, and Cramer's rule holds for `2 × 2` systems. The law
  `det (A * B) = det A * det B` is verified computationally in
  `linear.py`; a Lean proof of that one identity is not included.
* Eigenvalues, diagonalization and the spectral theory are **not**
  included: they need algebraic closure and limits, which leave the
  discrete exact setting. This is the boundary of the basic version.

Core Lean only, no Mathlib, no `sorry`.

Author: Takeo Yamamoto
License: Apache-2.0
-/

namespace LinearCore

/-- A discrete complex scalar: a Gaussian rational `re + i·im` with
    rational components. -/
structure QC where
  re : Rat
  im : Rat
deriving DecidableEq, Repr

namespace QC

def zero : QC := ⟨0, 0⟩
def one : QC := ⟨1, 0⟩
def eye : QC := ⟨0, 1⟩

instance : Inhabited QC := ⟨zero⟩
instance : Zero QC := ⟨zero⟩
instance : One QC := ⟨one⟩

def add (a b : QC) : QC := ⟨a.re + b.re, a.im + b.im⟩
def neg (a : QC) : QC := ⟨-a.re, -a.im⟩
def sub (a b : QC) : QC := ⟨a.re - b.re, a.im - b.im⟩
def mul (a b : QC) : QC := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
def conj (a : QC) : QC := ⟨a.re, -a.im⟩

/-- The squared norm `re² + im²`, a nonnegative rational (a plain sum of
    two rational squares). -/
def normSq (a : QC) : Rat := a.re * a.re + a.im * a.im

/-- The inverse `(re − i·im) / (re² + im²)`. At `0` it is defined as `0`
    (the usual junk value); the inverse law below is stated under
    `normSq a ≠ 0`. -/
def inv (a : QC) : QC := ⟨a.re / a.normSq, -a.im / a.normSq⟩

def div (a b : QC) : QC := a.mul b.inv

instance : Add QC := ⟨add⟩
instance : Neg QC := ⟨neg⟩
instance : Sub QC := ⟨sub⟩
instance : Mul QC := ⟨mul⟩

end QC

/-! ## Rational normalization

Component identities in `ℚ` are proved by expanding definitions and
normalizing with the commutative-ring lemmas of core `Rat`. -/

theorem rat_mul_left_comm (a b c : Rat) : a * (b * c) = b * (a * c) := by
  rw [← Rat.mul_assoc, Rat.mul_comm a b, Rat.mul_assoc]

macro "qc_norm" : tactic =>
  `(tactic| simp only [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_neg,
      Rat.neg_mul, Rat.neg_add, Rat.neg_neg, Rat.neg_zero, Rat.mul_assoc, Rat.mul_comm, rat_mul_left_comm,
      Rat.add_assoc, Rat.add_comm, Rat.add_left_comm, Rat.mul_one, Rat.one_mul,
      Rat.mul_zero, Rat.zero_mul, Rat.add_zero, Rat.zero_add, Rat.add_neg_cancel,
      Rat.neg_add_cancel])

namespace QC

theorem ext {a b : QC} (h₁ : a.re = b.re) (h₂ : a.im = b.im) : a = b := by
  cases a; cases b; simp_all

theorem add_comm (a b : QC) : a + b = b + a :=
  ext (Rat.add_comm _ _) (Rat.add_comm _ _)

theorem add_assoc (a b c : QC) : (a + b) + c = a + (b + c) :=
  ext (Rat.add_assoc _ _ _) (Rat.add_assoc _ _ _)

theorem add_zero (a : QC) : a + 0 = a :=
  ext (Rat.add_zero _) (Rat.add_zero _)

theorem zero_add (a : QC) : 0 + a = a :=
  ext (Rat.zero_add _) (Rat.zero_add _)

theorem add_neg_cancel (a : QC) : a + (-a) = 0 :=
  ext (Rat.add_neg_cancel _) (Rat.add_neg_cancel _)

theorem neg_add_cancel (a : QC) : (-a) + a = 0 :=
  ext (Rat.neg_add_cancel _) (Rat.neg_add_cancel _)

theorem sub_eq_add_neg (a b : QC) : a - b = a + (-b) :=
  ext (Rat.sub_eq_add_neg _ _) (Rat.sub_eq_add_neg _ _)

theorem mul_comm (a b : QC) : a * b = b * a := by
  apply ext
  · show a.re * b.re - a.im * b.im = b.re * a.re - b.im * a.im; qc_norm
  · show a.re * b.im + a.im * b.re = b.re * a.im + b.im * a.re; qc_norm

theorem mul_assoc (a b c : QC) : (a * b) * c = a * (b * c) := by
  apply ext
  · show (a.re * b.re - a.im * b.im) * c.re - (a.re * b.im + a.im * b.re) * c.im
      = a.re * (b.re * c.re - b.im * c.im) - a.im * (b.re * c.im + b.im * c.re)
    qc_norm
  · show (a.re * b.re - a.im * b.im) * c.im + (a.re * b.im + a.im * b.re) * c.re
      = a.re * (b.re * c.im + b.im * c.re) + a.im * (b.re * c.re - b.im * c.im)
    qc_norm

theorem mul_one (a : QC) : a * 1 = a := by
  apply ext
  · show a.re * 1 - a.im * 0 = a.re; qc_norm
  · show a.re * 0 + a.im * 1 = a.im; qc_norm

theorem one_mul (a : QC) : 1 * a = a := by
  apply ext
  · show 1 * a.re - 0 * a.im = a.re; qc_norm
  · show 1 * a.im + 0 * a.re = a.im; qc_norm

theorem mul_zero (a : QC) : a * 0 = 0 := by
  apply ext
  · show a.re * 0 - a.im * 0 = 0; qc_norm
  · show a.re * 0 + a.im * 0 = 0; qc_norm

theorem zero_mul (a : QC) : 0 * a = 0 := by
  apply ext
  · show 0 * a.re - 0 * a.im = 0; qc_norm
  · show 0 * a.im + 0 * a.re = 0; qc_norm

theorem mul_add (a b c : QC) : a * (b + c) = a * b + a * c := by
  apply ext
  · show a.re * (b.re + c.re) - a.im * (b.im + c.im)
      = (a.re * b.re - a.im * b.im) + (a.re * c.re - a.im * c.im)
    qc_norm
  · show a.re * (b.im + c.im) + a.im * (b.re + c.re)
      = (a.re * b.im + a.im * b.re) + (a.re * c.im + a.im * c.re)
    qc_norm

theorem add_mul (a b c : QC) : (a + b) * c = a * c + b * c := by
  apply ext
  · show (a.re + b.re) * c.re - (a.im + b.im) * c.im
      = (a.re * c.re - a.im * c.im) + (b.re * c.re - b.im * c.im)
    qc_norm
  · show (a.re + b.re) * c.im + (a.im + b.im) * c.re
      = (a.re * c.im + a.im * c.re) + (b.re * c.im + b.im * c.re)
    qc_norm

theorem conj_conj (a : QC) : a.conj.conj = a :=
  ext rfl (Rat.neg_neg _)

theorem conj_add (a b : QC) : (a + b).conj = a.conj + b.conj :=
  ext rfl (Rat.neg_add)

theorem conj_mul (a b : QC) : (a * b).conj = a.conj * b.conj := by
  apply ext
  · show a.re * b.re - a.im * b.im = a.re * b.re - (-a.im) * (-b.im); qc_norm
  · show -(a.re * b.im + a.im * b.re) = a.re * (-b.im) + (-a.im) * b.re; qc_norm

/-- `a * conj a` is the real scalar `normSq a`: its real part is
    `normSq a` and its imaginary part is `0`. -/
theorem mul_conj (a : QC) : (a * a.conj).re = a.normSq ∧ (a * a.conj).im = 0 := by
  constructor
  · show a.re * a.re - a.im * (-a.im) = a.re * a.re + a.im * a.im; qc_norm
  · show a.re * (-a.im) + a.im * a.re = 0; qc_norm

/-- The inverse law: if `normSq a ≠ 0` then `a * a⁻¹ = 1`. -/
theorem mul_inv_cancel (a : QC) (h : a.normSq ≠ 0) : a * a.inv = 1 := by
  have key : a.re * (a.re / a.normSq) + a.im * (a.im / a.normSq) = 1 := by
    rw [Rat.div_def, Rat.div_def]
    have e : a.re * (a.re * a.normSq⁻¹) + a.im * (a.im * a.normSq⁻¹)
        = a.normSq * a.normSq⁻¹ := by
      show a.re * (a.re * a.normSq⁻¹) + a.im * (a.im * a.normSq⁻¹)
        = (a.re * a.re + a.im * a.im) * a.normSq⁻¹
      qc_norm
    rw [e, Rat.mul_inv_cancel _ h]
  apply ext
  · show a.re * (a.re / a.normSq) - a.im * (-a.im / a.normSq) = 1
    have h2 : a.re * (a.re / a.normSq) - a.im * (-a.im / a.normSq)
        = a.re * (a.re / a.normSq) + a.im * (a.im / a.normSq) := by
      rw [Rat.div_def, Rat.div_def, Rat.div_def]; qc_norm
    rw [h2]; exact key
  · show a.re * (-a.im / a.normSq) + a.im * (a.re / a.normSq) = 0
    rw [Rat.div_def, Rat.div_def]
    qc_norm

/-- The inverse law from the other side: `a⁻¹ * a = 1`. -/
theorem inv_mul_cancel (a : QC) (h : a.normSq ≠ 0) : a.inv * a = 1 := by
  rw [mul_comm]; exact mul_inv_cancel a h

end QC

theorem QC.add_left_comm (a b c : QC) : a + (b + c) = b + (a + c) := by
  rw [← QC.add_assoc, QC.add_comm a b, QC.add_assoc]

/-! ## Vectors

A vector is a list of scalars. Operations are pointwise (`zipWith`), so
they are defined for all lengths, with the usual truncation semantics of
`zipWith`; the laws that need matching lengths say so. -/

/-- Vector addition, pointwise. -/
def vadd (u v : List QC) : List QC := List.zipWith QC.add u v

/-- Scalar multiplication. -/
def vsmul (a : QC) (u : List QC) : List QC := u.map (a * ·)

/-- The zero vector of length `n`. -/
def vzero (n : Nat) : List QC := List.replicate n 0

/-- The sum of a vector. -/
def vsum (u : List QC) : QC := u.foldl (· + ·) 0

/-- The dot product `Σ uᵢvᵢ` (no conjugation). -/
def dot (u v : List QC) : QC := vsum (List.zipWith QC.mul u v)

/-- The inner product `Σ (conj uᵢ) vᵢ`, conjugate-linear in the first
    argument. -/
def dotc (u v : List QC) : QC := dot (u.map QC.conj) v

theorem foldl_add_from (a : QC) (l : List QC) :
    l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
  induction l generalizing a with
  | nil => simp [QC.add_zero]
  | cons x l ih =>
    show (l.foldl (· + ·) (a + x)) = a + (l.foldl (· + ·) (0 + x))
    rw [ih (a + x), ih (0 + x), QC.zero_add, QC.add_assoc]

theorem vsum_cons (x : QC) (l : List QC) : vsum (x :: l) = x + vsum l := by
  show (l.foldl (· + ·) (0 + x)) = x + l.foldl (· + ·) 0
  rw [foldl_add_from, QC.zero_add]

theorem vsum_append (u v : List QC) : vsum (u ++ v) = vsum u + vsum v := by
  show (u ++ v).foldl (· + ·) 0 = u.foldl (· + ·) 0 + v.foldl (· + ·) 0
  rw [List.foldl_append, foldl_add_from]

theorem vsum_zipWith_add (u v : List QC) (h : u.length = v.length) :
    vsum (List.zipWith QC.add u v) = vsum u + vsum v := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => show (0 : QC) = 0 + 0; exact (QC.zero_add 0).symm
    | cons b v => simp at h
  | cons a u ih =>
    cases v with
    | nil => simp at h
    | cons b v =>
      have h' : u.length = v.length := by simpa using h
      show vsum ((a + b) :: List.zipWith QC.add u v) = _
      rw [vsum_cons, vsum_cons, vsum_cons, ih _ h']
      simp only [QC.add_assoc, QC.add_left_comm]

theorem vadd_comm (u v : List QC) : vadd u v = vadd v u := by
  induction u generalizing v with
  | nil => cases v <;> rfl
  | cons a u ih =>
    cases v with
    | nil => rfl
    | cons b v =>
      show (a + b) :: vadd u v = (b + a) :: vadd v u
      rw [QC.add_comm a b, ih]

theorem vadd_assoc (u v w : List QC) : vadd (vadd u v) w = vadd u (vadd v w) := by
  induction u generalizing v w with
  | nil => cases v <;> cases w <;> rfl
  | cons a u ih =>
    cases v with
    | nil => cases w <;> rfl
    | cons b v =>
      cases w with
      | nil => rfl
      | cons c w =>
        show ((a + b) + c) :: vadd (vadd u v) w = (a + (b + c)) :: vadd u (vadd v w)
        rw [QC.add_assoc, ih]

theorem vadd_zero (u : List QC) : vadd u (vzero u.length) = u := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    show (a + 0) :: vadd u (vzero u.length) = a :: u
    rw [QC.add_zero, ih]

theorem vsmul_add (a : QC) (u v : List QC) :
    vsmul a (vadd u v) = vadd (vsmul a u) (vsmul a v) := by
  induction u generalizing v with
  | nil => cases v <;> rfl
  | cons x u ih =>
    cases v with
    | nil => rfl
    | cons y v =>
      show (a * (x + y)) :: vsmul a (vadd u v) = (a * x + a * y) :: vadd (vsmul a u) (vsmul a v)
      rw [QC.mul_add, ih]

theorem add_smul (a b : QC) (u : List QC) :
    vsmul (a + b) u = vadd (vsmul a u) (vsmul b u) := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    show ((a + b) * x) :: vsmul (a + b) u = (a * x + b * x) :: vadd (vsmul a u) (vsmul b u)
    rw [QC.add_mul, ih]

theorem mul_smul (a b : QC) (u : List QC) :
    vsmul (a * b) u = vsmul a (vsmul b u) := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    show ((a * b) * x) :: vsmul (a * b) u = (a * (b * x)) :: vsmul a (vsmul b u)
    rw [QC.mul_assoc, ih]

theorem one_smul (u : List QC) : vsmul 1 u = u := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    show (1 * x) :: vsmul 1 u = x :: u
    rw [QC.one_mul, ih]

theorem zero_smul (u : List QC) : vsmul 0 u = vzero u.length := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    show (0 * x) :: vsmul 0 u = 0 :: vzero u.length
    rw [QC.zero_mul, ih]

theorem vsum_mul_left (c : QC) (u : List QC) :
    vsum (u.map (c * ·)) = c * vsum u := by
  induction u with
  | nil => simp [vsum, QC.mul_zero]
  | cons x u ih =>
    show vsum ((c * x) :: u.map (c * ·)) = c * vsum (x :: u)
    rw [vsum_cons, vsum_cons, ih, QC.mul_add]

theorem vsum_mul_right (c : QC) (u : List QC) :
    vsum (u.map (· * c)) = vsum u * c := by
  induction u with
  | nil => simp [vsum, QC.zero_mul]
  | cons x u ih =>
    show vsum ((x * c) :: u.map (· * c)) = vsum (x :: u) * c
    rw [vsum_cons, vsum_cons, ih, QC.add_mul]

theorem dot_comm (u v : List QC) : dot u v = dot v u := by
  have h : List.zipWith QC.mul u v = List.zipWith QC.mul v u := by
    induction u generalizing v with
    | nil => cases v <;> rfl
    | cons a u ih =>
      cases v with
      | nil => rfl
      | cons b v =>
        show (a * b) :: List.zipWith QC.mul u v = (b * a) :: List.zipWith QC.mul v u
        rw [QC.mul_comm a b, ih]
  rw [dot, dot, h]

theorem dot_add_right (u v w : List QC) (h : v.length = w.length) :
    dot u (vadd v w) = dot u v + dot u w := by
  have h1 : List.zipWith QC.mul u (vadd v w)
      = List.zipWith QC.add (List.zipWith QC.mul u v) (List.zipWith QC.mul u w) := by
    induction u generalizing v w with
    | nil => cases v <;> cases w <;> rfl
    | cons a u ih =>
      cases v with
      | nil =>
        cases w with
        | nil => rfl
        | cons c w => simp at h
      | cons b v =>
        cases w with
        | nil => simp at h
        | cons c w =>
          have h' : v.length = w.length := by simpa using h
          show (a * (b + c)) :: List.zipWith QC.mul u (vadd v w)
            = (a * b + a * c) :: List.zipWith QC.add (List.zipWith QC.mul u v) (List.zipWith QC.mul u w)
          rw [QC.mul_add, ih _ _ h']
  have h2 : (List.zipWith QC.mul u v).length = (List.zipWith QC.mul u w).length := by
    simp [List.length_zipWith, h]
  rw [dot, dot, dot, h1, vsum_zipWith_add _ _ h2]

theorem dot_smul_right (a : QC) (u v : List QC) :
    dot u (vsmul a v) = dot u v * a := by
  have h1 : List.zipWith QC.mul u (vsmul a v)
      = (List.zipWith QC.mul u v).map (· * a) := by
    induction u generalizing v with
    | nil => cases v <;> rfl
    | cons x u ih =>
      cases v with
      | nil => rfl
      | cons y v =>
        show (x * (a * y)) :: List.zipWith QC.mul u (vsmul a v)
          = ((x * y) * a) :: (List.zipWith QC.mul u v).map (· * a)
        rw [QC.mul_assoc x y a, QC.mul_comm a y, ih]
  rw [dot, dot, h1, vsum_mul_right]

theorem rfoldl_add_from (a : Rat) (l : List Rat) :
    l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
  induction l generalizing a with
  | nil => simp [Rat.add_zero]
  | cons x l ih =>
    show (l.foldl (· + ·) (a + x)) = a + (l.foldl (· + ·) (0 + x))
    rw [ih (a + x), ih (0 + x), Rat.zero_add, Rat.add_assoc]

/-- The inner product of a vector with itself is the real scalar whose
    real part is the sum of the squared norms and whose imaginary part
    is `0`. -/
theorem dotc_self (v : List QC) :
    dotc v v = ⟨(v.map QC.normSq).foldl (· + ·) 0, 0⟩ := by
  have h1 : List.zipWith QC.mul (v.map QC.conj) v = v.map (fun x => x * x.conj) := by
    induction v with
    | nil => rfl
    | cons x v ih =>
      show (x.conj * x) :: List.zipWith QC.mul (v.map QC.conj) v
        = (x * x.conj) :: v.map (fun x => x * x.conj)
      rw [QC.mul_comm x.conj x, ih]
  have h2 : ∀ l : List QC, vsum (l.map (fun x => x * x.conj))
      = ⟨(l.map QC.normSq).foldl (· + ·) 0, 0⟩ := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih =>
      show vsum ((x * x.conj) :: l.map (fun x => x * x.conj)) = _
      rw [vsum_cons, ih]
      obtain ⟨h3, h4⟩ := QC.mul_conj x
      apply QC.ext
      · show (x * x.conj).re + ((l.map QC.normSq).foldl (· + ·) 0) = _
        rw [h3]
        show x.normSq + (l.map QC.normSq).foldl (· + ·) 0
          = (l.map QC.normSq).foldl (· + ·) (0 + x.normSq)
        rw [rfoldl_add_from (0 + x.normSq) (l.map QC.normSq), Rat.zero_add]
      · show (x * x.conj).im + 0 = 0
        rw [h4, Rat.add_zero]
  rw [dotc, dot, h1, h2]

theorem dotc_smul_left (a : QC) (u v : List QC) :
    dotc (vsmul a u) v = a.conj * dotc u v := by
  have h1 : List.zipWith QC.mul (vsmul a.conj (u.map QC.conj)) v
      = (List.zipWith QC.mul (u.map QC.conj) v).map (a.conj * ·) := by
    induction u generalizing v with
    | nil => cases v <;> rfl
    | cons x u ih =>
      cases v with
      | nil => rfl
      | cons y v =>
        show ((a.conj * x.conj) * y) :: List.zipWith QC.mul (vsmul a.conj (u.map QC.conj)) v
          = (a.conj * (x.conj * y)) :: (List.zipWith QC.mul (u.map QC.conj) v).map (a.conj * ·)
        rw [QC.mul_assoc, ih]
  have h2 : (vsmul a u).map QC.conj = vsmul a.conj (u.map QC.conj) := by
    simp [vsmul, List.map_map, QC.conj_mul]
  rw [dotc, dotc, dot, h2, h1, vsum_mul_left]
  rfl

/-! ## Matrices

A matrix is a list of rows. Entries are accessed through `entry`, which
returns `0` outside the stored range, so entry identities can be stated
without side conditions; the shape-sensitive laws carry a rectangularity
hypothesis `Rect`. -/

/-- The width of a matrix: the length of its first row (`0` if empty). -/
def width (M : List (List QC)) : Nat := (M[0]?.getD []).length

/-- The `(i, j)` entry, `0` outside the stored range. -/
def entry (M : List (List QC)) (i j : Nat) : QC := (M[i]?.getD [])[j]?.getD 0

/-- A matrix is rectangular if every row has the same length `width M`. -/
def Rect (M : List (List QC)) : Prop := ∀ row ∈ M, row.length = width M

/-- Matrix addition, row-wise. -/
def madd (A B : List (List QC)) : List (List QC) := List.zipWith vadd A B

/-- The `j`-th column of a matrix, as a vector. -/
def col (M : List (List QC)) (j : Nat) : List QC := M.map (fun row => row[j]?.getD 0)

/-- The transpose: rows become columns. -/
def transpose (M : List (List QC)) : List (List QC) :=
  (List.range (width M)).map (fun j => col M j)

/-- The conjugate transpose. -/
def conjTranspose (M : List (List QC)) : List (List QC) :=
  (transpose M).map (fun row => row.map QC.conj)

/-- Matrix times vector. -/
def matVec (M : List (List QC)) (v : List QC) : List QC := M.map (fun row => dot row v)

/-- Matrix multiplication: the `(i, j)` entry is the dot product of the
    `i`-th row of `A` with the `j`-th column of `B`. -/
def matMul (A B : List (List QC)) : List (List QC) :=
  A.map (fun row => (List.range (width B)).map (fun j => dot row (col B j)))

/-- The unit row: `1` in position `k`, `0` elsewhere, of length `n`. -/
def unitRow (k n : Nat) : List QC :=
  List.replicate k 0 ++ [1] ++ List.replicate (n - k - 1) 0

/-- The identity matrix of order `n`. -/
def eyeM (n : Nat) : List (List QC) := (List.range n).map (fun i => unitRow i n)

/-- The diagonal of a matrix, as a vector. -/
def diag (M : List (List QC)) : List QC :=
  (List.range M.length).map (fun i => entry M i i)

/-- The trace: the sum of the diagonal. -/
def trace (M : List (List QC)) : QC := vsum (diag M)

theorem entry_eq_getElem (M : List (List QC)) (i j : Nat)
    (hi : i < M.length) (hj : j < (M[i]).length) : entry M i j = M[i][j] := by
  rw [entry, List.getElem?_eq_getElem hi, Option.getD_some,
    List.getElem?_eq_getElem hj, Option.getD_some]

theorem col_entry (M : List (List QC)) (i j : Nat) :
    (col M j)[i]?.getD 0 = entry M i j := by
  rw [col, List.getElem?_map, entry]
  cases h : M[i]? with
  | none => rfl
  | some row => rfl

theorem entry_transpose (M : List (List QC)) (i j : Nat) (hj : j < width M) :
    entry (transpose M) j i = entry M i j := by
  have h1 : (transpose M)[j]? = some (col M j) := by
    rw [transpose, List.getElem?_map, List.getElem?_range hj]
    rfl
  rw [entry, h1, Option.getD_some]
  exact col_entry M i j

theorem entry_matMul (A B : List (List QC)) (i j : Nat) (hj : j < width B) :
    entry (matMul A B) i j = dot (A[i]?.getD []) (col B j) := by
  have h1 : (matMul A B)[i]?
      = (A[i]?).map (fun row => (List.range (width B)).map (fun j => dot row (col B j))) := by
    rw [matMul, List.getElem?_map]
  rw [entry, h1]
  cases h : A[i]? with
  | none => rfl
  | some row =>
    rw [Option.map_some, Option.getD_some, List.getElem?_map,
      List.getElem?_range hj, Option.map_some, Option.getD_some,
      Option.getD_some]

theorem mat_ext (M N : List (List QC)) (hM : Rect M) (hN : Rect N)
    (hl : M.length = N.length) (hw : width M = width N)
    (he : ∀ i j, entry M i j = entry N i j) : M = N := by
  apply List.ext_getElem hl
  intro i hi₁ hi₂
  have hrow : (M[i]).length = (N[i]).length := by
    rw [hM _ (List.getElem_mem hi₁), hN _ (List.getElem_mem hi₂), hw]
  apply List.ext_getElem hrow
  intro j hj₁ hj₂
  rw [← entry_eq_getElem M i j hi₁ hj₁, ← entry_eq_getElem N i j hi₂ hj₂]
  exact he i j

theorem madd_comm (A B : List (List QC)) : madd A B = madd B A := by
  induction A generalizing B with
  | nil => cases B <;> rfl
  | cons r A ih =>
    cases B with
    | nil => rfl
    | cons s B =>
      show vadd r s :: madd A B = vadd s r :: madd B A
      rw [vadd_comm, ih]

theorem madd_assoc (A B C : List (List QC)) :
    madd (madd A B) C = madd A (madd B C) := by
  induction A generalizing B C with
  | nil => cases B <;> cases C <;> rfl
  | cons r A ih =>
    cases B with
    | nil => cases C <;> rfl
    | cons s B =>
      cases C with
      | nil => rfl
      | cons t C =>
        show vadd (vadd r s) t :: madd (madd A B) C
          = vadd r (vadd s t) :: madd A (madd B C)
        rw [vadd_assoc, ih]

theorem entry_add (A B : List (List QC)) (i j : Nat)
    (hi : i < A.length) (hiB : i < B.length)
    (hj : j < (A[i]).length) (hjB : j < (B[i]).length) :
    entry (madd A B) i j = entry A i j + entry B i j := by
  have hlen : (madd A B).length = min A.length B.length := by
    rw [madd, List.length_zipWith]
  have hiM : i < (madd A B).length := by rw [hlen]; omega
  have hz : (madd A B)[i]'hiM = vadd (A[i]'hi) (B[i]'hiB) :=
    List.getElem_zipWith (h := hiM)
  have hjM : j < (vadd (A[i]'hi) (B[i]'hiB)).length := by
    rw [vadd, List.length_zipWith]; omega
  have hz2 : (vadd (A[i]'hi) (B[i]'hiB))[j]'hjM = ((A[i]'hi)[j]'hj) + ((B[i]'hiB)[j]'hjB) :=
    List.getElem_zipWith (h := hjM)
  rw [entry, List.getElem?_eq_getElem hiM, Option.getD_some, hz,
    List.getElem?_eq_getElem hjM, Option.getD_some, hz2,
    entry_eq_getElem A i j hi hj, entry_eq_getElem B i j hiB hjB]

theorem transpose_length (M : List (List QC)) :
    (transpose M).length = width M := by
  rw [transpose, List.length_map, List.length_range]

theorem transpose_width (M : List (List QC)) (hw : 0 < width M) :
    width (transpose M) = M.length := by
  rw [width, transpose, List.getElem?_map, List.getElem?_range hw,
    Option.map_some, Option.getD_some, col, List.length_map]

theorem rect_transpose (M : List (List QC)) (hM : Rect M) (hw : 0 < width M) :
    Rect (transpose M) := by
  intro row hrow
  rw [transpose, List.mem_map] at hrow
  obtain ⟨j, _, rfl⟩ := hrow
  rw [transpose_width M hw, col, List.length_map]

theorem entry_eq_zero_of_length_le (M : List (List QC)) (i j : Nat)
    (h : M.length ≤ i) : entry M i j = 0 := by
  rw [entry, List.getElem?_eq_none h]
  rfl

theorem entry_eq_zero_of_width_le (M : List (List QC)) (hM : Rect M)
    (i j : Nat) (hi : i < M.length) (hj : width M ≤ j) : entry M i j = 0 := by
  have hrow : (M[i]'hi).length = width M := hM _ (List.getElem_mem hi)
  rw [entry, List.getElem?_eq_getElem hi, Option.getD_some,
    List.getElem?_eq_none (by omega)]
  rfl

theorem transpose_transpose (M : List (List QC)) (hM : Rect M) (hw : 0 < width M) :
    transpose (transpose M) = M := by
  have hMt : Rect (transpose M) := rect_transpose M hM hw
  have hwt : width (transpose M) = M.length := transpose_width M hw
  have hpos : 0 < M.length := by
    rcases M with _ | ⟨r, M⟩
    · simp [width] at hw
    · exact Nat.succ_pos _
  have hMtt : Rect (transpose (transpose M)) :=
    rect_transpose _ hMt (by rw [hwt]; exact hpos)
  have hwtt : width (transpose (transpose M)) = width M := by
    rw [transpose_width _ (by rw [hwt]; exact hpos), transpose_length]
  have hltt : (transpose (transpose M)).length = M.length := by
    rw [transpose_length, hwt]
  apply mat_ext _ _ hMtt hM hltt hwtt
  intro i j
  by_cases hi : i < M.length
  · by_cases hj : j < width M
    · rw [entry_transpose (transpose M) j i (by rw [hwt]; exact hi),
        entry_transpose M i j hj]
    · rw [entry_eq_zero_of_width_le _ hMtt i j (by rw [hltt]; exact hi)
        (by rw [hwtt]; omega),
        entry_eq_zero_of_width_le _ hM i j hi (by omega)]
  · rw [entry_eq_zero_of_length_le _ i j (by rw [hltt]; omega),
      entry_eq_zero_of_length_le _ i j (by omega)]

theorem entry_map_conj (N : List (List QC)) (i j : Nat) :
    entry (N.map (fun row => row.map QC.conj)) i j = (entry N i j).conj := by
  rw [entry, entry, List.getElem?_map]
  cases h : N[i]? with
  | none => rfl
  | some row =>
    rw [Option.map_some, Option.getD_some, Option.getD_some, List.getElem?_map]
    cases h2 : row[j]? with
    | none => rfl
    | some x => rw [Option.map_some, Option.getD_some, Option.getD_some]

theorem entry_conjTranspose (N : List (List QC)) (i j : Nat) (hi : i < width N) :
    entry (conjTranspose N) i j = (entry N j i).conj := by
  rw [conjTranspose, entry_map_conj, entry_transpose N j i hi]

theorem conjTranspose_length (M : List (List QC)) :
    (conjTranspose M).length = width M := by
  rw [conjTranspose, List.length_map, transpose_length]

theorem conjTranspose_width (M : List (List QC)) (hw : 0 < width M) :
    width (conjTranspose M) = M.length := by
  have h1 : (conjTranspose M)[0]? = some ((col M 0).map QC.conj) := by
    rw [conjTranspose, List.getElem?_map, transpose, List.getElem?_map,
      List.getElem?_range hw]
    rfl
  rw [width, h1, Option.getD_some, col, List.length_map, List.length_map]

theorem rect_conjTranspose (M : List (List QC)) (hw : 0 < width M) :
    Rect (conjTranspose M) := by
  intro row hrow
  rw [conjTranspose, List.mem_map] at hrow
  obtain ⟨t, ht, rfl⟩ := hrow
  rw [conjTranspose_width M hw]
  rw [transpose, List.mem_map] at ht
  obtain ⟨j, _, rfl⟩ := ht
  rw [List.length_map, col, List.length_map]

theorem conjTranspose_conjTranspose (M : List (List QC)) (hM : Rect M)
    (hw : 0 < width M) : conjTranspose (conjTranspose M) = M := by
  have hM1 : Rect (conjTranspose M) := rect_conjTranspose M hw
  have hw1 : width (conjTranspose M) = M.length := conjTranspose_width M hw
  have hl1 : (conjTranspose M).length = width M := conjTranspose_length M
  have hpos : 0 < M.length := by
    rcases M with _ | ⟨r, M⟩
    · simp [width] at hw
    · exact Nat.succ_pos _
  have hw2 : 0 < width (conjTranspose M) := by rw [hw1]; exact hpos
  have hM2 : Rect (conjTranspose (conjTranspose M)) :=
    rect_conjTranspose _ hw2
  have hwtt : width (conjTranspose (conjTranspose M)) = width M := by
    rw [conjTranspose_width _ hw2, hl1]
  have hltt : (conjTranspose (conjTranspose M)).length = M.length := by
    rw [conjTranspose_length, hw1]
  apply mat_ext _ _ hM2 hM hltt hwtt
  intro i j
  by_cases hi : i < M.length
  · by_cases hj : j < width M
    · rw [entry_conjTranspose _ i j (by rw [hw1]; exact hi),
        entry_conjTranspose M j i hj, QC.conj_conj]
    · rw [entry_eq_zero_of_width_le _ hM2 i j (by rw [hltt]; exact hi)
        (by rw [hwtt]; omega),
        entry_eq_zero_of_width_le _ hM i j hi (by omega)]
  · rw [entry_eq_zero_of_length_le _ i j (by rw [hltt]; omega),
      entry_eq_zero_of_length_le _ i j (by omega)]

theorem unitRow_length (k n : Nat) (h : k < n) : (unitRow k n).length = n := by
  simp [unitRow, List.length_append, List.length_replicate]
  omega

theorem unitRow_succ (k n : Nat) : unitRow (k + 1) n = 0 :: unitRow k (n - 1) := by
  have e : n - (k + 1) - 1 = (n - 1) - k - 1 := by omega
  simp only [unitRow, List.replicate_succ, e, List.cons_append, List.nil_append]

theorem unitRow_entry (k n i : Nat) (hi : i < n) (hk : k < n) :
    (unitRow k n)[i]?.getD 0 = if i = k then 1 else 0 := by
  induction k generalizing i n with
  | zero =>
    cases i with
    | zero => rfl
    | succ i =>
      have e : unitRow 0 n = 1 :: List.replicate (n - 1) 0 := rfl
      rw [e]
      show (List.replicate (n - 1) (0 : QC))[i]?.getD 0 = 0
      rw [List.getElem?_replicate]
      split
      · rfl
      · rfl
  | succ k ih =>
    rw [unitRow_succ]
    cases i with
    | zero => rfl
    | succ i =>
      rw [List.getElem?_cons_succ, ih (n - 1) i (by omega) (by omega)]
      by_cases h : i = k <;> simp [h]

theorem vsum_zipWith_mul_replicate_zero (m : Nat) (v : List QC) :
    vsum (List.zipWith QC.mul (List.replicate m 0) v) = 0 := by
  induction m generalizing v with
  | zero => cases v <;> rfl
  | succ m ih =>
    cases v with
    | nil => rfl
    | cons x v =>
      show vsum ((0 * x) :: List.zipWith QC.mul (List.replicate m 0) v) = 0
      rw [vsum_cons, QC.zero_mul, ih, QC.add_zero]

theorem dot_unitRow (v : List QC) (k n : Nat) (h : v.length = n) :
    dot (unitRow k n) v = v[k]?.getD 0 := by
  induction k generalizing v n with
  | zero =>
    cases v with
    | nil => rfl
    | cons x v =>
      have e : unitRow 0 n = 1 :: List.replicate (n - 1) 0 := rfl
      rw [e]
      show vsum ((1 * x) :: List.zipWith QC.mul (List.replicate (n - 1) 0) v) = x
      rw [vsum_cons, QC.one_mul, vsum_zipWith_mul_replicate_zero, QC.add_zero]
  | succ k ih =>
    cases v with
    | nil => rfl
    | cons x v =>
      have hv : v.length = n - 1 := by
        rw [List.length_cons] at h
        omega
      rw [unitRow_succ]
      show vsum ((0 * x) :: List.zipWith QC.mul (unitRow k (n - 1)) v) = v[k]?.getD 0
      rw [vsum_cons, QC.zero_mul, QC.zero_add]
      show dot (unitRow k (n - 1)) v = v[k]?.getD 0
      exact ih v (n - 1) hv

theorem dot_unitRow_right (u : List QC) (k n : Nat) (h : u.length = n) :
    dot u (unitRow k n) = u[k]?.getD 0 := by
  rw [dot_comm]
  exact dot_unitRow u k n h

theorem getElem_eq_getD (l : List QC) (i : Nat) (h : i < l.length) :
    l[i]'h = l[i]?.getD 0 := by
  rw [List.getElem?_eq_getElem h, Option.getD_some]

theorem width_eyeM (n : Nat) : width (eyeM n) = n := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [width, eyeM, List.getElem?_map,
      List.getElem?_range (Nat.zero_lt_succ n), Option.map_some,
      Option.getD_some, unitRow_length 0 _ (Nat.zero_lt_succ n)]

theorem rect_eyeM (n : Nat) : Rect (eyeM n) := by
  intro row hrow
  rw [eyeM, List.mem_map] at hrow
  obtain ⟨i, hi, rfl⟩ := hrow
  rw [width_eyeM, unitRow_length i n (List.mem_range.mp hi)]

theorem eyeM_length (n : Nat) : (eyeM n).length = n := by simp [eyeM]

theorem matVec_eye (n : Nat) (v : List QC) (h : v.length = n) :
    matVec (eyeM n) v = v := by
  have hlen : (matVec (eyeM n) v).length = n := by simp [matVec, eyeM]
  apply List.ext_getElem (by rw [hlen, h])
  intro i hi₁ hi₂
  have hi : i < n := by rwa [hlen] at hi₁
  simp only [matVec, eyeM, List.getElem_map,
    List.getElem_range (by rw [List.length_range]; exact hi)]
  rw [dot_unitRow v i n h, List.getElem?_eq_getElem hi₂, Option.getD_some]

theorem entry_eyeM (n i j : Nat) (hi : i < n) (hj : j < n) :
    entry (eyeM n) i j = if j = i then 1 else 0 := by
  have h1 : (eyeM n)[i]? = some (unitRow i n) := by
    rw [eyeM, List.getElem?_map, List.getElem?_range hi]
    rfl
  rw [entry, h1, Option.getD_some, unitRow_entry i n j hj hi]

theorem col_eyeM (n j : Nat) (hj : j < n) : col (eyeM n) j = unitRow j n := by
  apply List.ext_getElem
  · rw [col, eyeM, List.length_map, List.length_map, List.length_range,
      unitRow_length j n hj]
  · intro i hi₁ hi₂
    have hi : i < n := by
      have : (unitRow j n).length = n := unitRow_length j n hj
      omega
    rw [getElem_eq_getD, getElem_eq_getD, col_entry, entry_eyeM n i j hi hj,
      unitRow_entry j n i hi hj]
    by_cases h : i = j
    · simp [h]
    · have h' : ¬ (j = i) := fun hh => h hh.symm
      simp [h, h']

theorem matVec_add (M : List (List QC)) (u v : List QC) (h : u.length = v.length) :
    matVec M (vadd u v) = vadd (matVec M u) (matVec M v) := by
  induction M with
  | nil => rfl
  | cons r M ih =>
    show (dot r (vadd u v)) :: matVec M (vadd u v)
      = (dot r u + dot r v) :: vadd (matVec M u) (matVec M v)
    rw [dot_add_right _ _ _ h, ih]

theorem matVec_smul (M : List (List QC)) (a : QC) (v : List QC) :
    matVec M (vsmul a v) = vsmul a (matVec M v) := by
  induction M with
  | nil => rfl
  | cons r M ih =>
    show (dot r (vsmul a v)) :: matVec M (vsmul a v)
      = (a * dot r v) :: vsmul a (matVec M v)
    rw [dot_smul_right, QC.mul_comm, ih]

theorem width_matMul (X A : List (List QC)) (hX : 0 < X.length) :
    width (matMul X A) = width A := by
  have h1 : (matMul X A)[0]?
      = some ((List.range (width A)).map (fun j => dot (X[0]?.getD []) (col A j))) := by
    rw [matMul, List.getElem?_map]
    have h2 : X[0]? = some (X[0]'(hX)) := List.getElem?_eq_getElem hX
    rw [h2, Option.map_some]
    rfl
  rw [width, h1, Option.getD_some, List.length_map, List.length_range]

theorem rect_matMul (X A : List (List QC)) (hX : 0 < X.length) :
    Rect (matMul X A) := by
  intro row hrow
  rw [matMul, List.mem_map] at hrow
  obtain ⟨r, _, rfl⟩ := hrow
  rw [width_matMul X A hX, List.length_map, List.length_range]

theorem matMul_length (X A : List (List QC)) :
    (matMul X A).length = X.length := by
  rw [matMul, List.length_map]

theorem matMul_eye_left (A : List (List QC)) (hA : Rect A) (n : Nat)
    (hn : A.length = n) : matMul (eyeM n) A = A := by
  cases n with
  | zero =>
    have : A = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [this]
    rfl
  | succ n =>
    have hpos : 0 < (eyeM (n + 1)).length := by
      rw [eyeM, List.length_map, List.length_range]
      exact Nat.succ_pos n
    apply mat_ext _ _ (rect_matMul _ _ hpos) hA
    · rw [matMul_length, eyeM, List.length_map, List.length_range, hn]
    · rw [width_matMul _ _ hpos]
    · intro i j
      by_cases hi : i < A.length
      · by_cases hj : j < width A
        · rw [entry_matMul _ _ i j hj]
          have h1 : (eyeM (n + 1))[i]?.getD [] = unitRow i (n + 1) := by
            have h2 : (eyeM (n + 1))[i]? = some (unitRow i (n + 1)) := by
              rw [eyeM, List.getElem?_map, List.getElem?_range (by omega)]
              rfl
            rw [h2, Option.getD_some]
          have h3 : (col A j).length = n + 1 := by
            rw [col, List.length_map, hn]
          rw [h1, dot_unitRow _ i _ h3, col_entry]
        · rw [entry_eq_zero_of_width_le _ (rect_matMul _ _ hpos) i j
            (by rw [matMul_length, eyeM_length]; omega)
            (by rw [width_matMul _ _ hpos]; omega),
            entry_eq_zero_of_width_le _ hA i j hi (by omega)]
      · rw [entry_eq_zero_of_length_le _ i j
          (by rw [matMul_length, eyeM_length]; omega),
          entry_eq_zero_of_length_le _ i j (by omega)]

theorem matMul_eye_right (A : List (List QC)) (hA : Rect A) :
    matMul A (eyeM (width A)) = A := by
  by_cases hA0 : A.length = 0
  · have : A = [] := List.eq_nil_of_length_eq_zero hA0
    rw [this]
    rfl
  · by_cases hw0 : width A = 0
    · have hrows : ∀ row ∈ A, row = [] := by
        intro row hrow
        have h1 := hA row hrow
        rw [hw0] at h1
        exact List.eq_nil_of_length_eq_zero h1
      have hthis : matMul A (eyeM (width A)) = A.map (fun _ => []) := by
        rw [hw0]
        apply List.map_congr_left
        intro row _
        rfl
      rw [hthis]
      exact (List.map_congr_left
        (fun row hrow => (hrows row hrow).symm)).trans (List.map_id A)
    · have hpos : 0 < A.length := by omega
      apply mat_ext _ _ (rect_matMul _ _ hpos) hA
      · rw [matMul_length]
      · rw [width_matMul _ _ hpos, width_eyeM]
      · intro i j
        by_cases hi : i < A.length
        · by_cases hj : j < width A
          · rw [entry_matMul _ _ i j (by rw [width_eyeM]; exact hj),
              col_eyeM _ j hj,
              dot_unitRow_right _ j _ (by
                rw [List.getElem?_eq_getElem hi, Option.getD_some]
                exact hA _ (List.getElem_mem hi))]
            rfl
          · rw [entry_eq_zero_of_width_le _ (rect_matMul _ _ hpos) i j
              (by rw [matMul_length]; exact hi)
              (by rw [width_matMul _ _ hpos, width_eyeM]; omega),
              entry_eq_zero_of_width_le _ hA i j hi (by omega)]
        · rw [entry_eq_zero_of_length_le _ i j
            (by rw [matMul_length]; omega),
            entry_eq_zero_of_length_le _ i j (by omega)]

theorem width_madd (A B : List (List QC)) (hA : Rect A) (hB : Rect B)
    (hl : A.length = B.length) (hw : width A = width B) :
    width (madd A B) = width A := by
  cases A with
  | nil => rfl
  | cons r A =>
    cases B with
    | nil => simp at hl
    | cons s B =>
      have hr : r.length = width (r :: A) := hA r (by simp)
      have hs : s.length = width (s :: B) := hB s (by simp)
      show ((List.zipWith vadd (r :: A) (s :: B))[0]?.getD []).length
        = width (r :: A)
      show (vadd r s).length = width (r :: A)
      rw [vadd, List.length_zipWith]
      omega

theorem rect_madd (A B : List (List QC)) (hA : Rect A) (hB : Rect B)
    (hl : A.length = B.length) (hw : width A = width B) :
    Rect (madd A B) := by
  intro row hrow
  rw [List.mem_iff_getElem] at hrow
  obtain ⟨i, hi, rfl⟩ := hrow
  have hlen : (madd A B).length = min A.length B.length := by
    rw [madd, List.length_zipWith]
  have hiA : i < A.length := by omega
  have hiB : i < B.length := by omega
  have hz : (madd A B)[i]'hi = vadd (A[i]'hiA) (B[i]'hiB) :=
    List.getElem_zipWith (h := hi)
  rw [width_madd A B hA hB hl hw, hz, vadd, List.length_zipWith,
    hA _ (List.getElem_mem hiA), hB _ (List.getElem_mem hiB), hw, Nat.min_self]

theorem diag_getD (M : List (List QC)) (i : Nat) (hi : i < M.length) :
    (diag M)[i]?.getD 0 = entry M i i := by
  rw [diag, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some]

theorem trace_add (A B : List (List QC)) (hA : Rect A) (hB : Rect B)
    (hl : A.length = B.length) (hw : width A = width B) :
    trace (madd A B) = trace A + trace B := by
  have hlen : (madd A B).length = A.length := by
    rw [madd, List.length_zipWith, hl, Nat.min_self]
  have hdiag : diag (madd A B) = List.zipWith QC.add (diag A) (diag B) := by
    apply List.ext_getElem
    · simp [diag, hlen, hl]
    · intro i hi₁ hi₂
      have hiA : i < A.length := by
        have h1 : (diag (madd A B)).length = A.length := by
          rw [diag, List.length_map, List.length_range, hlen]
        omega
      have hiB : i < B.length := by omega
      rw [List.getElem_zipWith, getElem_eq_getD, getElem_eq_getD, getElem_eq_getD,
        diag_getD _ i (by rw [hlen]; exact hiA), diag_getD _ i hiA,
        diag_getD _ i hiB]
      by_cases hii : i < width A
      · exact entry_add A B i i hiA hiB
          (by rw [hA _ (List.getElem_mem hiA)]; exact hii)
          (by rw [hB _ (List.getElem_mem hiB), ← hw]; exact hii)
      · have e1 : entry (madd A B) i i = 0 :=
          entry_eq_zero_of_width_le _ (rect_madd A B hA hB hl hw) i i
            (by rw [hlen]; exact hiA) (by rw [width_madd A B hA hB hl hw]; omega)
        have e2 : entry A i i = 0 :=
          entry_eq_zero_of_width_le A hA i i hiA (by omega)
        have e3 : entry B i i = 0 :=
          entry_eq_zero_of_width_le B hB i i hiB (by omega)
        rw [e1, e2, e3]
        exact (QC.add_zero 0).symm
  rw [trace, trace, trace, hdiag,
    vsum_zipWith_add _ _ (by
      rw [diag, diag, List.length_map, List.length_map, List.length_range,
        List.length_range, hl])]

theorem QC.re_one : (1 : QC).re = 1 := rfl
theorem QC.im_one : (1 : QC).im = 0 := rfl
theorem QC.re_zero : (0 : QC).re = 0 := rfl
theorem QC.im_zero : (0 : QC).im = 0 := rfl

theorem QC.neg_add (a b : QC) : (-(a + b)) = (-a) + (-b) := by
  apply QC.ext
  · show -(a.re + b.re) = (-a).re + (-b).re; exact Rat.neg_add
  · show -(a.im + b.im) = (-a).im + (-b).im; exact Rat.neg_add

theorem QC.neg_mul (a b : QC) : (-(a * b)) = (-a) * b := by
  apply QC.ext
  · show -(a.re * b.re - a.im * b.im) = (-a.re) * b.re - (-a.im) * b.im; qc_norm
  · show -(a.re * b.im + a.im * b.re) = (-a.re) * b.im + (-a.im) * b.re; qc_norm

theorem QC.mul_neg (a b : QC) : (-(a * b)) = a * (-b) := by
  apply QC.ext
  · show -(a.re * b.re - a.im * b.im) = a.re * (-b.re) - a.im * (-b.im); qc_norm
  · show -(a.re * b.im + a.im * b.re) = a.re * (-b.im) + a.im * (-b.re); qc_norm

theorem QC.neg_neg (a : QC) : (-(-a)) = a :=
  QC.ext (Rat.neg_neg _) (Rat.neg_neg _)

theorem QC.mul_left_comm (a b c : QC) : a * (b * c) = b * (a * c) := by
  rw [← QC.mul_assoc, QC.mul_comm a b, QC.mul_assoc]

/-! ## Two-by-two matrices

For the determinant, the inverse and Cramer's rule it is convenient to
work with a dedicated `2 × 2` record. Its multiplication is the same as
the list `matMul` on `[[a, b], [c, d]]` (proved below), and its
associativity is proved by exact componentwise computation. -/

theorem QC.hadd_eq (a b : QC) : a + b = QC.add a b := rfl
theorem QC.hmul_eq (a b : QC) : a * b = QC.mul a b := rfl
theorem QC.hneg_eq (a : QC) : -a = QC.neg a := rfl
theorem QC.hsub_eq (a b : QC) : a - b = QC.sub a b := rfl

/-- A `2 × 2` matrix `[[a, b], [c, d]]` over `ℚ(i)`. -/
structure M2 where
  a : QC
  b : QC
  c : QC
  d : QC
deriving DecidableEq, Repr

namespace M2

def one : M2 := ⟨1, 0, 0, 1⟩

def mul (M N : M2) : M2 :=
  ⟨M.a * N.a + M.b * N.c, M.a * N.b + M.b * N.d,
   M.c * N.a + M.d * N.c, M.c * N.b + M.d * N.d⟩

def det (M : M2) : QC := M.a * M.d - M.b * M.c

/-- The adjugate inverse: `(1/det) · [[d, -b], [-c, a]]`. -/
def inv (M : M2) : M2 :=
  ⟨M.d * M.det.inv, (-M.b) * M.det.inv, (-M.c) * M.det.inv, M.a * M.det.inv⟩

/-- The matrix as a list of rows. -/
def toMat (M : M2) : List (List QC) := [[M.a, M.b], [M.c, M.d]]

theorem ext {M N : M2} (h1 : M.a = N.a) (h2 : M.b = N.b)
    (h3 : M.c = N.c) (h4 : M.d = N.d) : M = N := by
  cases M; cases N; simp_all

end M2

/-- Unfold the `2 × 2` operations and the scalar operations, then
    normalize the resulting rational identities. -/
macro "m2_norm" : tactic =>
  `(tactic| simp only [QC.hadd_eq, QC.hmul_eq, QC.hsub_eq, QC.hneg_eq,
      M2.mul, M2.det, M2.one, M2.inv, QC.add, QC.mul, QC.sub, QC.neg,
      QC.re_one, QC.im_one, QC.re_zero, QC.im_zero] <;> qc_norm)

/-- Normalize an identity between `ℚ(i)` expressions using the proved
    scalar laws: expand products over sums, then normalize with the
    associative-commutative laws at the scalar level. -/
macro "qc_lvl_norm" : tactic =>
  `(tactic| simp only [M2.mul, M2.det, M2.one, M2.inv,
      QC.sub_eq_add_neg, QC.neg_add, QC.neg_mul, QC.mul_neg,
      QC.neg_neg, QC.add_mul, QC.mul_add, QC.mul_assoc, QC.mul_comm,
      QC.mul_left_comm, QC.add_assoc, QC.add_comm, QC.add_left_comm,
      QC.mul_one, QC.one_mul, QC.mul_zero, QC.zero_mul, QC.add_zero,
      QC.zero_add, QC.add_neg_cancel, QC.neg_add_cancel])

/-! ## Factoring lemmas for the inverse and Cramer's rule

The identities behind `A * A⁻¹ = I` and Cramer's rule are pure
factoring (a common factor `s = (det A)⁻¹` is pulled out); no terms
cancel across the sum. They are proved here once, by `calc` chains of
the scalar laws, and reused for every entry. -/

theorem QC.mul_sub (a b c : QC) : a * (b - c) = a * b - a * c := by
  rw [QC.sub_eq_add_neg b c, QC.mul_add, ← QC.mul_neg a c,
    ← QC.sub_eq_add_neg (a * b) (a * c)]

theorem QC.sub_mul (a b c : QC) : (a - b) * c = a * c - b * c := by
  rw [QC.sub_eq_add_neg a b, QC.add_mul, ← QC.neg_mul b c,
    ← QC.sub_eq_add_neg (a * c) (b * c)]

theorem QC.lin_cancel (X m Y : QC) : X - m + (m - Y) = X - Y := by
  calc X - m + (m - Y)
      = (X + -m) + (m + -Y) := by
        rw [QC.sub_eq_add_neg X m, QC.sub_eq_add_neg m Y]
    _ = X + (-m + (m + -Y)) := by rw [QC.add_assoc X (-m) (m + -Y)]
    _ = X + ((-m + m) + -Y) := by rw [← QC.add_assoc (-m) m (-Y)]
    _ = X + (0 + -Y) := by rw [QC.neg_add_cancel m]
    _ = X + -Y := by rw [QC.zero_add]
    _ = X - Y := by rw [QC.sub_eq_add_neg X Y]

theorem QC.lin_cancel' (P Q R : QC) : (P - Q) + (R - P) = R - Q := by
  calc (P - Q) + (R - P)
      = (P + -Q) + (R + -P) := by
        rw [QC.sub_eq_add_neg P Q, QC.sub_eq_add_neg R P]
    _ = (P + R) + (-Q + -P) := by
        rw [← QC.add_assoc (P + -Q) R (-P), QC.add_assoc P (-Q) R,
          QC.add_comm (-Q) R, ← QC.add_assoc P R (-Q),
          QC.add_assoc (P + R) (-Q) (-P)]
    _ = (P + R) + (-P + -Q) := by rw [QC.add_comm (-Q) (-P)]
    _ = ((P + R) + -P) + -Q := by rw [← QC.add_assoc (P + R) (-P) (-Q)]
    _ = ((P + -P) + R) + -Q := by
        rw [QC.add_assoc P R (-P), QC.add_comm R (-P),
          ← QC.add_assoc P (-P) R]
    _ = (0 + R) + -Q := by rw [QC.add_neg_cancel P]
    _ = R + -Q := by rw [QC.zero_add]
    _ = R - Q := by rw [QC.sub_eq_add_neg R Q]

theorem QC.factor_diag (a b c d s : QC) :
    a * (d * s) + b * ((-c) * s) = (a * d - b * c) * s := by
  calc a * (d * s) + b * ((-c) * s)
      = (a * d) * s + (b * (-c)) * s := by
        rw [← QC.mul_assoc a d s, ← QC.mul_assoc b (-c) s]
    _ = (a * d) * s + (-(b * c)) * s := by rw [← QC.mul_neg b c]
    _ = (a * d + (-(b * c))) * s := by
        rw [QC.add_mul (a * d) (-(b * c)) s]
    _ = (a * d - b * c) * s := by rw [QC.sub_eq_add_neg (a * d) (b * c)]

theorem QC.factor_off (a b s : QC) :
    a * ((-b) * s) + b * (a * s) = 0 := by
  calc a * ((-b) * s) + b * (a * s)
      = (a * (-b)) * s + (b * a) * s := by
        rw [← QC.mul_assoc a (-b) s, ← QC.mul_assoc b a s]
    _ = (-(a * b)) * s + (a * b) * s := by
        rw [← QC.mul_neg a b, QC.mul_comm b a]
    _ = (-(a * b) + (a * b)) * s := by rw [QC.add_mul]
    _ = 0 * s := by rw [QC.neg_add_cancel]
    _ = 0 := QC.zero_mul s

theorem QC.factor_off' (c d s : QC) :
    c * (d * s) + d * ((-c) * s) = 0 := by
  calc c * (d * s) + d * ((-c) * s)
      = (c * d) * s + (d * (-c)) * s := by
        rw [← QC.mul_assoc c d s, ← QC.mul_assoc d (-c) s]
    _ = (c * d) * s + (-(c * d)) * s := by
        rw [← QC.mul_neg d c, QC.mul_comm d c]
    _ = ((c * d) + (-(c * d))) * s := by rw [QC.add_mul]
    _ = 0 * s := by rw [QC.add_neg_cancel]
    _ = 0 := QC.zero_mul s

theorem QC.factor_diag' (a b c d s : QC) :
    c * ((-b) * s) + d * (a * s) = (a * d - b * c) * s := by
  calc c * ((-b) * s) + d * (a * s)
      = (c * (-b)) * s + (d * a) * s := by
        rw [← QC.mul_assoc c (-b) s, ← QC.mul_assoc d a s]
    _ = (-(c * b)) * s + (a * d) * s := by
        rw [← QC.mul_neg c b, QC.mul_comm d a]
    _ = (a * d) * s + (-(c * b)) * s := by
        rw [QC.add_comm ((-(c * b)) * s) ((a * d) * s)]
    _ = (a * d + (-(c * b))) * s := by rw [QC.add_mul]
    _ = (a * d - c * b) * s := by rw [QC.sub_eq_add_neg]
    _ = (a * d - b * c) * s := by rw [QC.mul_comm c b]

theorem QC.factor_diag_left (a b c d s : QC) :
    (d * s) * a + ((-b) * s) * c = (a * d - b * c) * s := by
  calc (d * s) * a + ((-b) * s) * c
      = d * (a * s) + (-b) * (c * s) := by
        rw [QC.mul_assoc d s a, QC.mul_comm s a, QC.mul_assoc (-b) s c,
          QC.mul_comm s c]
    _ = (d * a) * s + ((-b) * c) * s := by
        rw [← QC.mul_assoc d a s, ← QC.mul_assoc (-b) c s]
    _ = (a * d) * s + (-(b * c)) * s := by
        rw [QC.mul_comm d a, ← QC.neg_mul b c]
    _ = (a * d + (-(b * c))) * s := by rw [QC.add_mul]
    _ = (a * d - b * c) * s := by rw [QC.sub_eq_add_neg]

theorem QC.factor_off_left (b d s : QC) :
    (d * s) * b + ((-b) * s) * d = 0 := by
  calc (d * s) * b + ((-b) * s) * d
      = d * (b * s) + (-b) * (d * s) := by
        rw [QC.mul_assoc d s b, QC.mul_comm s b, QC.mul_assoc (-b) s d,
          QC.mul_comm s d]
    _ = (d * b) * s + ((-b) * d) * s := by
        rw [← QC.mul_assoc d b s, ← QC.mul_assoc (-b) d s]
    _ = (d * b) * s + (-(b * d)) * s := by rw [← QC.neg_mul b d]
    _ = (b * d) * s + (-(b * d)) * s := by rw [QC.mul_comm d b]
    _ = ((b * d) + (-(b * d))) * s := by rw [QC.add_mul]
    _ = 0 * s := by rw [QC.add_neg_cancel]
    _ = 0 := QC.zero_mul s

theorem QC.factor_off_left' (a c s : QC) :
    ((-c) * s) * a + (a * s) * c = 0 := by
  calc ((-c) * s) * a + (a * s) * c
      = (-c) * (a * s) + a * (c * s) := by
        rw [QC.mul_assoc (-c) s a, QC.mul_comm s a, QC.mul_assoc a s c,
          QC.mul_comm s c]
    _ = ((-c) * a) * s + (a * c) * s := by
        rw [← QC.mul_assoc (-c) a s, ← QC.mul_assoc a c s]
    _ = (-(a * c)) * s + (a * c) * s := by
        rw [← QC.neg_mul c a, QC.mul_comm c a]
    _ = (-(a * c) + (a * c)) * s := by rw [QC.add_mul]
    _ = 0 * s := by rw [QC.neg_add_cancel]
    _ = 0 := QC.zero_mul s

theorem QC.factor_diag_left' (a b c d s : QC) :
    ((-c) * s) * b + (a * s) * d = (a * d - b * c) * s := by
  calc ((-c) * s) * b + (a * s) * d
      = (-c) * (b * s) + a * (d * s) := by
        rw [QC.mul_assoc (-c) s b, QC.mul_comm s b, QC.mul_assoc a s d,
          QC.mul_comm s d]
    _ = ((-c) * b) * s + (a * d) * s := by
        rw [← QC.mul_assoc (-c) b s, ← QC.mul_assoc a d s]
    _ = (-(c * b)) * s + (a * d) * s := by rw [← QC.neg_mul c b]
    _ = (a * d) * s + (-(c * b)) * s := by
        rw [QC.add_comm ((-(c * b)) * s) ((a * d) * s)]
    _ = (a * d + (-(c * b))) * s := by rw [QC.add_mul]
    _ = (a * d - c * b) * s := by rw [QC.sub_eq_add_neg]
    _ = (a * d - b * c) * s := by rw [QC.mul_comm c b]

namespace M2

theorem mul_one (M : M2) : M.mul one = M := by
  apply ext <;> apply QC.ext <;> m2_norm

theorem one_mul (M : M2) : one.mul M = M := by
  apply ext <;> apply QC.ext <;> m2_norm

theorem mul_assoc (M N P : M2) : (M.mul N).mul P = M.mul (N.mul P) := by
  apply ext <;> qc_lvl_norm

theorem mul_inv (M : M2) (h : M.det.normSq ≠ 0) : M.mul M.inv = one := by
  have hd : M.a * M.d - M.b * M.c = M.det := rfl
  apply ext
  · show M.a * (M.d * M.det.inv) + M.b * ((-M.c) * M.det.inv) = 1
    rw [QC.factor_diag, hd, QC.mul_inv_cancel _ h]
  · show M.a * ((-M.b) * M.det.inv) + M.b * (M.a * M.det.inv) = 0
    exact QC.factor_off _ _ _
  · show M.c * (M.d * M.det.inv) + M.d * ((-M.c) * M.det.inv) = 0
    exact QC.factor_off' _ _ _
  · show M.c * ((-M.b) * M.det.inv) + M.d * (M.a * M.det.inv) = 1
    rw [QC.factor_diag', hd, QC.mul_inv_cancel _ h]

theorem inv_mul (M : M2) (h : M.det.normSq ≠ 0) : M.inv.mul M = one := by
  have hd : M.a * M.d - M.b * M.c = M.det := rfl
  apply ext
  · show (M.d * M.det.inv) * M.a + ((-M.b) * M.det.inv) * M.c = 1
    rw [QC.factor_diag_left, hd, QC.mul_inv_cancel _ h]
  · show (M.d * M.det.inv) * M.b + ((-M.b) * M.det.inv) * M.d = 0
    exact QC.factor_off_left _ _ _
  · show ((-M.c) * M.det.inv) * M.a + (M.a * M.det.inv) * M.c = 0
    exact QC.factor_off_left' _ _ _
  · show ((-M.c) * M.det.inv) * M.b + (M.a * M.det.inv) * M.d = 1
    rw [QC.factor_diag_left', hd, QC.mul_inv_cancel _ h]

/-- Cramer's rule: the displayed `u, v` solve the `2 × 2` system
    `M · (u, v) = (x, y)` whenever `det M ≠ 0`. -/
theorem cramer (M : M2) (x y : QC) (h : M.det.normSq ≠ 0) :
    M.a * ((x * M.d - y * M.b) * M.det.inv)
      + M.b * ((M.a * y - M.c * x) * M.det.inv) = x
    ∧ M.c * ((x * M.d - y * M.b) * M.det.inv)
      + M.d * ((M.a * y - M.c * x) * M.det.inv) = y := by
  have hd : M.a * M.d - M.b * M.c = M.det := rfl
  constructor
  · have e : M.a * ((x * M.d - y * M.b) * M.det.inv)
        + M.b * ((M.a * y - M.c * x) * M.det.inv)
        = (M.det * M.det.inv) * x := by
      calc M.a * ((x * M.d - y * M.b) * M.det.inv)
            + M.b * ((M.a * y - M.c * x) * M.det.inv)
          = (M.a * (x * M.d - y * M.b)) * M.det.inv
            + (M.b * (M.a * y - M.c * x)) * M.det.inv := by
            rw [← QC.mul_assoc M.a (x * M.d - y * M.b) M.det.inv,
              ← QC.mul_assoc M.b (M.a * y - M.c * x) M.det.inv]
        _ = ((M.a * (x * M.d) - M.a * (y * M.b))
            + (M.b * (M.a * y) - M.b * (M.c * x))) * M.det.inv := by
            rw [QC.mul_sub M.a (x * M.d) (y * M.b),
              QC.mul_sub M.b (M.a * y) (M.c * x),
              ← QC.add_mul (M.a * (x * M.d) - M.a * (y * M.b))
                (M.b * (M.a * y) - M.b * (M.c * x)) M.det.inv]
        _ = (((M.a * M.d) * x - (M.a * M.b) * y)
            + ((M.a * M.b) * y - (M.b * M.c) * x)) * M.det.inv := by
            congr 1
            rw [← QC.mul_assoc M.b M.a y, QC.mul_comm M.b M.a,
              QC.mul_comm x M.d, ← QC.mul_assoc M.a M.d x,
              ← QC.mul_assoc M.a y M.b, QC.mul_comm M.a y,
              QC.mul_assoc y M.a M.b, QC.mul_comm y (M.a * M.b),
              ← QC.mul_assoc M.b M.c x]
        _ = ((M.a * M.d) * x - (M.b * M.c) * x) * M.det.inv := by
            rw [QC.lin_cancel]
        _ = ((M.a * M.d - M.b * M.c) * x) * M.det.inv := by
            rw [QC.sub_mul (M.a * M.d) (M.b * M.c) x]
        _ = (M.det * x) * M.det.inv := by rw [← hd]
        _ = (M.det * M.det.inv) * x := by
            rw [QC.mul_assoc M.det x M.det.inv, QC.mul_comm x M.det.inv,
              ← QC.mul_assoc M.det M.det.inv x]
    rw [e, QC.mul_inv_cancel _ h, QC.one_mul]
  · have e : M.c * ((x * M.d - y * M.b) * M.det.inv)
        + M.d * ((M.a * y - M.c * x) * M.det.inv)
        = (M.det * M.det.inv) * y := by
      calc M.c * ((x * M.d - y * M.b) * M.det.inv)
            + M.d * ((M.a * y - M.c * x) * M.det.inv)
          = (M.c * (x * M.d - y * M.b)) * M.det.inv
            + (M.d * (M.a * y - M.c * x)) * M.det.inv := by
            rw [← QC.mul_assoc M.c (x * M.d - y * M.b) M.det.inv,
              ← QC.mul_assoc M.d (M.a * y - M.c * x) M.det.inv]
        _ = ((M.c * (x * M.d) - M.c * (y * M.b))
            + (M.d * (M.a * y) - M.d * (M.c * x))) * M.det.inv := by
            rw [QC.mul_sub M.c (x * M.d) (y * M.b),
              QC.mul_sub M.d (M.a * y) (M.c * x),
              ← QC.add_mul (M.c * (x * M.d) - M.c * (y * M.b))
                (M.d * (M.a * y) - M.d * (M.c * x)) M.det.inv]
        _ = ((x * (M.c * M.d) - M.c * (y * M.b))
            + ((M.a * M.d) * y - x * (M.c * M.d))) * M.det.inv := by
            congr 1
            rw [QC.mul_left_comm M.c x M.d, QC.mul_comm M.c x,
              QC.mul_left_comm M.d x M.c, QC.mul_comm M.d M.c,
              ← QC.mul_assoc M.d M.a y, QC.mul_comm M.d M.a]
        _ = ((M.a * M.d) * y - M.c * (y * M.b)) * M.det.inv := by
            rw [QC.lin_cancel']
        _ = ((M.a * M.d) * y - (M.b * M.c) * y) * M.det.inv := by
            rw [QC.mul_left_comm M.c y M.b, QC.mul_comm M.c M.b,
              QC.mul_comm y (M.b * M.c)]
        _ = ((M.a * M.d - M.b * M.c) * y) * M.det.inv := by
            rw [QC.sub_mul (M.a * M.d) (M.b * M.c) y]
        _ = (M.det * y) * M.det.inv := by rw [← hd]
        _ = (M.det * M.det.inv) * y := by
            rw [QC.mul_assoc M.det y M.det.inv, QC.mul_comm y M.det.inv,
              ← QC.mul_assoc M.det M.det.inv y]
    rw [e, QC.mul_inv_cancel _ h, QC.one_mul]

end M2

/-! ## Bridges to the list matrices, Pauli matrices, and order 3 -/

/-- The list `matMul` on `2 × 2` matrices, entry by entry. -/
theorem matMul_two (a b c d e f g h : QC) :
    matMul [[a, b], [c, d]] [[e, f], [g, h]]
      = [[a * e + b * g, a * f + b * h], [c * e + d * g, c * f + d * h]] := by
  simp [matMul, col, dot, width, vsum, QC.zero_add, QC.add_zero]
  simp only [List.range_succ, List.range_zero, List.map_append,
    List.map_cons, List.map_nil, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, QC.hadd_eq, QC.hmul_eq,
    List.cons_append, List.nil_append, List.cons.injEq, and_true, true_and]

/-- `M2.mul` is the list `matMul` on the rows. -/
theorem M2.toMat_mul (M N : M2) :
    (M.mul N).toMat = matMul M.toMat N.toMat := by
  show [[M.a * N.a + M.b * N.c, M.a * N.b + M.b * N.d],
        [M.c * N.a + M.d * N.c, M.c * N.b + M.d * N.d]]
      = matMul [[M.a, M.b], [M.c, M.d]] [[N.a, N.b], [N.c, N.d]]
  rw [matMul_two]

/-- Associativity of the list `matMul` for `2 × 2` matrices. -/
theorem matMul_assoc_two (A B C : M2) :
    matMul (matMul A.toMat B.toMat) C.toMat
      = matMul A.toMat (matMul B.toMat C.toMat) := by
  rw [← M2.toMat_mul, ← M2.toMat_mul, ← M2.toMat_mul, ← M2.toMat_mul,
    M2.mul_assoc]

/-- The Pauli matrices and the phase matrix `S`, over `ℚ(i)`. -/
def pauliX : M2 := ⟨0, 1, 1, 0⟩
def pauliY : M2 := ⟨0, -QC.eye, QC.eye, 0⟩
def pauliZ : M2 := ⟨1, 0, 0, -1⟩
def phaseS : M2 := ⟨1, 0, 0, QC.eye⟩

theorem pauliX_mul_self : pauliX.mul pauliX = M2.one := by
  apply M2.ext <;> apply QC.ext <;>
    simp only [pauliX, M2.mul, M2.one, QC.hadd_eq, QC.hmul_eq, QC.hsub_eq,
      QC.hneg_eq, QC.add, QC.mul, QC.sub, QC.neg, QC.re_one, QC.im_one,
      QC.re_zero, QC.im_zero] <;> qc_norm

theorem pauliY_mul_self : pauliY.mul pauliY = M2.one := by
  apply M2.ext <;> apply QC.ext <;>
    simp only [pauliY, QC.eye, M2.mul, M2.one, QC.hadd_eq, QC.hmul_eq,
      QC.hsub_eq, QC.hneg_eq, QC.add, QC.mul, QC.sub, QC.neg, QC.re_one,
      QC.im_one, QC.re_zero, QC.im_zero] <;> qc_norm

theorem pauliZ_mul_self : pauliZ.mul pauliZ = M2.one := by
  apply M2.ext <;> apply QC.ext <;>
    simp only [pauliZ, M2.mul, M2.one, QC.hadd_eq, QC.hmul_eq, QC.hsub_eq,
      QC.hneg_eq, QC.add, QC.mul, QC.sub, QC.neg, QC.re_one, QC.im_one,
      QC.re_zero, QC.im_zero] <;> qc_norm

theorem phaseS_mul_self : phaseS.mul phaseS = pauliZ := by
  apply M2.ext <;> apply QC.ext <;>
    simp only [phaseS, pauliZ, QC.eye, M2.mul, QC.hadd_eq, QC.hmul_eq,
      QC.hsub_eq, QC.hneg_eq, QC.add, QC.mul, QC.sub, QC.neg, QC.re_one,
      QC.im_one, QC.re_zero, QC.im_zero] <;> qc_norm

/-- A `3 × 3` matrix over `ℚ(i)`, for the determinant of order 3. -/
structure M3 where
  a : QC
  b : QC
  c : QC
  d : QC
  e : QC
  f : QC
  g : QC
  h : QC
  i : QC
deriving DecidableEq, Repr

namespace M3

/-- The determinant of order 3 (first-row cofactor expansion). -/
def det (M : M3) : QC :=
  M.a * (M.e * M.i - M.f * M.h) - M.b * (M.d * M.i - M.f * M.g)
    + M.c * (M.d * M.h - M.e * M.g)

def one : M3 := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩

theorem det_one : one.det = 1 := by
  apply QC.ext <;> simp only [det, one, QC.hadd_eq, QC.hmul_eq, QC.hsub_eq,
    QC.add, QC.mul, QC.sub, QC.re_one, QC.im_one, QC.re_zero, QC.im_zero] <;>
    qc_norm

end M3
