/-
# PolyCore — Exact Polynomial Arithmetic over the Rationals

Polynomials with rational coefficients, in a fully discrete, exact form,
designed to be used on digital machines.

A polynomial is a list of rational coefficients in ascending order of
degree: `[a₀, a₁, a₂]` reads as `a₀ + a₁·X + a₂·X²`. Every operation is
exact rational arithmetic — no floating point, no rounding anywhere — so
the whole development runs as-is on a digital computer (the companion
`poly.py` runs the same structure).

This file proves, as theorems in core Lean (no Mathlib, no `sorry`):

* The additive laws: `add` is commutative and associative, with `[]` as
  its identity on both sides.
* Scalar multiplication distributes over polynomial addition on both
  sides, composes as `a • (b • p) = (a·b) • p`, and `1 • p = p`.
* Multiplication (defined by recursion on the left factor, through
  scalar multiplication and the shift `· * X`) distributes over
  addition on both sides and satisfies `p * [1] = p`; `p * 0` is the
  all-zero list of length `p.length`.
* Evaluation at a rational point is a homomorphism on the nose:
  `eval x (p + q) = eval x p + eval x q`,
  `eval x (c • p) = c * eval x p`, `eval x (p * X) = x * eval x p`, and
  `eval x (p * q) = eval x p * eval x q`.
* The formal derivative satisfies `deriv (p + q) = deriv p + deriv q`
  and `deriv (c • p) = c • deriv p`.

Commutativity and associativity of multiplication, the product rule
for the derivative, and the numeric examples are verified
computationally in `poly.py` (exact rational arithmetic, random
tests); Lean proofs of those identities are not included. The list
representation does not identify trailing zeros syntactically
(`[0] ≠ []`), which is what makes the syntactic forms of those laws
fail; they hold semantically — for commutativity, `eval_mul_comm`
below proves that the values of `p * q` and `q * p` agree at every
point.

Author: Takeo Yamamoto
License: Apache-2.0
-/

namespace PolyCore

/-- A polynomial with rational coefficients, in ascending order of
    degree: the head is the constant term. -/
abbrev Poly := List Rat

/-! ## Rational normalization

Component identities in `ℚ` are proved by normalizing with the
commutative-ring lemmas of core `Rat` (the same idiom as LinearCore). -/

theorem rat_mul_left_comm (a b c : Rat) : a * (b * c) = b * (a * c) := by
  rw [← Rat.mul_assoc, Rat.mul_comm a b, Rat.mul_assoc]

macro "rat_norm" : tactic =>
  `(tactic| simp only [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_neg,
      Rat.neg_mul, Rat.neg_add, Rat.neg_neg, Rat.neg_zero, Rat.mul_assoc, Rat.mul_comm, rat_mul_left_comm,
      Rat.add_assoc, Rat.add_comm, Rat.add_left_comm, Rat.mul_one, Rat.one_mul,
      Rat.mul_zero, Rat.zero_mul, Rat.add_zero, Rat.zero_add, Rat.add_neg_cancel,
      Rat.neg_add_cancel])

/-! ## Addition -/

/-- Polynomial addition, pointwise, with the shorter side padded by
    zeros (a missing coefficient is a zero coefficient). -/
def add : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

theorem nil_add (q : Poly) : add [] q = q := rfl

theorem add_nil (p : Poly) : add p [] = p := by
  cases p <;> rfl

theorem add_cons_cons (a : Rat) (p : Poly) (b : Rat) (q : Poly) :
    add (a :: p) (b :: q) = (a + b) :: add p q := rfl

theorem add_comm (p q : Poly) : add p q = add q p := by
  induction p generalizing q with
  | nil => cases q <;> rfl
  | cons a p ih =>
    cases q with
    | nil => rfl
    | cons b q =>
      show (a + b) :: add p q = (b + a) :: add q p
      rw [Rat.add_comm a b, ih]

theorem add_assoc (p q r : Poly) : add (add p q) r = add p (add q r) := by
  induction p generalizing q r with
  | nil => cases q <;> cases r <;> rfl
  | cons a p ih =>
    cases q with
    | nil => cases r <;> rfl
    | cons b q =>
      cases r with
      | nil => rfl
      | cons c r =>
        show ((a + b) + c) :: add (add p q) r = (a + (b + c)) :: add p (add q r)
        rw [Rat.add_assoc, ih]

/-- The additive inverse, coefficient by coefficient. -/
def neg (p : Poly) : Poly := p.map (fun a => -a)

theorem neg_cons (a : Rat) (p : Poly) : neg (a :: p) = (-a) :: neg p := rfl

/-- `p + (-p)` is the all-zero list of the same length: the list
    representation keeps the length, so this is the exact form of the
    cancellation law. -/
theorem add_neg (p : Poly) : add p (neg p) = List.replicate p.length 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    show (a + -a) :: add p (neg p) = 0 :: List.replicate p.length 0
    rw [Rat.add_neg_cancel, ih]

/-! ## Scalar multiplication and the shift -/

/-- Multiply every coefficient by the scalar `c`. -/
def smul (c : Rat) (p : Poly) : Poly := p.map (c * ·)

theorem smul_cons (c a : Rat) (p : Poly) : smul c (a :: p) = (c * a) :: smul c p := rfl

theorem smul_nil (c : Rat) : smul c [] = [] := rfl

/-- Multiplication by `X`: a zero constant term is pushed in front. -/
def shift (p : Poly) : Poly := 0 :: p

theorem smul_add (c : Rat) (p q : Poly) :
    smul c (add p q) = add (smul c p) (smul c q) := by
  induction p generalizing q with
  | nil => cases q <;> rfl
  | cons a p ih =>
    cases q with
    | nil => rfl
    | cons b q =>
      show (c * (a + b)) :: smul c (add p q) = (c * a + c * b) :: add (smul c p) (smul c q)
      rw [Rat.mul_add, ih]

theorem add_smul (a b : Rat) (p : Poly) :
    smul (a + b) p = add (smul a p) (smul b p) := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    show ((a + b) * c) :: smul (a + b) p = (a * c + b * c) :: add (smul a p) (smul b p)
    rw [Rat.add_mul, ih]

theorem smul_smul (a b : Rat) (p : Poly) :
    smul a (smul b p) = smul (a * b) p := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    show (a * (b * c)) :: smul a (smul b p) = ((a * b) * c) :: smul (a * b) p
    rw [Rat.mul_assoc, ih]

theorem smul_one (p : Poly) : smul 1 p = p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    show (1 * a) :: smul 1 p = a :: p
    rw [Rat.one_mul, ih]

theorem smul_shift (c : Rat) (p : Poly) : smul c (shift p) = shift (smul c p) := by
  show (c * 0) :: smul c p = 0 :: smul c p
  rw [Rat.mul_zero]

theorem smul_neg (c : Rat) (p : Poly) : smul c (neg p) = neg (smul c p) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    show (c * -a) :: smul c (neg p) = (-(c * a)) :: neg (smul c p)
    rw [Rat.mul_neg, ih]

/-! ## Multiplication -/

/-- Polynomial multiplication, by recursion on the left factor:
    `(a + X·p) * q = a • q + X · (p * q)`. -/
def mul : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => add (smul a q) (shift (mul p q))

theorem mul_nil (q : Poly) : mul [] q = [] := rfl

theorem mul_cons (a : Rat) (p q : Poly) :
    mul (a :: p) q = add (smul a q) (shift (mul p q)) := rfl

/-- `p * 0` is the all-zero list of length `p.length` (the list
    representation keeps the factors' lengths, so this — not `[]` —
    is the exact form of the law). -/
theorem mul_zero (p : Poly) : mul p [] = List.replicate p.length 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [mul_cons, smul_nil, ih]
    rfl

theorem mul_one (p : Poly) : mul p [1] = p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    show add (smul a [1]) (shift (mul p [1])) = a :: p
    rw [ih]
    show (a * 1 + 0) :: p = a :: p
    rw [Rat.mul_one, Rat.add_zero]

theorem mul_smul (c : Rat) (p q : Poly) : mul (smul c p) q = smul c (mul p q) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    show add (smul (c * a) q) (shift (mul (smul c p) q)) = smul c (add (smul a q) (shift (mul p q)))
    rw [ih, smul_add, smul_shift, smul_smul]

theorem smul_mul (c : Rat) (p q : Poly) : mul p (smul c q) = smul c (mul p q) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    show add (smul a (smul c q)) (shift (mul p (smul c q))) = smul c (add (smul a q) (shift (mul p q)))
    rw [ih, smul_add, smul_shift, smul_smul a c q, smul_smul c a q, Rat.mul_comm a c]

theorem shift_add (u v : Poly) : shift (add u v) = add (shift u) (shift v) := by
  show (0 : Rat) :: add u v = (0 + 0) :: add u v
  rw [Rat.add_zero]

theorem add_comm_mid (a b c d : Poly) :
    add (add a b) (add c d) = add (add a c) (add b d) := by
  rw [add_assoc a b (add c d), ← add_assoc b c d, add_comm b c, add_assoc c b d,
    ← add_assoc a c (add b d)]

/-- Multiplication distributes over addition in the right factor. -/
theorem mul_add (p q r : Poly) : mul p (add q r) = add (mul p q) (mul p r) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    show add (smul a (add q r)) (shift (mul p (add q r)))
        = add (add (smul a q) (shift (mul p q))) (add (smul a r) (shift (mul p r)))
    rw [smul_add, ih, shift_add, add_comm_mid]

/-- Multiplication distributes over addition in the left factor. -/
theorem add_mul (p q r : Poly) : mul (add p q) r = add (mul p r) (mul q r) := by
  induction p generalizing q with
  | nil => cases q <;> rfl
  | cons a p ih =>
    cases q with
    | nil => rw [add_nil, mul_nil, add_nil]
    | cons b q =>
      show add (smul (a + b) r) (shift (mul (add p q) r))
          = add (add (smul a r) (shift (mul p r))) (add (smul b r) (shift (mul q r)))
      rw [add_smul, ih, shift_add, add_comm_mid]

/-! ## Evaluation -/

/-- Evaluate a polynomial at a rational point, by Horner's rule from
    the constant term up. -/
def eval (x : Rat) : Poly → Rat
  | [] => 0
  | a :: p => a + x * eval x p

theorem eval_nil (x : Rat) : eval x [] = 0 := rfl

theorem eval_cons (x a : Rat) (p : Poly) : eval x (a :: p) = a + x * eval x p := rfl

theorem eval_replicate_zero (x : Rat) (n : Nat) :
    eval x (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (0 : Rat) + x * eval x (List.replicate n 0) = 0
    rw [ih]
    rat_norm

theorem eval_add (x : Rat) (p q : Poly) :
    eval x (add p q) = eval x p + eval x q := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => show (0 : Rat) = 0 + 0; rat_norm
    | cons b q => show b + x * eval x q = 0 + (b + x * eval x q); rw [Rat.zero_add]
  | cons a p ih =>
    cases q with
    | nil => show a + x * eval x p = (a + x * eval x p) + 0; rw [Rat.add_zero]
    | cons b q =>
      show (a + b) + x * eval x (add p q) = (a + x * eval x p) + (b + x * eval x q)
      rw [ih]
      rat_norm

theorem eval_neg (x : Rat) (p : Poly) : eval x (neg p) = - eval x p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    show (-a) + x * eval x (neg p) = - (a + x * eval x p)
    rw [ih]
    rat_norm

theorem eval_smul (x c : Rat) (p : Poly) : eval x (smul c p) = c * eval x p := by
  induction p with
  | nil => show (0 : Rat) = c * 0; rw [Rat.mul_zero]
  | cons a p ih =>
    show (c * a) + x * eval x (smul c p) = c * (a + x * eval x p)
    rw [ih]
    rat_norm

theorem eval_shift (x : Rat) (p : Poly) : eval x (shift p) = x * eval x p := by
  show (0 : Rat) + x * eval x p = x * eval x p
  rw [Rat.zero_add]

/-- Evaluation is multiplicative: the values of a product are the
    product of the values. This is the theorem that makes the list
    multiplication above the polynomial multiplication. -/
theorem eval_mul (x : Rat) (p q : Poly) :
    eval x (mul p q) = eval x p * eval x q := by
  induction p generalizing q with
  | nil => show (0 : Rat) = 0 * eval x q; rw [Rat.zero_mul]
  | cons a p ih =>
    show eval x (add (smul a q) (shift (mul p q))) = (a + x * eval x p) * eval x q
    rw [eval_add, eval_smul, eval_shift, ih]
    rat_norm

/-- Semantic commutativity of multiplication: at every point, the
    values of `p * q` and `q * p` agree. (Syntactic commutativity of
    the lists themselves fails by trailing zeros — `[0] ≠ []` — and is
    verified computationally in `poly.py`; see the file header.) -/
theorem eval_mul_comm (x : Rat) (p q : Poly) :
    eval x (mul p q) = eval x (mul q p) := by
  rw [eval_mul, eval_mul, Rat.mul_comm]

theorem eval_one_mul (x : Rat) (q : Poly) : eval x (mul [1] q) = eval x q := by
  rw [eval_mul]
  show (1 + x * 0) * eval x q = eval x q
  rat_norm

/-! ## The formal derivative -/

/-- Auxiliary for the derivative: `derivAux n p` differentiates the
    tail whose head has degree `n + 1`. -/
def derivAux : Nat → Poly → Poly
  | _, [] => []
  | n, a :: p => ((n + 1 : Nat) : Rat) * a :: derivAux (n + 1) p

/-- The formal derivative: `deriv (a₀ + a₁X + a₂X² + …)
    = a₁ + 2a₂X + …`. -/
def deriv : Poly → Poly
  | [] => []
  | _ :: p => derivAux 0 p

theorem derivAux_add (n : Nat) (p q : Poly) :
    derivAux n (add p q) = add (derivAux n p) (derivAux n q) := by
  induction p generalizing q n with
  | nil => cases q <;> rfl
  | cons a p ih =>
    cases q with
    | nil => rfl
    | cons b q =>
      show ((n + 1 : Nat) : Rat) * (a + b) :: derivAux (n + 1) (add p q)
          = (((n + 1 : Nat) : Rat) * a + ((n + 1 : Nat) : Rat) * b)
            :: add (derivAux (n + 1) p) (derivAux (n + 1) q)
      rw [Rat.mul_add, ih]

theorem deriv_add (p q : Poly) : deriv (add p q) = add (deriv p) (deriv q) := by
  cases p with
  | nil => cases q <;> rfl
  | cons a p =>
    cases q with
    | nil =>
      have h : deriv ([] : Poly) = [] := rfl
      rw [h, add_nil (a :: p), add_nil (deriv (a :: p))]
    | cons b q =>
      show derivAux 0 (add p q) = add (derivAux 0 p) (derivAux 0 q)
      exact derivAux_add 0 p q

theorem derivAux_smul (n : Nat) (c : Rat) (p : Poly) :
    derivAux n (smul c p) = smul c (derivAux n p) := by
  induction p generalizing n with
  | nil => rfl
  | cons a p ih =>
    have h : ((n + 1 : Nat) : Rat) * (c * a) = c * (((n + 1 : Nat) : Rat) * a) := by
      rw [← Rat.mul_assoc, Rat.mul_comm (((n + 1 : Nat) : Rat)) c, Rat.mul_assoc]
    show ((n + 1 : Nat) : Rat) * (c * a) :: derivAux (n + 1) (smul c p)
        = (c * (((n + 1 : Nat) : Rat) * a)) :: smul c (derivAux (n + 1) p)
    rw [h, ih]

theorem deriv_smul (c : Rat) (p : Poly) : deriv (smul c p) = smul c (deriv p) := by
  cases p with
  | nil => rfl
  | cons a p =>
    show derivAux 0 (smul c p) = smul c (derivAux 0 p)
    exact derivAux_smul 0 c p

end PolyCore
