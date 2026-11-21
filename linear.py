#!/usr/bin/env python3
"""Discrete complex linear algebra over the Gaussian rationals Q(i).

The companion implementation of LinearCore.lean: scalars are pairs of
fractions (re, im) read as re + i*im, vectors are lists of scalars,
matrices are lists of rows, and every operation is exact rational
arithmetic (fractions.Fraction) -- no floating point anywhere.

Provides: scalar field arithmetic, vector operations, the inner
product, matrix operations (add, multiply, transpose, conjugate
transpose, trace, determinant and inverse by exact Gaussian
elimination over Q(i)), and exact solving of linear systems.

Run directly to execute the self-checks.
"""

from fractions import Fraction


class QC:
    """A Gaussian rational re + i*im with rational components."""

    __slots__ = ("re", "im")

    def __init__(self, re=0, im=0):
        self.re = Fraction(re)
        self.im = Fraction(im)

    def __repr__(self):
        return f"QC({self.re}, {self.im})"

    def __eq__(self, other):
        return self.re == other.re and self.im == other.im

    def __hash__(self):
        return hash((self.re, self.im))

    def __add__(self, other):
        return QC(self.re + other.re, self.im + other.im)

    def __neg__(self):
        return QC(-self.re, -self.im)

    def __sub__(self, other):
        return QC(self.re - other.re, self.im - other.im)

    def __mul__(self, other):
        return QC(self.re * other.re - self.im * other.im,
                  self.re * other.im + self.im * other.re)

    def conj(self):
        return QC(self.re, -self.im)

    def norm_sq(self):
        return self.re * self.re + self.im * self.im

    def inv(self):
        d = self.norm_sq()
        if d == 0:
            raise ZeroDivisionError("inverse of zero scalar")
        return QC(self.re / d, -self.im / d)

    def __truediv__(self, other):
        return self * other.inv()

    def is_zero(self):
        return self.re == 0 and self.im == 0


ZERO = QC(0)
ONE = QC(1)
EYE = QC(0, 1)


# --- vectors -------------------------------------------------------------

def vadd(u, v):
    return [a + b for a, b in zip(u, v)]


def vsmul(a, u):
    return [a * x for x in u]


def dot(u, v):
    s = ZERO
    for a, b in zip(u, v):
        s = s + a * b
    return s


def dotc(u, v):
    """Inner product, conjugate-linear in the first argument."""
    s = ZERO
    for a, b in zip(u, v):
        s = s + a.conj() * b
    return s


# --- matrices ------------------------------------------------------------

def madd(A, B):
    return [vadd(r, s) for r, s in zip(A, B)]


def transpose(M):
    if not M:
        return []
    return [list(col) for col in zip(*M)]


def conj_transpose(M):
    return [[x.conj() for x in row] for row in transpose(M)]


def mat_vec(M, v):
    return [dot(row, v) for row in M]


def mat_mul(A, B):
    Bt = transpose(B)
    return [[dot(row, col) for col in Bt] for row in A]


def eye(n):
    return [[ONE if i == j else ZERO for j in range(n)] for i in range(n)]


def trace(M):
    s = ZERO
    for i in range(len(M)):
        s = s + M[i][i]
    return s


def rref(M):
    """Reduced row echelon form over Q(i), by exact Gauss-Jordan."""
    A = [row[:] for row in M]
    rows = len(A)
    cols = len(A[0]) if rows else 0
    pivots = []
    r = 0
    for c in range(cols):
        if r >= rows:
            break
        piv = None
        for i in range(r, rows):
            if not A[i][c].is_zero():
                piv = i
                break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(rows):
            if i != r and not A[i][c].is_zero():
                factor = A[i][c]
                A[i] = [x - factor * y for x, y in zip(A[i], A[r])]
        pivots.append(c)
        r += 1
    return A, pivots


def det(M):
    """Determinant over Q(i), by exact Gaussian elimination."""
    n = len(M)
    A = [row[:] for row in M]
    d = ONE
    for c in range(n):
        piv = None
        for i in range(c, n):
            if not A[i][c].is_zero():
                piv = i
                break
        if piv is None:
            return ZERO
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            d = -d
        pv = A[c][c]
        d = d * pv
        for i in range(c + 1, n):
            if not A[i][c].is_zero():
                factor = A[i][c] / pv
                A[i] = [x - factor * y for x, y in zip(A[i], A[c])]
    return d


def inverse(M):
    """Inverse by Gauss-Jordan on the augmented matrix; None if singular."""
    n = len(M)
    A = [row[:] + e for row, e in zip(M, eye(n))]
    R, pivots = rref(A)
    if pivots != list(range(n)):
        return None
    return [row[n:] for row in R]


def solve(A, b):
    """Solve A x = b exactly over Q(i); None if there is no unique solution."""
    n = len(A)
    M = [row[:] + [bb] for row, bb in zip(A, b)]
    R, pivots = rref(M)
    if pivots != list(range(n)):
        return None
    return [R[i][n] for i in range(n)]


# --- self-checks -----------------------------------------------------------

def _self_check():
    import random

    # scalar field laws on random Gaussian rationals
    def rand_qc():
        return QC(Fraction(random.randint(-5, 5), random.randint(1, 4)),
                  Fraction(random.randint(-5, 5), random.randint(1, 4)))

    for _ in range(200):
        a, b, c = rand_qc(), rand_qc(), rand_qc()
        assert a + b == b + a
        assert (a + b) + c == a + (b + c)
        assert a * b == b * a
        assert (a * b) * c == a * (b * c)
        assert a * (b + c) == a * b + a * c
        assert (a * a.conj()).im == 0
        assert (a * a.conj()).re == a.norm_sq()
        if not a.is_zero():
            assert a * a.inv() == ONE
            assert a.inv() * a == ONE

    # Pauli matrices over Q(i)
    X = [[ZERO, ONE], [ONE, ZERO]]
    Y = [[ZERO, -EYE], [EYE, ZERO]]
    Z = [[ONE, ZERO], [ZERO, -ONE]]
    S = [[ONE, ZERO], [ZERO, EYE]]
    I2 = eye(2)
    assert mat_mul(X, X) == I2
    assert mat_mul(Y, Y) == I2
    assert mat_mul(Z, Z) == I2
    assert mat_mul(S, S) == Z
    assert det(X) == -ONE
    assert det(S) == EYE

    # random matrices: associativity, det of product, inverse, solving
    def rand_mat(n):
        return [[rand_qc() for _ in range(n)] for _ in range(n)]

    for n in (2, 3, 4):
        for _ in range(30):
            A, B, C = rand_mat(n), rand_mat(n), rand_mat(n)
            assert mat_mul(mat_mul(A, B), C) == mat_mul(A, mat_mul(B, C))
            assert det(mat_mul(A, B)) == det(A) * det(B)
            assert transpose(transpose(A)) == A
            assert conj_transpose(conj_transpose(A)) == A
            assert trace(madd(A, B)) == trace(A) + trace(B)
            Ainv = inverse(A)
            if Ainv is not None:
                assert mat_mul(A, Ainv) == eye(n)
                assert mat_mul(Ainv, A) == eye(n)
                b = [rand_qc() for _ in range(n)]
                x = solve(A, b)
                assert x is not None
                assert mat_vec(A, x) == b

    # inner product: self inner product is a nonnegative rational scalar
    for _ in range(50):
        v = [rand_qc() for _ in range(5)]
        w = dotc(v, v)
        assert w.im == 0
        assert w.re == sum(x.norm_sq() for x in v)

    print("linear.py: all self-checks passed")


if __name__ == "__main__":
    _self_check()
