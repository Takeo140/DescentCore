#!/usr/bin/env python3
"""PolyCore — companion executable for PolyCore.lean.

The same structure as the Lean file, in exact rational arithmetic
(Python fractions): polynomials are lists of coefficients in
ascending order of degree.

It verifies computationally what PolyCore.lean states honestly as
not proved in Lean:

* commutativity and associativity of multiplication,
* the product rule for the formal derivative,
* the numeric examples (evaluation, a product, a derivative),

and cross-checks the Lean-proved laws (additive laws, both
distributivities, the evaluation homomorphism, the derivative of a
sum) on random inputs. Equalities that the list representation only
satisfies up to trailing zeros are compared after trimming.

Author: Takeo Yamamoto
License: Apache-2.0
"""

import random
from fractions import Fraction


def trim(p):
    """Strip trailing zero coefficients."""
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def add(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else Fraction(0)) + (q[i] if i < len(q) else Fraction(0))
            for i in range(n)]


def neg(p):
    return [-a for a in p]


def smul(c, p):
    return [c * a for a in p]


def shift(p):
    return [Fraction(0)] + list(p)


def mul(p, q):
    # The Lean definition, verbatim: recursion on the left factor.
    if not p:
        return []
    return add(smul(p[0], q), shift(mul(p[1:], q)))


def eval_at(x, p):
    # Horner from the constant term up, as in the Lean file.
    if not p:
        return Fraction(0)
    return p[0] + x * eval_at(x, p[1:])


def deriv(p):
    return [Fraction(i + 1) * p[i + 1] for i in range(len(p) - 1)] if p else []


def rand_poly(rng, max_len=5, max_num=5, max_den=3):
    n = rng.randrange(0, max_len + 1)
    return [Fraction(rng.randrange(-max_num, max_num + 1),
                     rng.randrange(1, max_den + 1)) for _ in range(n)]


def main():
    rng = random.Random(20261124)
    trials = 400

    for _ in range(trials):
        p, q, r = rand_poly(rng), rand_poly(rng), rand_poly(rng)
        c = Fraction(rng.randrange(-4, 5), rng.randrange(1, 4))
        x = Fraction(rng.randrange(-3, 4), rng.randrange(1, 3))

        # Lean-proved laws, cross-checked.
        assert add(p, q) == add(q, p)
        assert add(add(p, q), r) == add(p, add(q, r))
        assert add(p, neg(p)) == [Fraction(0)] * len(p)
        assert smul(c, add(p, q)) == add(smul(c, p), smul(c, q))
        assert mul(p, add(q, r)) == add(mul(p, q), mul(p, r))
        assert mul(add(p, q), r) == add(mul(p, r), mul(q, r))
        assert mul(p, [Fraction(1)]) == p
        assert eval_at(x, add(p, q)) == eval_at(x, p) + eval_at(x, q)
        assert eval_at(x, smul(c, p)) == c * eval_at(x, p)
        assert eval_at(x, mul(p, q)) == eval_at(x, p) * eval_at(x, q)
        assert trim(deriv(add(p, q))) == trim(add(deriv(p), deriv(q)))
        assert trim(deriv(smul(c, p))) == trim(smul(c, deriv(p)))

        # Verified here only (not proved in Lean): up to trailing zeros.
        assert trim(mul(p, q)) == trim(mul(q, p)), "mul comm"
        assert trim(mul(mul(p, q), r)) == trim(mul(p, mul(q, r))), "mul assoc"
        assert trim(deriv(mul(p, q))) == trim(add(mul(deriv(p), q), mul(p, deriv(q)))), \
            "deriv product rule"
        assert trim(mul([Fraction(1)], q)) == trim(q), "one_mul"

    # The numeric examples (exact, no trimming needed).
    assert eval_at(Fraction(2), [Fraction(1), Fraction(2), Fraction(3)]) == 17
    assert eval_at(Fraction(3), mul([Fraction(1), Fraction(1)],
                                    [Fraction(1), Fraction(1)])) == 16
    assert deriv([Fraction(1), Fraction(2), Fraction(3)]) == [Fraction(2), Fraction(6)]

    print(f"poly.py: all checks passed ({trials} random trials + examples)")


if __name__ == "__main__":
    main()
