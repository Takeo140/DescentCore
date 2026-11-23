#!/usr/bin/env python3
"""NewAI — companion executable for NewAI.lean.

The same design as the Lean blueprint, for the worked example: a
self-correcting weight vector. One round of self-improvement halves
every weight; the defect is the total weight; settling runs `defect`
rounds.

It cross-checks the blueprint's guarantees on random inputs:
settling reaches total weight zero within the defect bound, the
settled vector is all zeros and a fixed point, the defect never
increases, and the accelerated design (operator applied twice per
round) matches the original at twice the rounds — the properties
NewAI.lean proves as theorems.

Author: Takeo Yamamoto
License: Apache-2.0
"""

import random


def improve(weights):
    return [w // 2 for w in weights]


def defect(weights):
    return sum(weights)


def iterate(f, n, s):
    for _ in range(n):
        s = f(s)
    return s


def settle(weights):
    return iterate(improve, defect(weights), weights)


def main():
    rng = random.Random(20261124)
    trials = 500

    for _ in range(trials):
        n = rng.randrange(0, 7)
        weights = [rng.randrange(0, 64) for _ in range(n)]

        settled = settle(weights)
        assert defect(settled) == 0, (weights, settled)
        assert all(w == 0 for w in settled)
        assert improve(settled) == settled

        # Monotonicity along the run.
        s = weights
        prev = defect(s)
        for _ in range(defect(weights) + 2):
            s = improve(s)
            assert defect(s) <= prev
            prev = defect(s)
        assert s == settled

        # Acceleration: n accelerated rounds = 2n original rounds.
        accel = lambda v: improve(improve(v))
        k = rng.randrange(0, 6)
        assert iterate(accel, k, weights) == iterate(improve, 2 * k, weights)

    # The Lean examples.
    assert settle([3, 5, 8]) == [0, 0, 0]
    assert settle([7, 1]) == [0, 0]

    print(f"new_ai.py: all checks passed ({trials} random trials + examples)")


if __name__ == "__main__":
    main()
