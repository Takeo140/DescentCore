#!/usr/bin/env python3
"""NewComputer — companion executable for NewComputer.lean.

The same design as the Lean blueprint: a machine that computes by
descent. The worked design is the Euclidean machine — state (a, b),
one Euclidean step at a time, energy a + 2b off the rest states,
readout the first register.

The Lean file proves the specification in full
(compute (a, b) = Nat.gcd a b); this executable cross-checks the same
design against Python's math.gcd on random inputs, and checks the
design guarantees directly: the reached state has energy zero, the
computation takes at most `energy` steps, and a rest input is read
back unchanged.

Author: Takeo Yamamoto
License: Apache-2.0
"""

import math
import random


def euclid_step(s):
    a, b = s
    return (a, b) if b == 0 else (b, a % b)


def euclid_energy(s):
    a, b = s
    return 0 if b == 0 else a + 2 * b


def compute(s):
    # Run for exactly `energy` steps, as the blueprint prescribes.
    n = euclid_energy(s)
    for _ in range(n):
        s = euclid_step(s)
    return s[0], s


def main():
    rng = random.Random(20261124)
    trials = 500

    for _ in range(trials):
        a = rng.randrange(0, 500)
        b = rng.randrange(0, 500)
        out, reached = compute((a, b))
        assert out == math.gcd(a, b), (a, b, out)
        assert euclid_energy(reached) == 0, (a, b, reached)
        assert euclid_step(reached) == reached
        assert reached[1] == 0

        # A rest input is read back unchanged.
        out0, reached0 = compute((a, 0))
        assert out0 == a and reached0 == (a, 0)

        # The energy strictly falls while positive (the design condition).
        s = (a, b)
        while euclid_energy(s) > 0:
            t = euclid_step(s)
            assert euclid_energy(t) < euclid_energy(s)
            s = t

    # The Lean examples.
    assert compute((12, 18))[0] == 6
    assert compute((7, 13))[0] == 1
    assert compute((100, 75))[0] == 25
    assert compute((0, 9))[0] == 9

    print(f"new_computer.py: all checks passed ({trials} random trials + examples)")


if __name__ == "__main__":
    main()
