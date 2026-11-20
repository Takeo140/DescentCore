"""QuantumCore — discrete quantum computation for digital machines.

A Python reference implementation of the model formalized in
QuantumCore.lean. An amplitude is a quadruple of ints ``(u, v, w, z)``
read as ``(u + v*sqrt(2)) + i*(w + z*sqrt(2))`` — an element of the ring
Z[sqrt(2), i] — and a state carries a scale: the actual amplitude of a
basis state is ``A / sqrt(2)**scale``. Every gate of the universal set
{X, Z, S, T, H, CNOT} is exact integer arithmetic — no floating point —
so the model runs as-is on a digital computer.

The sqrt(2) components are necessary: the T gate multiplies one component
of a pair by (1 + i)/sqrt(2) and the other by 1, so a shared scale can
only absorb the sqrt(2) denominator if the numerators can themselves
carry a factor of sqrt(2).

Author: Takeo Yamamoto
License: Apache-2.0
"""

# An amplitude is a tuple (u, v, w, z) of ints.
ZERO = (0, 0, 0, 0)
ONE = (1, 0, 0, 0)


def aadd(a, b):
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2], a[3] + b[3])


def aneg(a):
    return (-a[0], -a[1], -a[2], -a[3])


def asub(a, b):
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3])


def mul_i(a):
    return (-a[2], -a[3], a[0], a[1])


def mul_sqrt2(a):
    return (2 * a[1], a[0], 2 * a[3], a[2])


def mul_one_plus_i(a):
    return (a[0] - a[2], a[1] - a[3], a[2] + a[0], a[3] + a[1])


def abs_sq(a):
    """|A|^2 as a pair (p, q) standing for p + q*sqrt(2)."""
    return (a[0] * a[0] + 2 * a[1] * a[1] + a[2] * a[2] + 2 * a[3] * a[3],
            2 * (a[0] * a[1] + a[2] * a[3]))


def gate_x(a, b):
    return (b, a)


def gate_z(a, b):
    return (a, aneg(b))


def gate_s(a, b):
    return (a, mul_i(b))


def gate_h(a, b):
    return (aadd(a, b), asub(a, b))


def gate_t(a, b):
    # At scale +1 this represents (a, (1 + i)/sqrt(2) * b) exactly.
    return (mul_sqrt2(a), mul_one_plus_i(b))


def partner(i, q):
    if (i >> q) & 1:
        return i - (1 << q)
    return i + (1 << q)


def apply_gate(g, q, amps):
    out = []
    for i in range(len(amps)):
        p = partner(i, q)
        if (i >> q) & 1:
            a, b = amps[p], amps[i]
            out.append(g(a, b)[1])
        else:
            a, b = amps[i], amps[p]
            out.append(g(a, b)[0])
    return out


def apply_cnot(c, t, amps):
    out = []
    for i in range(len(amps)):
        if (i >> c) & 1:
            out.append(amps[partner(i, t)])
        else:
            out.append(amps[i])
    return out


class QState:
    def __init__(self, scale, amps):
        self.scale = scale
        self.amps = list(amps)

    def __eq__(self, other):
        return self.scale == other.scale and self.amps == other.amps

    def __repr__(self):
        return f"QState(scale={self.scale}, amps={self.amps})"

    def weight(self):
        """Total weight as a pair (p, q) standing for p + q*sqrt(2)."""
        p = q = 0
        for a in self.amps:
            ap, aq = abs_sq(a)
            p += ap
            q += aq
        return (p, q)

    def normalized(self):
        return self.weight() == (2 ** self.scale, 0)


def step(state, instr):
    op = instr[0]
    if op == "X":
        return QState(state.scale, apply_gate(gate_x, instr[1], state.amps))
    if op == "Z":
        return QState(state.scale, apply_gate(gate_z, instr[1], state.amps))
    if op == "S":
        return QState(state.scale, apply_gate(gate_s, instr[1], state.amps))
    if op == "T":
        return QState(state.scale + 1, apply_gate(gate_t, instr[1], state.amps))
    if op == "H":
        return QState(state.scale + 1, apply_gate(gate_h, instr[1], state.amps))
    if op == "CNOT":
        return QState(state.scale, apply_cnot(instr[1], instr[2], state.amps))
    raise ValueError(f"unknown instruction: {instr}")


def run(state, circuit):
    for instr in circuit:
        state = step(state, instr)
    return state


def basis(n, k):
    return QState(0, [ONE if i == k else ZERO for i in range(2 ** n)])


def main():
    # X flips |0> to |1>.
    assert run(basis(1, 0), [("X", 0)]) == basis(1, 1)

    # H on |0> gives (|0> + |1>) / sqrt(2), normalized.
    s = run(basis(1, 0), [("H", 0)])
    assert s == QState(1, [(1, 0, 0, 0), (1, 0, 0, 0)])
    assert s.normalized()

    # H then CNOT on |00> gives the Bell state (|00> + |11>) / sqrt(2).
    bell = run(basis(2, 0), [("H", 0), ("CNOT", 0, 1)])
    assert bell == QState(1, [(1, 0, 0, 0), (0, 0, 0, 0),
                              (0, 0, 0, 0), (1, 0, 0, 0)])
    assert bell.normalized()
    assert abs_sq(bell.amps[0]) == (1, 0)  # probability (1,0)/(2,0) = 1/2

    # GHZ state on three qubits.
    ghz = run(basis(3, 0), [("H", 0), ("CNOT", 0, 1), ("CNOT", 1, 2)])
    assert ghz == QState(1, [(1, 0, 0, 0)] + [(0, 0, 0, 0)] * 6
                         + [(1, 0, 0, 0)])
    assert ghz.normalized()

    # Interference: H twice returns |0> to itself, as (2,0,0,0) at scale 2.
    assert run(basis(1, 0), [("H", 0), ("H", 0)]) == \
        QState(2, [(2, 0, 0, 0), (0, 0, 0, 0)])

    # T on |1> gives the phase (1 + i) / sqrt(2); S on |1> gives i.
    assert run(basis(1, 1), [("T", 0)]) == \
        QState(1, [(0, 0, 0, 0), (1, 0, 1, 0)])
    assert run(basis(1, 1), [("S", 0)]) == \
        QState(0, [(0, 0, 0, 0), (0, 0, 1, 0)])

    # Regression: T on a superposition stays exact and normalized.
    ts = run(basis(1, 0), [("H", 0), ("T", 0)])
    assert ts == QState(2, [(0, 1, 0, 0), (1, 0, 1, 0)])
    assert ts.normalized()

    # Invariant: every circuit preserves normalization exactly.
    import random
    rng = random.Random(20261121)
    for _ in range(200):
        n = rng.randint(1, 4)
        circ = []
        for _ in range(rng.randint(1, 30)):
            op = rng.choice(["X", "Z", "S", "T", "H", "CNOT"])
            if op == "CNOT" and n > 1:
                c, t = rng.sample(range(n), 2)
                circ.append(("CNOT", c, t))
            elif op == "CNOT":
                circ.append(("H", rng.randrange(n)))
            else:
                circ.append((op, rng.randrange(n)))
        assert run(basis(n, 0), circ).normalized(), circ

    print("self-check OK: X, H, CNOT (Bell), GHZ, H*H interference, T, S,")
    print("  T-on-superposition regression, 200 random circuits normalized")
    print("Bell state:", bell)


if __name__ == "__main__":
    main()
