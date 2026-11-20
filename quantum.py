"""QuantumCore — discrete quantum computation for digital machines.

A Python reference implementation of the model formalized in
QuantumCore.lean. Amplitudes are Gaussian integers (pairs of ints), and a
state carries a scale: the actual amplitude of a basis state is
``(re + i*im) / sqrt(2)**scale``. Every gate of the universal set
{X, Z, S, T, H, CNOT} is exact integer arithmetic — no floating point —
so the model runs as-is on a digital computer.

Author: Takeo Yamamoto
License: Apache-2.0
"""

# An amplitude is a tuple (re, im) of ints, read as re + i*im.
ZERO = (0, 0)
ONE = (1, 0)
EYE = (0, 1)


def gadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def gneg(a):
    return (-a[0], -a[1])


def gsub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def gmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def norm_sq(a):
    return a[0] * a[0] + a[1] * a[1]


def gate_x(a, b):
    return (b, a)


def gate_z(a, b):
    return (a, gneg(b))


def gate_s(a, b):
    return (a, gmul(EYE, b))


def gate_h(a, b):
    return (gadd(a, b), gsub(a, b))


def gate_t(a, b):
    # b is multiplied by (1 + i) / sqrt(2); the sqrt(2) goes to the scale.
    return (a, (b[0] - b[1], b[0] + b[1]))


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
        return sum(norm_sq(a) for a in self.amps)

    def normalized(self):
        return self.weight() == 2 ** self.scale


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
    assert s == QState(1, [(1, 0), (1, 0)])
    assert s.normalized()

    # H then CNOT on |00> gives the Bell state (|00> + |11>) / sqrt(2).
    bell = run(basis(2, 0), [("H", 0), ("CNOT", 0, 1)])
    assert bell == QState(1, [(1, 0), (0, 0), (0, 0), (1, 0)])
    assert bell.normalized()
    assert norm_sq(bell.amps[0]) * 2 == bell.weight()  # probability 1/2

    # GHZ state on three qubits.
    ghz = run(basis(3, 0), [("H", 0), ("CNOT", 0, 1), ("CNOT", 1, 2)])
    assert ghz == QState(1, [(1, 0)] + [(0, 0)] * 6 + [(1, 0)])
    assert ghz.normalized()

    # Interference: H twice returns |0> to itself, as (2, 0) at scale 2.
    assert run(basis(1, 0), [("H", 0), ("H", 0)]) == QState(2, [(2, 0), (0, 0)])

    # T on |1> gives the phase (1 + i) / sqrt(2); S on |1> gives i.
    assert run(basis(1, 1), [("T", 0)]) == QState(1, [(0, 0), (1, 1)])
    assert run(basis(1, 1), [("S", 0)]) == QState(0, [(0, 0), (0, 1)])

    print("self-check OK: X, H, CNOT (Bell), GHZ, H*H interference, T, S")
    print("Bell state:", bell)


if __name__ == "__main__":
    main()
