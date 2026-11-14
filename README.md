# DescentCore

A verified kernel for descent systems, in Lean 4 (core Lean only — no Mathlib).

A **descent system** is a set of states carrying a natural-number energy and a step function, such that:

- the energy strictly decreases at every step while it is positive, and
- a state of energy zero never moves.

`DescentCore.lean` proves, for **every** such system:

- **Termination within a bound** (`terminates_within`): from any state `s`, the orbit reaches an energy-zero state within `energy s` steps.
- **The attractor** (`reaches_rest`): the state reached is a rest state, and once the orbit arrives there, it stays there forever.

Convergence is derived from strict energy descent. **No convergence axiom is assumed.**

## Why this exists

This is the shared pattern underneath the ExtremalMachine line of work and the 2026 blueprints — OSBlueprint, NewComputer, NewAI, YamamotoEvolution. Each of them is a descent system in the sense defined here. DescentCore states and proves the common kernel once, so the instances do not have to repeat the argument. The halving machine (repeated halving of a natural number reaches zero within `n` steps) is included as a small concrete instance.

## Verification

- Lean 4, core library only (no Mathlib dependency).
- No `sorry`, no placeholders.
- `#print axioms` for the main theorems reports only `[propext, Quot.sound]` — the standard logical axioms, and no `sorryAx`.

To check:

```
lean DescentCore.lean
```

## Author

Takeo Yamamoto

## License

Apache License 2.0
