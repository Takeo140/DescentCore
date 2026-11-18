# DescentCore

The descent core, and everything that stands on it — in one repository.

Five self-contained Lean 4 files (core Lean only, no Mathlib): the first four are rungs built on the last, each complete on its own, plus a standalone companion file in the same descent style:

## The five files

- **`DescentCore.lean` — the kernel.** For any *descent system* — a step function with a natural-number energy that strictly decreases until it reaches zero — termination within the initial energy and the attractor property (the reached state is a rest state the orbit never leaves) are proved once, as theorems, for all such systems.
- **`UniversalCore.lean` — the universal machine.** A universal register machine (`inc`, `dec`-with-jump, `jmp`, `halt`; unbounded natural registers) on the kernel: any program carrying a measure that decreases between non-halting states is proved to halt within `μ s + 1` steps and rest there (`machine_halts`), with a verified end-to-end example (`progZero`).
- **`VonNeumannCore.lean` — the stored program.** Instructions encoded as data in memory, three cells per instruction (`decode_encode`, `encodeMem_encodes`); one fetch–decode–execute interpreter proved to simulate the direct machine step for step (`vsim`, `vsim_iter`); the termination guarantee transferred to interpreted execution (`interpreter_halts`); `progZero` run from memory to the same proved final state (`progZero_interpreted`).
- **`TowerCore.lean` — the tower.** Systems stacked on the base layer: under one interface condition — each upper layer preserves the rest sets of the layers below it — a tower of any height is proved to be again a descent system of exactly the base form (`towerSys`) and to reach the joint rest state where every layer's energy is zero (`tower_halts`), instantiated with the two countdown machines (`two_countdowns_tower`). The earlier rungs are included in the same file, so the tower stands on them literally as well as conceptually.
- **`RSI.lean` — recursive self-improvement.** A self-improving system (`SelfImprover`): while the defect (distance to self-consistency) is positive, self-application of `improve` strictly lowers it, and a defect-zero state is a fixed point that no longer rewrites itself. Proved as theorems: termination within the defect bound, the self-consistent attractor, monotone improvement, and self-acceleration (`accelerate`: n accelerated rounds equal 2n original rounds; `metaRun` preserves termination under repeated self-rewriting). Companion executable `rsi.py` checks the same structure.

## Honest scope

- The Turing completeness of the register-machine model itself is the classical result and is not re-proved here; what is proved is the halting guarantee for measured programs.
- What the stacking construction produces is a system of the base form together with its guarantees — not a new physical machine. The layer interface is a real condition: arbitrary systems do not stack.
- Claims are exactly what the theorems say — no more.

## Verification

- Lean 4 (core only), no Mathlib, no `sorry`. `#print axioms` on the main theorems reports only `[propext, Quot.sound]`.
- CI compiles all five files and fails if any `sorry` warning appears.

## License

Apache License 2.0. See `LICENSE`.
