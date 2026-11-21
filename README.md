#
DescentCore

The descent core, and everything that stands on it — in one repository.

Seven self-contained Lean 4 files (core Lean only, no Mathlib): the first four are rungs built on the last, each complete on its own, plus three standalone companion files:

## The seven files

- **`DescentCore.lean` — the kernel.** For any *descent system* — a step function with a natural-number energy that strictly decreases until it reaches zero — termination within the initial energy and the attractor property (the reached state is a rest state the orbit never leaves) are proved once, as theorems, for all such systems.
- **`UniversalCore.lean` — the universal machine.** A universal register machine (`inc`, `dec`-with-jump, `jmp`, `halt`; unbounded natural registers) on the kernel: any program carrying a measure that decreases between non-halting states is proved to halt within `μ s + 1` steps and rest there (`machine_halts`), with a verified end-to-end example (`progZero`).
- **`VonNeumannCore.lean` — the stored program.** Instructions encoded as data in memory, three cells per instruction (`decode_encode`, `encodeMem_encodes`); one fetch–decode–execute interpreter proved to simulate the direct machine step for step (`vsim`, `vsim_iter`); the termination guarantee transferred to interpreted execution (`interpreter_halts`); `progZero` run from memory to the same proved final state (`progZero_interpreted`).
- **`TowerCore.lean` — the tower.** Systems stacked on the base layer: under one interface condition — each upper layer preserves the rest sets of the layers below it — a tower of any height is proved to be again a descent system of exactly the base form (`towerSys`) and to reach the joint rest state where every layer's energy is zero (`tower_halts`), instantiated with the two countdown machines (`two_countdowns_tower`). The earlier rungs are included in the same file, so the tower stands on them literally as well as conceptually.
- **`RSI.lean` — recursive self-improvement.** A self-improving system (`SelfImprover`): while the defect (distance to self-consistency) is positive, self-application of `improve` strictly lowers it, and a defect-zero state is a fixed point that no longer rewrites itself. Proved as theorems: termination within the defect bound, the self-consistent attractor, monotone improvement, and self-acceleration (`accelerate`: n accelerated rounds equal 2n original rounds; `metaRun` preserves termination under repeated self-rewriting). Companion executable `rsi.py` checks the same structure.
- **`QuantumCore.lean` — discrete quantum computation.** Quantum computation in a fully discrete, exact form, designed to be used on digital machines: amplitudes are elements of the ring `ℤ[√2, i]` — quadruples of integers `(u, v, w, z)` read as `(u + v·√2) + i·(w + z·√2)` — carried with a natural-number scale (the actual amplitude is `A/(√2)^scale`), so the universal gate set `{X, Z, S, T, H, CNOT}` is exact integer arithmetic — no floating point anywhere. (The `√2` components are necessary: the `T` gate is exact only if the numerators can carry a factor of `√2`.) Circuits are instruction lists executed by a fold. Proved as theorems: length preservation for gates and whole circuits, and circuit composition. The standard examples — superposition, the Bell state, the GHZ state, `H` twice as interference, the `T` and `S` phases, and `T` on a superposition — are verified by exact computation (`decide`), with normalization checked as weight `= (2^scale, 0)`. Companion executable `quantum.py` checks the same structure.
- **`LinearCore.lean` — discrete complex linear algebra.** The base layer under the quantum file, in the same discrete exact style: the scalars are the Gaussian rationals `ℚ(i)` — pairs of rationals `(re, im)` — a field whose laws are proved in full, including an inverse for every scalar with `normSq ≠ 0`. Vectors are lists of scalars and matrices are lists of rows; the vector and inner-product laws and the matrix addition, transpose, conjugate-transpose and identity laws are proved for all shapes. On the `2 × 2` record: associativity of multiplication (with a bridge to the list matrices), the adjugate inverse with `A * A⁻¹ = A⁻¹ * A = I` under `det A ≠ 0`, Cramer's rule, and the Pauli matrices (`X² = Y² = Z² = I`, `S² = Z`). Determinants are the classical formulas for orders 2 and 3. One honest exception: `det (A * B) = det A * det B` is not proved in Lean; it is verified computationally, in exact rational arithmetic, by the companion executable `linear.py`, which also runs Gaussian elimination over `ℚ(i)`. Eigenvalues and spectral theory lie outside the discrete exact frame and are not included.

## Honest scope

- The Turing completeness of the register-machine model itself is the classical result and is not re-proved here; what is proved is the halting guarantee for measured programs.
- What the stacking construction produces is a system of the base form together with its guarantees — not a new physical machine. The layer interface is a real condition: arbitrary systems do not stack.
- Claims are exactly what the theorems say — no more.

## Verification

- Lean 4 (core only), no Mathlib, no `sorry`. `#print axioms` on the main theorems of the first six files reports only `[propext, Quot.sound]`; the theorems of `LinearCore.lean` report `[propext, Classical.choice, Quot.sound]`.
- CI compiles all seven files and fails if any `sorry` warning appears.

## License

Apache License 2.0. See `LICENSE`.
