/-
# RSI — Recursive Self-Improvement

A formal kernel for recursive self-improvement, in the descent style of
DescentCore.

A self-improving system is a state space together with an improvement
procedure `improve` that the system applies to its own current state —
the state describes the whole system, including the current configuration
of its improvement procedure — and a natural-number `defect` measuring
how far the state is from a self-consistent one. The defining conditions:

* **Progress.** While the defect is positive, one self-application of
  `improve` strictly lowers it.
* **Consistency.** A state of defect zero is a fixed point of `improve`:
  the system no longer rewrites itself.

For any such system, this file proves — as theorems, not axioms:

* **Termination within a bound.** Iterated self-improvement reaches a
  defect-zero state within `defect s` steps.
* **The self-consistent attractor.** The state reached is a fixed point
  of `improve`, and once the orbit arrives there it stays there forever.
* **Monotonicity.** Self-improvement never makes the defect worse.
* **Self-acceleration.** The system may rewrite its own improvement
  procedure by self-composition (`accelerate`: the new procedure is the
  old one applied twice). The accelerated system is again a
  self-improving system with the same defect, its `n`-step run equals
  the original `2n`-step run, and termination within the same bound is
  preserved under arbitrarily many such self-rewritings (`metaRun`).

Convergence is derived from strict defect descent. No convergence axiom
is assumed. The countdown machine at the bottom is a small concrete
instance: repeated halving of a natural number reaches zero.

Author: Takeo Yamamoto
License: Apache-2.0
-/

namespace RSI

/-- A recursively self-improving system: an improvement procedure the
system applies to its own current state, a defect into the natural
numbers, strict progress while the defect is positive, and fixed points
at defect zero. -/
structure SelfImprover (S : Type) where
  improve : S → S
  defect : S → Nat
  progress : ∀ s, defect s ≠ 0 → defect (improve s) < defect s
  consistent : ∀ s, defect s = 0 → improve s = s

variable {S : Type}

/-- `run sys n s` is the state reached after `n` rounds of
self-improvement from `s`. -/
def run (sys : SelfImprover S) : Nat → S → S
  | 0, s => s
  | n + 1, s => sys.improve (run sys n s)

theorem run_zero (sys : SelfImprover S) (s : S) : run sys 0 s = s :=
  rfl

theorem run_succ (sys : SelfImprover S) (n : Nat) (s : S) :
    run sys (n + 1) s = sys.improve (run sys n s) :=
  rfl

/-- One round of self-improvement never increases the defect. -/
theorem defect_improve_le (sys : SelfImprover S) (s : S) :
    sys.defect (sys.improve s) ≤ sys.defect s := by
  by_cases h0 : sys.defect s = 0
  · rw [sys.consistent s h0]
    exact Nat.le_refl _
  · exact Nat.le_of_lt (sys.progress s h0)

/-- Self-improvement is monotone: each further round leaves the defect
no larger than the previous round did. -/
theorem defect_run_mono (sys : SelfImprover S) (n : Nat) (s : S) :
    sys.defect (run sys (n + 1) s) ≤ sys.defect (run sys n s) := by
  show sys.defect (sys.improve (run sys n s)) ≤ sys.defect (run sys n s)
  exact defect_improve_le sys _

/-- The key invariant: after `n` rounds, either the defect has already
reached zero, or it has fallen by at least `n`. -/
theorem defect_run (sys : SelfImprover S) :
    ∀ n s, sys.defect (run sys n s) + n ≤ sys.defect s ∨
      sys.defect (run sys n s) = 0 := by
  intro n
  induction n with
  | zero =>
      intro s
      left
      show sys.defect s + 0 ≤ sys.defect s
      omega
  | succ n ih =>
      intro s
      by_cases h0 : sys.defect (run sys n s) = 0
      · right
        show sys.defect (sys.improve (run sys n s)) = 0
        rw [sys.consistent _ h0]
        exact h0
      · left
        have hprog : sys.defect (sys.improve (run sys n s)) <
            sys.defect (run sys n s) := sys.progress _ h0
        obtain h | h := ih s
        · show sys.defect (sys.improve (run sys n s)) + (n + 1) ≤ sys.defect s
          omega
        · exact absurd h h0

/-- Termination with an explicit bound: from any state, iterated
self-improvement reaches a defect-zero state within `defect s` rounds. -/
theorem terminates_within (sys : SelfImprover S) (s : S) :
    ∃ n, n ≤ sys.defect s ∧ sys.defect (run sys n s) = 0 := by
  refine ⟨sys.defect s, Nat.le_refl _, ?_⟩
  obtain h | h := defect_run sys (sys.defect s) s
  · omega
  · exact h

/-- Runs compose: `a + b` rounds are `a` rounds followed by `b` rounds. -/
theorem run_add (sys : SelfImprover S) :
    ∀ a b s, run sys (a + b) s = run sys b (run sys a s) := by
  intro a b
  induction b with
  | zero =>
      intro s
      rw [Nat.add_zero, run_zero]
  | succ b ih =>
      intro s
      rw [Nat.add_succ]
      show sys.improve (run sys (a + b) s) =
        sys.improve (run sys b (run sys a s))
      rw [ih s]

/-- The self-consistent attractor: from any state, iterated
self-improvement reaches a state that the system no longer rewrites,
and once the orbit arrives there it stays there forever. -/
theorem reaches_consistent (sys : SelfImprover S) (s : S) :
    ∃ t, (∃ n, run sys n s = t) ∧ sys.defect t = 0 ∧ sys.improve t = t ∧
      ∀ m, run sys m t = t := by
  obtain ⟨n, -, hn⟩ := terminates_within sys s
  refine ⟨run sys n s, ⟨n, rfl⟩, hn, sys.consistent _ hn, ?_⟩
  intro m
  induction m with
  | zero => rfl
  | succ m ihm =>
      show sys.improve (run sys m (run sys n s)) = run sys n s
      rw [ihm]
      exact sys.consistent _ hn

/-- Self-acceleration: the system rewrites its own improvement procedure
by self-composition — the new procedure is the old one applied twice.
The result is again a self-improving system, with the same defect. -/
def accelerate (sys : SelfImprover S) : SelfImprover S where
  improve := fun s => sys.improve (sys.improve s)
  defect := sys.defect
  progress := by
    intro s hs
    show sys.defect (sys.improve (sys.improve s)) < sys.defect s
    by_cases h1 : sys.defect (sys.improve s) = 0
    · have hfix : sys.improve (sys.improve s) = sys.improve s :=
        sys.consistent _ h1
      rw [hfix, h1]
      exact Nat.pos_of_ne_zero hs
    · have a := sys.progress (sys.improve s) h1
      have b := sys.progress s hs
      omega
  consistent := by
    intro s hs
    show sys.improve (sys.improve s) = s
    have h := sys.consistent s hs
    rw [h, h]

/-- One round of the accelerated system is two rounds of the original:
the `n`-step run of the self-accelerated system is the `2n`-step run of
the original. -/
theorem run_accelerate (sys : SelfImprover S) :
    ∀ n s, run (accelerate sys) n s = run sys (2 * n) s := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      show sys.improve (sys.improve (run (accelerate sys) n s)) =
        run sys (2 * (n + 1)) s
      rw [ih s]
      have h2 : 2 * (n + 1) = 2 * n + 2 := by omega
      rw [h2]
      rfl

/-- Arbitrarily many self-rewritings of the improvement procedure:
`metaRun k sys` is `sys` after `k` rounds of self-acceleration. -/
def metaRun : Nat → SelfImprover S → SelfImprover S
  | 0, sys => sys
  | k + 1, sys => accelerate (metaRun k sys)

/-- Self-rewriting never changes the defect measure. -/
theorem metaRun_defect (sys : SelfImprover S) :
    ∀ k, (metaRun k sys).defect = sys.defect
  | 0 => rfl
  | k + 1 => metaRun_defect sys k

/-- Termination is preserved under arbitrarily many self-rewritings of
the improvement procedure, within the same defect bound. -/
theorem meta_terminates (sys : SelfImprover S) (k : Nat) (s : S) :
    ∃ n, n ≤ sys.defect s ∧ sys.defect (run (metaRun k sys) n s) = 0 := by
  obtain ⟨n, hn1, hn2⟩ := terminates_within (metaRun k sys) s
  refine ⟨n, ?_, ?_⟩
  · rwa [metaRun_defect sys k] at hn1
  · rwa [metaRun_defect sys k] at hn2

/-- The countdown machine: the state is a natural number, a round of
self-improvement halves it, and the defect is the number itself.
A concrete self-improving system. -/
def countdown : SelfImprover Nat where
  improve := fun n => n / 2
  defect := fun n => n
  progress := by
    intro n hn
    show n / 2 < n
    omega
  consistent := by
    intro n hn
    have hn' : n = 0 := hn
    show n / 2 = n
    rw [hn']

/-- Seven rounds of self-improvement take 100 to the self-consistent
state 0. -/
theorem countdown_example : run countdown 7 100 = 0 :=
  rfl

end RSI
