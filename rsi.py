"""RSI — Recursive Self-Improvement.

A small executable companion to RSI.lean, in the descent style of
DescentCore.

A self-improving system applies an improvement procedure to its own
current state. A natural-number ``defect`` measures how far the state is
from a self-consistent one: while the defect is positive, one round of
improvement strictly lowers it; at defect zero the state is a fixed
point — the system no longer rewrites itself.

Guarantees (proved in RSI.lean; checked here on the concrete instance):

* Termination within a bound: iterated self-improvement reaches a
  defect-zero state within ``defect(state)`` rounds.
* Monotonicity: self-improvement never makes the defect worse.
* Self-acceleration: the system may rewrite its own improvement
  procedure by self-composition (the new procedure is the old one
  applied twice). The accelerated ``n``-round run equals the original
  ``2n``-round run, and termination is preserved under arbitrarily many
  such self-rewritings.

Standard library only.

Author: Takeo Yamamoto
License: Apache-2.0
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Generic, TypeVar

S = TypeVar("S")


@dataclass(frozen=True)
class SelfImprover(Generic[S]):
    """An improvement procedure plus its defect measure.

    ``progress`` and ``consistent`` from RSI.lean are the caller's
    contract: ``defect(improve(s)) < defect(s)`` whenever
    ``defect(s) > 0``, and ``improve(s) == s`` whenever
    ``defect(s) == 0``.
    """

    improve: Callable[[S], S]
    defect: Callable[[S], int]

    def run(self, rounds: int, state: S) -> S:
        """The state after ``rounds`` rounds of self-improvement."""
        for _ in range(rounds):
            state = self.improve(state)
        return state

    def run_to_consistent(self, state: S) -> tuple[S, int]:
        """Iterate self-improvement to the self-consistent attractor.

        Returns ``(final_state, rounds_used)``. By the termination
        theorem this takes at most ``defect(state)`` rounds.
        """
        bound = self.defect(state)
        rounds = 0
        while self.defect(state) > 0:
            state = self.improve(state)
            rounds += 1
            if rounds > bound:  # cannot happen for a valid SelfImprover
                raise AssertionError("termination bound violated")
        return state, rounds

    def accelerate(self) -> "SelfImprover[S]":
        """Rewrite the improvement procedure by self-composition.

        The new procedure is the old one applied twice per round; the
        defect measure is unchanged.
        """
        improve = self.improve
        return SelfImprover(lambda s: improve(improve(s)), self.defect)

    def meta_run(self, rewritings: int) -> "SelfImprover[S]":
        """This system after ``rewritings`` rounds of self-acceleration."""
        sys = self
        for _ in range(rewritings):
            sys = sys.accelerate()
        return sys


def countdown() -> SelfImprover[int]:
    """The countdown machine: a round of self-improvement halves the
    number; the defect is the number itself."""
    return SelfImprover(lambda n: n // 2, lambda n: n)


def _self_check() -> None:
    sys = countdown()

    # Termination within the bound, at the self-consistent fixed point.
    final, rounds = sys.run_to_consistent(100)
    assert final == 0 and sys.improve(final) == final
    assert rounds == 7 and rounds <= sys.defect(100)
    assert [sys.run(k, 100) for k in range(8)] == [100, 50, 25, 12, 6, 3, 1, 0]

    # Monotonicity: the defect never grows along the orbit.
    orbit = [sys.defect(sys.run(k, 100)) for k in range(8)]
    assert all(b <= a for a, b in zip(orbit, orbit[1:]))

    # Self-acceleration: the accelerated n-round run is the original
    # 2n-round run (the run_accelerate theorem of RSI.lean).
    acc = sys.accelerate()
    for n in range(5):
        assert acc.run(n, 100) == sys.run(2 * n, 100)
    acc_final, acc_rounds = acc.run_to_consistent(100)
    assert acc_final == 0 and acc_rounds == 4

    # Arbitrarily many self-rewritings preserve termination and defect.
    for k in range(4):
        meta = sys.meta_run(k)
        assert meta.defect(100) == sys.defect(100)
        meta_final, meta_rounds = meta.run_to_consistent(100)
        assert meta_final == 0 and meta_rounds <= sys.defect(100)

    print("rsi.py self-check OK")
    print(f"  countdown from 100: {rounds} rounds to the fixed point 0")
    print(f"  self-accelerated:   {acc_rounds} rounds")


if __name__ == "__main__":
    _self_check()
