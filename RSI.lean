/-
# RSI — Relative Strength Index

The Relative Strength Index, the momentum indicator published by
J. Welles Wilder Jr. in 1978, computed exactly over the rational
numbers (core Lean only, no Mathlib).

Given a list of prices, the changes between consecutive prices split
into gains and losses. Wilder's method averages them with a smoothing
recursion (an exponential average with factor `1 / period`):

* the first average is the plain mean of the first `period` changes,
* each later change updates the average by
  `avg := (avg * (period - 1) + current) / period`.

From the final averages `g` (gain) and `l` (loss) the index is

    RSI = 100 - 100 / (1 + g / l)  =  100 * g / (g + l),

with the conventional edge cases: no loss at all gives 100, and no
movement at all gives the neutral 50.

This file proves — as theorems, not axioms:

* **Bounds.** Whenever the average loss is nonzero, the value from
  `rsiFromAverages` lies in `[0, 100]`.
* **Edge cases.** `rsiFromAverages 0 0 = 50` and, for `g ≠ 0`,
  `rsiFromAverages g 0 = 100`.
* **A worked sample** (by evaluation, below). The price series used
  to check the companion Python implementation (`rsi.py` in this
  repository) gives the same final value here, as an exact rational
  number.

Author: Takeo Yamamoto
License: Apache-2.0
-/

namespace RSI

/-- The gain of a single price change: the change itself if it is
positive, otherwise zero. -/
def gain (d : Rat) : Rat :=
  if 0 < d then d else 0

/-- The loss of a single price change: the size of the change if it is
negative, otherwise zero. -/
def loss (d : Rat) : Rat :=
  gain (-d)

theorem gain_nonneg (d : Rat) : 0 ≤ gain d := by
  by_cases h : 0 < d
  · unfold gain
    rw [ite_eq_left h]
    exact (Rat.lt_iff_le_and_ne).mp h |>.1
  · unfold gain
    rw [ite_eq_right h]
    decide

theorem loss_nonneg (d : Rat) : 0 ≤ loss d :=
  gain_nonneg (-d)

/-- The changes between consecutive prices. -/
def changes : List Rat → List Rat
  | [] => []
  | [_] => []
  | a :: b :: rest => (b - a) :: changes (b :: rest)

/-- The index from average gain and average loss, in the fraction form
`100 * g / (g + l)`, with the conventional edge cases when the average
loss is zero. -/
def rsiFromAverages (avgGain avgLoss : Rat) : Rat :=
  if avgLoss = 0 then
    if avgGain = 0 then 50 else 100
  else
    100 * avgGain / (avgGain + avgLoss)

/-- The inverse of a nonnegative rational is nonnegative. -/
theorem inv_nonneg {q : Rat} (h : 0 ≤ q) : 0 ≤ q⁻¹ := by
  rw [Rat.inv_def]
  exact Rat.divInt_nonneg (by omega) (Rat.num_nonneg.mpr h)

/-- The bounds theorem: with a nonzero average loss, the index lies in
`[0, 100]`. -/
theorem rsiFromAverages_bounds {g l : Rat} (hg : 0 ≤ g) (hl : 0 ≤ l)
    (hl0 : l ≠ 0) :
    0 ≤ rsiFromAverages g l ∧ rsiFromAverages g l ≤ 100 := by
  have hle_l : l ≤ g + l := by
    have h : l + 0 ≤ l + g := Rat.add_le_add_left.mpr hg
    rw [Rat.add_zero, Rat.add_comm l g] at h
    exact h
  have hsum_ne : g + l ≠ 0 := by
    intro h
    rw [h] at hle_l
    exact hl0 (Rat.le_antisymm hle_l hl)
  have hsum_nonneg : 0 ≤ g + l := Rat.add_nonneg hg hl
  have hinv : 0 ≤ (g + l)⁻¹ := inv_nonneg hsum_nonneg
  have hg_le : g ≤ g + l := by
    have h : g + 0 ≤ g + l := Rat.add_le_add_left.mpr hl
    rwa [Rat.add_zero] at h
  have hfrac_le : g * (g + l)⁻¹ ≤ 1 := by
    have h1 : g * (g + l)⁻¹ ≤ (g + l) * (g + l)⁻¹ :=
      Rat.mul_le_mul_of_nonneg_right hg_le hinv
    rwa [Rat.mul_inv_cancel _ hsum_ne] at h1
  have h100 : (0 : Rat) ≤ 100 := by decide
  unfold rsiFromAverages
  rw [ite_eq_right hl0, Rat.div_def]
  constructor
  · rw [Rat.mul_assoc]
    exact Rat.mul_nonneg h100 (Rat.mul_nonneg hg hinv)
  · rw [Rat.mul_assoc]
    have h := Rat.mul_le_mul_of_nonneg_left hfrac_le h100
    rwa [Rat.mul_one] at h

/-- No movement at all: the neutral value 50. -/
theorem rsiFromAverages_flat : rsiFromAverages 0 0 = 50 := by
  unfold rsiFromAverages
  rw [ite_eq_left rfl, ite_eq_left rfl]

/-- No loss at all: the maximal value 100. -/
theorem rsiFromAverages_no_loss {g : Rat} (hg : g ≠ 0) :
    rsiFromAverages g 0 = 100 := by
  unfold rsiFromAverages
  rw [ite_eq_left rfl, ite_eq_right hg]

/-- One Wilder smoothing step: fold a new price change into the running
average gain and average loss. -/
def wilderStep (period : Nat) (avg : Rat × Rat) (d : Rat) : Rat × Rat :=
  let p : Rat := (period : Rat)
  ((avg.1 * (p - 1) + gain d) / p, (avg.2 * (p - 1) + loss d) / p)

/-- The RSI of a price series with the given period (14 by default):
`none` when there are fewer changes than the period, otherwise the
index after Wilder smoothing over all changes. -/
def rsi (prices : List Rat) (period : Nat := 14) : Option Rat :=
  let ds := changes prices
  if period = 0 ∨ ds.length < period then
    none
  else
    let init := ds.take period
    let rest := ds.drop period
    let avgG := (init.map gain).sum / (period : Rat)
    let avgL := (init.map loss).sum / (period : Rat)
    let final := rest.foldl (wilderStep period) (avgG, avgL)
    some (rsiFromAverages final.1 final.2)

/-- The sample price series used to check the companion Python
implementation, scaled by 100 (the index is scale-invariant, so the
values agree exactly). -/
def samplePrices : List Rat :=
  [4434, 4409, 4415, 4361, 4433, 4483, 4510, 4542, 4584, 4608,
   4589, 4603, 4561, 4628, 4628, 4600, 4603, 4641, 4622, 4564,
   4621, 4625, 4571, 4645, 4578, 4535, 4403, 4418, 4422, 4457,
   4342, 4266]

/- The worked sample, checked by evaluation: the final RSI of
`samplePrices` is `338112527124029046860900 / 10217817959618882469739`
(approximately 33.09), in agreement with the companion Python
implementation. Rational arithmetic does not reduce in core Lean's
kernel, so this is an `#eval` check rather than a theorem. -/
#eval rsi samplePrices 14

end RSI
