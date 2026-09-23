import GaloisForLFunctions.RHTower.XiWardCubicTranslationEnergySeparator

/-!
# Modular chamber of the cubic Ward source-shift defect

The two prime-normalized critical shifts producing the positive strict-right conormal feature do
not form a positive difference on the primal critical Hilbert carrier.  After pulling both shift
energies back to the same source coordinate, their exact Lebesgue defect density is

`exp |x-L| - exp |x-2L|`.

This file proves that the density is reflection-odd about `3L/2`, is negative to the left of that
wall and positive to its right, and retains both signs after insertion of the critical modular
half-density.  Thus the missing completed Ward incidence cannot be an ordinary Loewner-positive
difference of the two source-shift energies.  It must retain a graded/modular orientation before
cubic compression.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

open HedenmalmThetaSource

namespace HedenmalmThetaSource

/-- Lebesgue density of the prime-normalized energy difference between source shifts of depths
`L` and `2L`, after both energies are pulled back to the same source coordinate. -/
def cubicCriticalShiftLebesgueDefectDensity (L x : ℝ) : ℝ :=
  Real.exp |x - L| - Real.exp |x - 2 * L|

/-- Radon--Nikodym density, relative to the critical Haar model, of one prime-normalized critical
shift energy pulled back to its input coordinate. -/
def primeNormalizedCriticalShiftPulledDensity (L x : ℝ) : ℝ :=
  Real.exp L * ‖criticalShiftSymbol L (x - L)‖ ^ (2 : ℕ)

/-- Exact critical half-density formula for a pulled prime-normalized shift. -/
theorem primeNormalizedCriticalShiftPulledDensity_eq
    (L x : ℝ) :
    primeNormalizedCriticalShiftPulledDensity L x =
      Real.exp (-|x|) * Real.exp |x - L| := by
  rw [primeNormalizedCriticalShiftPulledDensity,
    norm_criticalShiftSymbol_sq, radialRiggingShiftEnergyRatio,
    radialRiggingWeight]
  simp only [one_mul, radialRiggingWeight]
  rw [show x - L + L = x by ring]
  rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add,
    ← Real.exp_add, ← Real.exp_add]
  rw [← Real.exp_add]
  congr 1
  ring

/-- Difference of the two pulled prime-normalized critical-shift densities. -/
def cubicCriticalShiftPulledDefectDensity (L x : ℝ) : ℝ :=
  primeNormalizedCriticalShiftPulledDensity L x -
    primeNormalizedCriticalShiftPulledDensity (2 * L) x

/-- The critical modular factor is strictly positive and leaves the raw Lebesgue chamber as the
entire sign-bearing part of the pulled defect. -/
theorem cubicCriticalShiftPulledDefectDensity_eq
    (L x : ℝ) :
    cubicCriticalShiftPulledDefectDensity L x =
      Real.exp (-|x|) * cubicCriticalShiftLebesgueDefectDensity L x := by
  rw [cubicCriticalShiftPulledDefectDensity,
    primeNormalizedCriticalShiftPulledDensity_eq,
    primeNormalizedCriticalShiftPulledDensity_eq,
    cubicCriticalShiftLebesgueDefectDensity]
  ring

/-- Exact reflection antisymmetry of the raw defect density about the moving wall `3L/2`. -/
theorem cubicCriticalShiftLebesgueDefectDensity_reflection
    (L x : ℝ) :
    cubicCriticalShiftLebesgueDefectDensity L (3 * L - x) =
      -cubicCriticalShiftLebesgueDefectDensity L x := by
  rw [cubicCriticalShiftLebesgueDefectDensity,
    cubicCriticalShiftLebesgueDefectDensity]
  have h1 : 3 * L - x - L = -(x - 2 * L) := by ring
  have h2 : 3 * L - x - 2 * L = -(x - L) := by ring
  rw [h1, h2, abs_neg, abs_neg]
  ring

private theorem abs_sub_dyadic_lt_iff
    {L : ℝ} (hL : 0 < L) (x : ℝ) :
    |x - L| < |x - 2 * L| ↔ x < 3 * L / 2 := by
  by_cases h1 : x ≤ L
  · rw [abs_of_nonpos (sub_nonpos.mpr h1),
      abs_of_nonpos (by linarith : x - 2 * L ≤ 0)]
    constructor <;> intro h <;> linarith
  · have hxL : L ≤ x := (lt_of_not_ge h1).le
    by_cases h2 : x ≤ 2 * L
    · rw [abs_of_nonneg (sub_nonneg.mpr hxL),
        abs_of_nonpos (sub_nonpos.mpr h2)]
      constructor <;> intro h <;> linarith
    · have hx2 : 2 * L ≤ x := (lt_of_not_ge h2).le
      rw [abs_of_nonneg (sub_nonneg.mpr hxL),
        abs_of_nonneg (sub_nonneg.mpr hx2)]
      constructor <;> intro h <;> linarith

private theorem abs_dyadic_sub_lt_iff
    {L : ℝ} (hL : 0 < L) (x : ℝ) :
    |x - 2 * L| < |x - L| ↔ 3 * L / 2 < x := by
  by_cases h1 : x ≤ L
  · rw [abs_of_nonpos (sub_nonpos.mpr h1),
      abs_of_nonpos (by linarith : x - 2 * L ≤ 0)]
    constructor <;> intro h <;> linarith
  · have hxL : L ≤ x := (lt_of_not_ge h1).le
    by_cases h2 : x ≤ 2 * L
    · rw [abs_of_nonneg (sub_nonneg.mpr hxL),
        abs_of_nonpos (sub_nonpos.mpr h2)]
      constructor <;> intro h <;> linarith
    · have hx2 : 2 * L ≤ x := (lt_of_not_ge h2).le
      rw [abs_of_nonneg (sub_nonneg.mpr hxL),
        abs_of_nonneg (sub_nonneg.mpr hx2)]
      constructor <;> intro h <;> linarith

/-- Left chamber of the raw source-shift defect. -/
theorem cubicCriticalShiftLebesgueDefectDensity_neg_iff
    {L : ℝ} (hL : 0 < L) (x : ℝ) :
    cubicCriticalShiftLebesgueDefectDensity L x < 0 ↔
      x < 3 * L / 2 := by
  rw [cubicCriticalShiftLebesgueDefectDensity, sub_neg,
    Real.exp_lt_exp, abs_sub_dyadic_lt_iff hL]

/-- Right chamber of the raw source-shift defect. -/
theorem cubicCriticalShiftLebesgueDefectDensity_pos_iff
    {L : ℝ} (hL : 0 < L) (x : ℝ) :
    0 < cubicCriticalShiftLebesgueDefectDensity L x ↔
      3 * L / 2 < x := by
  rw [cubicCriticalShiftLebesgueDefectDensity, sub_pos,
    Real.exp_lt_exp, abs_dyadic_sub_lt_iff hL]

/-- The unique zero of the raw defect is the reflection wall. -/
theorem cubicCriticalShiftLebesgueDefectDensity_eq_zero_iff
    {L : ℝ} (hL : 0 < L) (x : ℝ) :
    cubicCriticalShiftLebesgueDefectDensity L x = 0 ↔
      x = 3 * L / 2 := by
  constructor
  · intro hzero
    rcases lt_trichotomy x (3 * L / 2) with hlt | heq | hgt
    · have hneg := (cubicCriticalShiftLebesgueDefectDensity_neg_iff hL x).2 hlt
      linarith
    · exact heq
    · have hpos := (cubicCriticalShiftLebesgueDefectDensity_pos_iff hL x).2 hgt
      linarith
  · rintro rfl
    rw [cubicCriticalShiftLebesgueDefectDensity]
    have h1 : 3 * L / 2 - L = L / 2 := by ring
    have h2 : 3 * L / 2 - 2 * L = -(L / 2) := by ring
    rw [h1, h2, abs_neg, sub_self]

/-- The critical half-density does not repair the negative chamber. -/
theorem cubicCriticalShiftPulledDefectDensity_neg_iff
    {L : ℝ} (hL : 0 < L) (x : ℝ) :
    cubicCriticalShiftPulledDefectDensity L x < 0 ↔
      x < 3 * L / 2 := by
  rw [cubicCriticalShiftPulledDefectDensity_eq]
  constructor
  · intro hneg
    apply (cubicCriticalShiftLebesgueDefectDensity_neg_iff hL x).1
    by_contra hnot
    have hnonneg : 0 ≤ cubicCriticalShiftLebesgueDefectDensity L x :=
      le_of_not_gt hnot
    exact (not_lt_of_ge (mul_nonneg (Real.exp_nonneg _) hnonneg)) hneg
  · intro hx
    exact mul_neg_of_pos_of_neg (Real.exp_pos _)
      ((cubicCriticalShiftLebesgueDefectDensity_neg_iff hL x).2 hx)

/-- The critical half-density does not repair the positive chamber. -/
theorem cubicCriticalShiftPulledDefectDensity_pos_iff
    {L : ℝ} (hL : 0 < L) (x : ℝ) :
    0 < cubicCriticalShiftPulledDefectDensity L x ↔
      3 * L / 2 < x := by
  rw [cubicCriticalShiftPulledDefectDensity_eq,
    mul_pos_iff_of_pos_left (Real.exp_pos _),
    cubicCriticalShiftLebesgueDefectDensity_pos_iff hL]

/-- Unconditional two-sign obstruction: at every positive scale, the actual pulled critical-shift
defect has a negative source cell and a positive source cell. -/
theorem cubicCriticalShiftPulledDefectDensity_has_both_signs :
    ∀ L : ℝ, 0 < L →
      cubicCriticalShiftPulledDefectDensity L L < 0 ∧
        0 < cubicCriticalShiftPulledDefectDensity L (2 * L) := by
  intro L hL
  constructor
  · exact (cubicCriticalShiftPulledDefectDensity_neg_iff hL L).2 (by linarith)
  · exact (cubicCriticalShiftPulledDefectDensity_pos_iff hL (2 * L)).2 (by linarith)

end HedenmalmThetaSource

end

end RHTower
