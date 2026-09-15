import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleWallFieldWeld
import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeCesaroAnchoredMoment
import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeFixedRectangularMixture

/-!
# Restricted-Weil pole / CCM-FU hyperbolic Green weld

The normalized `(1 - d²/ds²)` residual of one literal odd restricted-Weil
pole response is exactly the raw CCM-FU triangular prime weight.  At half
aperture `s = H / 2`, the identity is coefficient-faithful for every atom and
hence for the complete finite prime channel.  The final theorem keeps that
channel coupled to the literal polar continuum inside the actual anchored FU
moment.
-/

open Set MeasureTheory
open scoped BigOperators
noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- Hyperbolically normalized odd-pole Green residual. -/
def ccmWeilOddNormalizedGreenResidual (n : ℕ) (s : ℝ) : ℝ :=
  (ccmWeilOddWallEnergyResponse n s -
      deriv (deriv (ccmWeilOddWallEnergyResponse n)) s) /
    (4 * Real.cosh (Real.log n / 2))

/-- The normalized odd-pole Green residual is a literal affine clock deficit. -/
theorem ccmWeilOddNormalizedGreenResidual_eq_linear (n : ℕ) (s : ℝ) :
    ccmWeilOddNormalizedGreenResidual n s = 2 * s - Real.log n := by
  exact ccmWeilOddWallEnergyResponse_normalized_green_triangle n s

/-- Half-aperture pole residual is the uncut FU triangular factor. -/
theorem ccmWeilOddNormalizedGreenResidual_half_aperture (n : ℕ) (H : ℝ) :
    ccmWeilOddNormalizedGreenResidual n (H / 2) = H - Real.log n := by
  rw [ccmWeilOddNormalizedGreenResidual_eq_linear]
  ring

/-- On the actual finite head, the positive-lag rectangular triangle is the pole Green residual. -/
theorem ccmPositiveLagRectangularTriangle_eq_oddPoleGreenResidual
    {n : ℕ} {H : ℝ} (hn : n ∈ Finset.Icc 2 ⌊Real.exp H⌋₊) :
    ccmPositiveLagRectangularTriangle H (Real.log n) =
      ccmWeilOddNormalizedGreenResidual n (H / 2) := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two (Finset.mem_Icc.mp hn).1)
  have hnexp : (n : ℝ) ≤ Real.exp H :=
    (Nat.le_floor_iff (Real.exp_pos H).le).mp (Finset.mem_Icc.mp hn).2
  have hlogH : Real.log n ≤ H :=
    (Real.log_le_iff_le_exp hnpos).mpr hnexp
  rw [ccmWeilOddNormalizedGreenResidual_half_aperture]
  simp [ccmPositiveLagRectangularTriangle, sub_nonneg.mpr hlogH]

/-- Exact cubic CCM-FU coefficient on one normalized odd-pole Green residual. -/
theorem criticalMellinAtomWeight_mul_thirdGradeTriangularWeight_eq_oddPoleGreenResidual
    {n : ℕ} {H : ℝ} (hn : 2 ≤ n) (hH : H ≠ 0) :
    criticalMellinAtomWeight n *
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H (Real.log n) =
      criticalMellinAtomWeight n * (32 / (H * (Real.log n) ^ 3)) *
        ccmWeilOddNormalizedGreenResidual n (H / 2) := by
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log n ≠ 0 := ne_of_gt (Real.log_pos hnreal)
  rw [ccmWeilOddNormalizedGreenResidual_half_aperture]
  unfold ccmGuinandWeilThirdGradeCesaroTriangularWeight
    ccmGuinandWeilThirdGradeWeight
  field_simp [hH, hlog]

/-- Actual finite FU prime channel written as normalized odd-pole Green residuals. -/
def ccmWeilOddThirdGradeGreenResidualPrimeWindow (b H : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
    if b < Real.log n then
      criticalMellinAtomWeight n * (32 / (H * (Real.log n) ^ 3)) *
        ccmWeilOddNormalizedGreenResidual n (H / 2)
    else 0

/-- The whole finite third-grade prime window is the coefficient-faithful pole Green residual. -/
theorem ccmGuinandWeilThirdGradePrimeWindow_eq_oddPoleGreenResidual
    {b H : ℝ} (hH : 0 < H) :
    (∑ n ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if b < Real.log n then
          criticalMellinAtomWeight n *
            ccmGuinandWeilThirdGradeCesaroTriangularWeight H (Real.log n)
        else 0) =
      ccmWeilOddThirdGradeGreenResidualPrimeWindow b H := by
  unfold ccmWeilOddThirdGradeGreenResidualPrimeWindow
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hbn : b < Real.log n
  · rw [if_pos hbn, if_pos hbn]
    exact criticalMellinAtomWeight_mul_thirdGradeTriangularWeight_eq_oddPoleGreenResidual
      (Finset.mem_Icc.mp hn).1 hH.ne'
  · simp [hbn]

/-- Literal triangular prime-minus-polar window in odd-pole Green coordinates. -/
theorem ccmGuinandWeilPrimePolarTriangularWindow_eq_oddPoleGreenResidual_sub_polar
    {b H : ℝ} (hH : 0 < H) :
    ccmGuinandWeilPrimePolarWeightedWindow b H
        (ccmGuinandWeilThirdGradeCesaroTriangularWeight H) =
      ccmWeilOddThirdGradeGreenResidualPrimeWindow b H -
        ∫ h in b..H,
          ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
            (2 * Real.cosh (h / 2)) := by
  rw [ccmGuinandWeilPrimePolarWeightedWindow,
    ccmGuinandWeilThirdGradePrimeWindow_eq_oddPoleGreenResidual hH]

/-- RH-bearing anchored FU moment as one signed pole-Green/polar residual current. -/
theorem ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_oddPoleGreenResidual_sub_polar
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H =
      ccmWeilOddThirdGradeGreenResidualPrimeWindow b H -
        ∫ h in b..H,
          ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
            (2 * Real.cosh (h / 2)) := by
  rw [ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_primePolarTriangularWindow hb hbH]
  exact ccmGuinandWeilPrimePolarTriangularWindow_eq_oddPoleGreenResidual_sub_polar
    (hb.trans_le hbH)

end GaloisForLFunctions.RHTower
