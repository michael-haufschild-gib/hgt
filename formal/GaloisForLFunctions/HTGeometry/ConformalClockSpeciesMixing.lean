import GaloisForLFunctions.HTGeometry.ConformalClockScaleBlindness

/-!
# Species mixing must be diagonalized before the scale law is applied

The two-species scale law divides the potential difference by the difference of the two calibrated
squared masses. With a non-diagonal mass matrix the physical species are the eigenvectors, and the
calibrated masses are the eigenvalues, not the diagonal entries of the matrix in the reporter
basis.

This file proves the resulting failure mode exactly. For a real symmetric mass matrix with diagonal
entries `a, d` and mixing `b`, the eigenvalue gap is `√((a-d)² + 4b²)`. It equals the naive channel
gap `|a - d|` precisely when the mixing vanishes, and strictly exceeds it otherwise. Dividing by the
naive gap therefore returns a strictly overestimated conformal scale.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Spectral gap of a real symmetric mass matrix with diagonal entries `a, d` and mixing `b`. -/
noncomputable def massMixingGap (a b d : ℝ) : ℝ :=
  Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2)

/-- Upper calibrated squared mass of a mixed clock pair. -/
noncomputable def massEigenvalueHigh (a b d : ℝ) : ℝ :=
  ((a + d) + massMixingGap a b d) / 2

/-- Lower calibrated squared mass of a mixed clock pair. -/
noncomputable def massEigenvalueLow (a b d : ℝ) : ℝ :=
  ((a + d) - massMixingGap a b d) / 2

theorem massMixingGap_nonneg (a b d : ℝ) : 0 ≤ massMixingGap a b d :=
  Real.sqrt_nonneg _

theorem sq_massMixingGap (a b d : ℝ) :
    massMixingGap a b d ^ 2 = (a - d) ^ 2 + 4 * b ^ 2 := by
  refine Real.sq_sqrt ?_
  positivity

/-- The upper eigenvalue is a root of the characteristic polynomial. -/
theorem massEigenvalueHigh_isRoot (a b d : ℝ) :
    massEigenvalueHigh a b d ^ 2 - (a + d) * massEigenvalueHigh a b d + (a * d - b ^ 2) = 0 := by
  have hsq := sq_massMixingGap a b d
  simp only [massEigenvalueHigh]
  nlinarith [hsq]

/-- The lower eigenvalue is a root of the characteristic polynomial. -/
theorem massEigenvalueLow_isRoot (a b d : ℝ) :
    massEigenvalueLow a b d ^ 2 - (a + d) * massEigenvalueLow a b d + (a * d - b ^ 2) = 0 := by
  have hsq := sq_massMixingGap a b d
  simp only [massEigenvalueLow]
  nlinarith [hsq]

/-- The calibrated mass difference of a mixed pair is its spectral gap. -/
theorem massEigenvalue_difference (a b d : ℝ) :
    massEigenvalueHigh a b d - massEigenvalueLow a b d = massMixingGap a b d := by
  simp only [massEigenvalueHigh, massEigenvalueLow]
  ring

/-- **The naive channel gap is the true calibrated gap exactly when the mixing vanishes.** -/
theorem massMixingGap_eq_abs_sub_iff (a b d : ℝ) :
    massMixingGap a b d = |a - d| ↔ b = 0 := by
  constructor
  · intro hEq
    have hsq := sq_massMixingGap a b d
    rw [hEq, sq_abs] at hsq
    have hb : b ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hb
  · intro hb
    simp only [massMixingGap, hb]
    rw [show (a - d) ^ 2 + 4 * (0 : ℝ) ^ 2 = (a - d) ^ 2 by ring]
    exact Real.sqrt_sq_eq_abs _

/-- **Mixing strictly widens the calibrated mass gap.** -/
theorem abs_sub_lt_massMixingGap {a b d : ℝ} (hb : b ≠ 0) :
    |a - d| < massMixingGap a b d := by
  have hlt : (a - d) ^ 2 < (a - d) ^ 2 + 4 * b ^ 2 := by
    have : 0 < b ^ 2 := pow_pos (abs_pos.mpr hb) 2 |>.trans_le (le_of_eq (sq_abs b))
    linarith
  calc |a - d| = Real.sqrt ((a - d) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ < massMixingGap a b d := Real.sqrt_lt_sqrt (sq_nonneg _) hlt

/-- **Correct reconstruction after diagonalization.** Dividing the potential difference of the two
mass eigenstates by their spectral gap returns the conformal scale. -/
theorem conformalPotentialData_mixed_reconstruction (weight a b d scale defectLaplace
    defectGradient : ℝ) (hgap : massMixingGap a b d ≠ 0) :
    (conformalPotentialData weight (massEigenvalueHigh a b d) scale defectLaplace
          defectGradient -
        conformalPotentialData weight (massEigenvalueLow a b d) scale defectLaplace
          defectGradient) /
        (massEigenvalueHigh a b d - massEigenvalueLow a b d) = scale := by
  rw [conformalPotentialData_difference, massEigenvalue_difference]
  field_simp

/-- **Using un-diagonalized channel labels overestimates the conformal scale.**

The measured potential difference divided by the naive channel gap `|a - d|` is the true scale
multiplied by the ratio of the spectral gap to the naive gap, which strictly exceeds one whenever
the species mix. -/
theorem conformalPotentialData_mixed_naive_overestimate (weight a b d scale defectLaplace
    defectGradient : ℝ) (hb : b ≠ 0) (had : a ≠ d) (hscale : 0 < scale) :
    scale <
      (conformalPotentialData weight (massEigenvalueHigh a b d) scale defectLaplace
            defectGradient -
          conformalPotentialData weight (massEigenvalueLow a b d) scale defectLaplace
            defectGradient) / |a - d| := by
  rw [conformalPotentialData_difference, massEigenvalue_difference]
  have habs : 0 < |a - d| := abs_pos.mpr (sub_ne_zero.mpr had)
  rw [lt_div_iff₀ habs]
  have hgap := abs_sub_lt_massMixingGap (a := a) (d := d) hb
  nlinarith [hgap, habs, hscale]

/-- **A mixed pair never reconstructs the scale from raw channel labels.** -/
theorem conformalPotentialData_mixed_naive_ne (weight a b d scale defectLaplace
    defectGradient : ℝ) (hb : b ≠ 0) (had : a ≠ d) (hscale : 0 < scale) :
    (conformalPotentialData weight (massEigenvalueHigh a b d) scale defectLaplace
          defectGradient -
        conformalPotentialData weight (massEigenvalueLow a b d) scale defectLaplace
          defectGradient) / |a - d| ≠ scale := by
  intro hEq
  have hlt := conformalPotentialData_mixed_naive_overestimate weight a b d scale defectLaplace
    defectGradient hb had hscale
  rw [hEq] at hlt
  exact lt_irrefl scale hlt

end GaloisForLFunctions.HTGeometry
