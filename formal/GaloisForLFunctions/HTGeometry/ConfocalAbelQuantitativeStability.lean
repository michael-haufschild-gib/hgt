import GaloisForLFunctions.HTGeometry.ConfocalAbelDefectFlow

/-!
# Quantitative stability of the confocal amplitude and Abel flow

The qualitative recession laws follow from convergence of the confocal defect envelope.  Here we
retain the finite-scale error.  The source collar is transported through exact rational identities
for the squared amplitude and Abel radius, and the squared-amplitude recession receives an
explicit two-sided error bound.
-/

open Complex

namespace HTGeometry

noncomputable section

/-- The confocal defect envelope of a radius-`M` source never exceeds `2M`. -/
theorem confocalDefectEnvelope_le_two_mul_bound
    {S : Set ℂ} (hne : S.Nonempty) {M R : ℝ}
    (hR : 0 ≤ R) (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    confocalDefectEnvelope S R ≤ 2 * M := by
  rw [confocalDefectEnvelope]
  apply csSup_le (hne.image _)
  rintro y ⟨z, hz, rfl⟩
  exact (confocalDefect_le_two_mul_norm hR z).trans
    (mul_le_mul_of_nonneg_left (hbound z hz) (by norm_num))

/-- Exact finite-scale form of the squared-amplitude recession. -/
theorem mul_confocalAmplitudeEnvelope_sq_sub_one_eq
    (S : Set ℂ) {R : ℝ} (hR : 0 < R) :
    R * (confocalAmplitudeEnvelope S R ^ (2 : ℕ) - 1) =
      2 * confocalDefectEnvelope S R +
        confocalDefectEnvelope S R ^ (2 : ℕ) / R := by
  rw [confocalAmplitudeEnvelope]
  field_simp [hR.ne']
  ring

/-- **Explicit squared-amplitude stability collar.**  At every scale beyond a radius-`M`
source, the first recession differs from `2 Delta` by a nonnegative quantity bounded by an
explicit rational error. -/
theorem mul_confocalAmplitudeEnvelope_sq_sub_one_error_bounds
    {S : Set ℂ} (hne : S.Nonempty) {M R : ℝ}
    (hM : 0 ≤ M) (hRM : M < R) (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    0 ≤
        R * (confocalAmplitudeEnvelope S R ^ (2 : ℕ) - 1) -
          2 * transverseDefectEnvelope S ∧
      R * (confocalAmplitudeEnvelope S R ^ (2 : ℕ) - 1) -
          2 * transverseDefectEnvelope S ≤
        M ^ (2 : ℕ) / (R - M) + 4 * M ^ (2 : ℕ) / R := by
  let D : ℝ := confocalDefectEnvelope S R
  let delta : ℝ := transverseDefectEnvelope S
  have hR : 0 < R := hM.trans_lt hRM
  have hcollar :=
    transverseDefectEnvelope_le_confocalDefectEnvelope_le hne hM hRM hbound
  have hD0 : 0 ≤ D := by
    exact confocalDefectEnvelope_nonneg hne hR.le hbound
  have hD2M : D ≤ 2 * M := by
    exact confocalDefectEnvelope_le_two_mul_bound hne hR.le hbound
  have hDsq : D ^ (2 : ℕ) ≤ 4 * M ^ (2 : ℕ) := by nlinarith
  have hgap0 : 0 ≤ D - delta := by
    simpa only [D, delta] using sub_nonneg.mpr hcollar.1
  have hgap : D - delta ≤ M ^ (2 : ℕ) / (2 * (R - M)) := by
    dsimp only [D, delta]
    linarith [hcollar.2]
  rw [mul_confocalAmplitudeEnvelope_sq_sub_one_eq S hR]
  change 0 ≤ 2 * D + D ^ (2 : ℕ) / R - 2 * delta ∧
    2 * D + D ^ (2 : ℕ) / R - 2 * delta ≤
      M ^ (2 : ℕ) / (R - M) + 4 * M ^ (2 : ℕ) / R
  constructor
  · have hdiv0 : 0 ≤ D ^ (2 : ℕ) / R := div_nonneg (sq_nonneg D) hR.le
    linarith
  · have hgap2 : 2 * (D - delta) ≤ M ^ (2 : ℕ) / (R - M) := by
      have hden : 0 < R - M := sub_pos.mpr hRM
      calc
        2 * (D - delta) ≤ 2 * (M ^ (2 : ℕ) / (2 * (R - M))) := by linarith
        _ = M ^ (2 : ℕ) / (R - M) := by field_simp [hden.ne']
    have hdiv : D ^ (2 : ℕ) / R ≤ 4 * M ^ (2 : ℕ) / R :=
      div_le_div_of_nonneg_right hDsq hR.le
    linarith

/-- Exact finite-scale transport from the confocal defect envelope to the Abel-radius
recession. -/
theorem mul_one_sub_confocalAbelRadius_eq
    {S : Set ℂ} (hne : S.Nonempty) {M R : ℝ}
    (hM : 0 ≤ M) (hRM : M < R) (hbound : ∀ z ∈ S, ‖z‖ ≤ M) :
    R * (1 - confocalAbelRadius S R) =
      (2 * confocalDefectEnvelope S R +
          confocalDefectEnvelope S R ^ (2 : ℕ) / R) /
        (1 + confocalDefectEnvelope S R / R) ^ (2 : ℕ) := by
  let B : ℝ := confocalAmplitudeEnvelope S R
  have hR : 0 < R := hM.trans_lt hRM
  have hD0 : 0 ≤ confocalDefectEnvelope S R :=
    confocalDefectEnvelope_nonneg hne hR.le hbound
  have hB : 0 < B := by
    dsimp only [B, confocalAmplitudeEnvelope]
    positivity
  calc
    R * (1 - confocalAbelRadius S R) = R * (B ^ (2 : ℕ) - 1) / B ^ (2 : ℕ) := by
      rw [confocalAbelRadius]
      change R * (1 - (B ^ (2 : ℕ))⁻¹) = R * (B ^ (2 : ℕ) - 1) / B ^ (2 : ℕ)
      field_simp [hB.ne']
    _ = (2 * confocalDefectEnvelope S R +
          confocalDefectEnvelope S R ^ (2 : ℕ) / R) / B ^ (2 : ℕ) := by
      rw [mul_confocalAmplitudeEnvelope_sq_sub_one_eq S hR]
    _ = (2 * confocalDefectEnvelope S R +
          confocalDefectEnvelope S R ^ (2 : ℕ) / R) /
        (1 + confocalDefectEnvelope S R / R) ^ (2 : ℕ) := by
      rfl

end

end HTGeometry
