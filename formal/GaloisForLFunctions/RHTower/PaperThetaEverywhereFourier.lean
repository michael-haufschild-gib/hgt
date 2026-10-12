import GaloisForLFunctions.RHTower.PaperThetaSeamFourier

/-! # Everywhere recovery after assigning the common trace at the seam

Only the representative's value at the seam changes. The literal source
coefficients and every symmetric partial sum are preserved.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open GaloisForLFunctions.HTGeometry FourierLLogL

def seamCorrectedCircleMode (z : ℂ) (x : Torus) : ℂ := by
  classical
  exact if x = Period.circle 0 then -1 else circleMode z x

private theorem circle_seam_null : circleMeasure {Period.circle 0} = 0 := by
  rw [← Period.map_circle_volume, Measure.map_apply Period.measurable_circle (measurableSet_singleton _),
    Period.μ₁, Measure.restrict_apply (Period.measurable_circle (measurableSet_singleton _))]
  have hs : Period.circle ⁻¹' {Period.circle 0} ∩ Period.unitInt = {0} := by
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨ht, hi⟩
      have h := congrArg Period.coord ht
      rw [Period.coord_circle_eq hi, Period.coord_circle_eq (by norm_num [Period.unitInt])] at h
      exact h
    · intro ht
      subst t
      exact ⟨rfl, by norm_num [Period.unitInt]⟩
  rw [hs, measure_singleton]

theorem seamCorrectedCircleMode_ae (z : ℂ) :
    seamCorrectedCircleMode z =ᵐ[circleMeasure] circleMode z := by
  have h : ∀ᵐ x : Torus ∂circleMeasure, x ≠ Period.circle 0 :=
    ae_iff.mpr (by simpa using circle_seam_null)
  filter_upwards [h] with x hx
  simp only [seamCorrectedCircleMode, if_neg hx]

/-- The corrected representative has exactly the original flat-source coefficients. -/
theorem fourierCoeff_seamCorrectedCircleMode (z : ℂ) (k : ℤ) :
    fourierCoeff (seamCorrectedCircleMode z) k = sourceCoeff z k := by
  have h : fourierCoeff (seamCorrectedCircleMode z) = fourierCoeff (circleMode z) :=
    _root_.fourierCoeff_congr_ae (T := 2*Real.pi) (f := seamCorrectedCircleMode z)
      (g := circleMode z) (seamCorrectedCircleMode_ae z)
  rw [h, fourierCoeff_eq_sourceCoeff_all]

theorem symmetricPartialSum_seamCorrectedCircleMode (z : ℂ) (N : ℕ) (x : Torus) :
    symmetricPartialSum (seamCorrectedCircleMode z) N x = symmetricPartialSum (circleMode z) N x :=
  symmetricPartialSum_congr_ae (seamCorrectedCircleMode_ae z) N x

theorem integrable_seamCorrectedCircleMode (z : {z : ℂ // XiC z = 0}) :
    Integrable (seamCorrectedCircleMode z.val) circleMeasure :=
  (integrable_circleMode_L1 ⟨z.val, Or.inr (Or.inl z.2)⟩).congr
    (seamCorrectedCircleMode_ae z.val).symm

private theorem coord_mem_unit (x : Torus) : Period.coord x ∈ Period.unitInt := by
  have hx := (AddCircle.measurableEquivIco (2*Real.pi) 0 x).property
  change 0 ≤ _ / (2*Real.pi) ∧ _ / (2*Real.pi) < 1
  constructor
  · exact div_nonneg hx.1 Real.two_pi_pos.le
  · apply (div_lt_one Real.two_pi_pos).mpr
    simpa only [zero_add] using hx.2

private theorem circle_coord (x : Torus) : Period.circle (Period.coord x) = x := by
  unfold Period.circle Period.coord
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ Real.two_pi_pos.ne']
  exact AddCircle.coe_equivIco

/-- Full symmetric partial sums recover every circle point at each actual Xi divisor point. -/
theorem circle_everywhere_recovery (z : {z : ℂ // XiC z = 0}) (x : Torus) :
    Tendsto (fun N : ℕ => symmetricPartialSum (seamCorrectedCircleMode z.val) N x)
      atTop (𝓝 (seamCorrectedCircleMode z.val x)) := by
  simp_rw [symmetricPartialSum_seamCorrectedCircleMode]
  by_cases hx : x = Period.circle 0
  · subst x
    simpa [seamCorrectedCircleMode] using circle_seam_recovery z
  · have hm := coord_mem_unit x
    have hn : Period.coord x ≠ 0 := by
      intro he
      apply hx
      rw [← circle_coord x, he]
    have ht : Period.coord x ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hm.1 (Ne.symm hn), hm.2⟩
    have h := circle_interior_recovery_L1 ⟨z.val, Or.inr (Or.inl z.2)⟩ ⟨Period.coord x, ht⟩
    rw [circle_coord] at h
    simpa only [seamCorrectedCircleMode, if_neg hx, circleMode] using h

/-- The unchanged literal source coefficients recover the seam trace as well. -/
theorem source_seam_recovery (z : {z : ℂ // XiC z = 0}) :
    Tendsto (fun N : ℕ => sourcePartialSum z.val N 0) atTop (𝓝 (-1)) := by
  simpa only [sourcePartialSum_eq_all] using circle_seam_recovery z

end RHTower.PaperThetaEndpoint
