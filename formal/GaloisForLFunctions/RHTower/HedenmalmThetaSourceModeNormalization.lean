import GaloisForLFunctions.RHTower.HedenmalmThetaRootEndpoints

/-!
# Canonical normalization of the theta-source divisor mode

At a zero of the completed theta-source transform, the explicit two-ended mode
`u_z = sourceModeU thetaSource z` decays exponentially.  This closes the two analytic hypotheses
previously left on the divisor-to-eigenvector map:

* `f_z = -z u_z` is integrable;
* its total integral is exactly the source mass.

Indeed `u_z' = D_z`, `f_z = -i D_z + k`, and the two endpoint values of `u_z` vanish, so the
whole-line fundamental theorem of calculus gives `∫ D_z = 0` and hence `∫ f_z = ∫ k = M`.
Consequently every theta-source divisor in the strip produces a genuine eigenfunction of the
source inverse, with no assumed endpoint normalization or integrability data.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmPrimeTranslation

/-- The source-pointed mode at a theta-source zero is Lebesgue integrable. -/
theorem integrable_sourceModeU_thetaSource {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    Integrable (sourceModeU thetaSource z) (volume : Measure ℝ) := by
  have hgap : (0 : ℝ) < 1 - |z.im| := by linarith
  have hC : 0 ≤ thetaBound / (1 - |z.im|) :=
    div_nonneg thetaBound_nonneg hgap.le
  have hmajor : Integrable
      (fun x : ℝ => thetaBound / (1 - |z.im|) * Real.exp (-|x|))
      (volume : Measure ℝ) := by
    simpa using
      (integrable_exp_neg_mul_abs (c := (1 : ℝ)) one_pos).const_mul
        (thetaBound / (1 - |z.im|))
  refine hmajor.mono' (continuous_sourceModeU hz).aestronglyMeasurable ?_
  filter_upwards with x
  exact norm_sourceModeU_le hz hzero x

/-- The right mode `f_z = -z u_z` at a theta-source zero is Lebesgue integrable. -/
theorem integrable_sourceModeF_thetaSource {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    Integrable (sourceModeF thetaSource z) (volume : Measure ℝ) := by
  refine ((integrable_sourceModeU_thetaSource hz hzero).const_mul (-z)).congr ?_
  filter_upwards with x
  rw [sourceModeF]

/-- The theta-source mode vanishes at the left endpoint. -/
theorem tendsto_sourceModeU_thetaSource_atBot {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    Tendsto (sourceModeU thetaSource z) atBot (𝓝 0) := by
  refine squeeze_zero_norm (fun x => norm_sourceModeU_le hz hzero x) ?_
  have habs : Tendsto (fun x : ℝ => -|x|) atBot atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_abs_atBot_atTop
  simpa using (Real.tendsto_exp_atBot.comp habs).const_mul
    (thetaBound / (1 - |z.im|))

/-- The theta-source mode vanishes at the right endpoint. -/
theorem tendsto_sourceModeU_thetaSource_atTop {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    Tendsto (sourceModeU thetaSource z) atTop (𝓝 0) := by
  refine squeeze_zero_norm (fun x => norm_sourceModeU_le hz hzero x) ?_
  have habs : Tendsto (fun x : ℝ => -|x|) atTop atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_abs_atTop_atTop
  simpa using (Real.tendsto_exp_atBot.comp habs).const_mul
    (thetaBound / (1 - |z.im|))

/-- **Canonical source-mode normalization.**  At every theta-source zero in the strip, the right
mode carries exactly the full source mass.  The equality is forced by the two endpoint values and
is not an additional eigenvector hypothesis. -/
theorem integral_sourceModeF_thetaSource_eq_mass {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    (∫ x, sourceModeF thetaSource z x) = (thetaSource.mass : ℂ) := by
  have hf := integrable_sourceModeF_thetaSource hz hzero
  have hk : Integrable (fun x : ℝ => (thetaSource.k x : ℂ))
      (volume : Measure ℝ) := thetaSource.integrable_k.ofReal
  have hD : Integrable (sourceModeD thetaSource z) (volume : Measure ℝ) := by
    refine ((hf.sub hk).const_mul Complex.I).congr ?_
    filter_upwards with x
    exact (sourceModeD_eq thetaSource z x).symm
  have hzeroD : (∫ x, sourceModeD thetaSource z x) = 0 := by
    have h := MeasureTheory.integral_of_hasDerivAt_of_tendsto
      (hasDerivAt_sourceModeU thetaSource (hasShiftedTail_thetaSource hz)) hD
      (tendsto_sourceModeU_thetaSource_atBot hz hzero)
      (tendsto_sourceModeU_thetaSource_atTop hz hzero)
    simpa only [sourceModeD, sub_zero] using h
  calc
    (∫ x, sourceModeF thetaSource z x) =
        ∫ x, (-Complex.I * sourceModeD thetaSource z x + (thetaSource.k x : ℂ)) := by
      refine integral_congr_ae ?_
      filter_upwards with x
      exact sourceModeF_eq_neg_I_mul_D thetaSource z x
    _ = -Complex.I * (∫ x, sourceModeD thetaSource z x)
          + ∫ x, (thetaSource.k x : ℂ) := by
      rw [MeasureTheory.integral_add (hD.const_mul (-Complex.I)) hk,
        MeasureTheory.integral_const_mul]
    _ = (thetaSource.mass : ℂ) := by
      rw [hzeroD, mul_zero, zero_add, integral_complex_ofReal]
      rfl

/-- Zero is not a theta-source divisor: the completed transform there is the positive source
mass. -/
theorem ne_zero_of_xiC_thetaSource_eq_zero {z : ℂ}
    (hzero : xiC thetaSource z = 0) : z ≠ 0 := by
  intro hz0
  subst z
  apply thetaSource.mass_ne_zero
  change (∫ x : ℝ, thetaCuspFullSource x) = 0
  simpa [xiC, sourceChar, integral_complex_ofReal] using hzero

/-- The explicit source inverse recovers the two-ended theta mode with all analytic inputs proved. -/
theorem sourceInverse_sourceModeF_thetaSource {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) (x : ℝ) :
    sourceInverse thetaSource (sourceModeF thetaSource z) x =
      sourceModeU thetaSource z x :=
  sourceInverse_sourceModeF thetaSource (hasShiftedTail_thetaSource hz)
    (integrable_sourceModeF_thetaSource hz hzero)
    (tendsto_sourceModeU_thetaSource_atBot hz hzero)
    (integral_sourceModeF_thetaSource_eq_mass hz hzero) x

/-- **Hypothesis-free divisor-to-eigenfunction map.**  Every theta-source divisor in the strip
produces the explicit source-inverse eigenfunction with eigenvalue `-z⁻¹`. -/
theorem sourceInverse_sourceModeF_eq_smul_thetaSource {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) (x : ℝ) :
    sourceInverse thetaSource (sourceModeF thetaSource z) x =
      (-z⁻¹) * sourceModeF thetaSource z x := by
  rw [sourceInverse_sourceModeF_thetaSource hz hzero, sourceModeF]
  field_simp [ne_zero_of_xiC_thetaSource_eq_zero hzero]

end HedenmalmThetaSource

end

end RHTower
