import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinLineInvariance
import GaloisForLFunctions.RHTower.EisensteinLineTailParseval

/-!
# Zero mean of the Eisenstein cusp tail over a period, for every parameter

For every parameter `u ∈ ℂ` and every height `Y > 0`, the nonconstant part of the completed
Eisenstein Fourier model has zero mean in `x` over one period:
`∫_0^(1 : ℕ) tail_u(x, Y) dx = 0`, hence `∫_0^(1 : ℕ) E*(u; x, Y) dx = c_u(Y)` (the Weyl constant part).
This generalises `setIntegral_Ioc_cuspTailPart` (which was stated on the line `u = it`) using the
uniform majorant `eisensteinTailMajorant` of the line-invariance module.
-/

open Complex MeasureTheory Set Filter Topology intervalIntegral
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- The `x`-free amplitude of a tail term. -/
def eisensteinTailAmplitude (Y : ℝ) (N : ℕ) (u : ℂ) : ℂ :=
  d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ * (Real.sqrt Y : ℂ) *
    modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * Y) u

theorem eisensteinTailTerm_eq_amplitude_mul_phase (negative : Bool) (x Y : ℝ) (N : ℕ) (u : ℂ) :
    eisensteinTailTerm negative x Y N u =
      eisensteinTailAmplitude Y N u * d4BMCompletedEisensteinFourierPhase negative N x := by
  unfold eisensteinTailTerm eisensteinTailAmplitude
  simp only [pow_zero, mul_one]
  ring

theorem continuous_fourierPhase (negative : Bool) (N : ℕ) :
    Continuous (d4BMCompletedEisensteinFourierPhase negative N) := by
  unfold d4BMCompletedEisensteinFourierPhase
  fun_prop

theorem continuous_eisensteinTailTerm_x' (negative : Bool) (Y : ℝ) (N : ℕ) (u : ℂ) :
    Continuous (fun x => eisensteinTailTerm negative x Y N u) := by
  simp_rw [eisensteinTailTerm_eq_amplitude_mul_phase]
  exact continuous_const.mul (continuous_fourierPhase negative N)

theorem setIntegral_Ioc_eisensteinTailTerm' (negative : Bool) (Y : ℝ) (N : ℕ) (u : ℂ) :
    ∫ x in Ioc (0 : ℝ) 1, eisensteinTailTerm negative x Y N u = 0 := by
  rw [← integral_of_le zero_le_one]
  simp_rw [eisensteinTailTerm_eq_amplitude_mul_phase]
  rw [intervalIntegral.integral_const_mul, intervalIntegral_fourierPhase, mul_zero]

/-- The signed tail is a continuous function of `x` (uniform convergence on the period). -/
theorem continuous_signedSqrtWhittakerTail_x (negative : Bool) {Y : ℝ} (hY : 0 < Y) (u : ℂ) :
    Continuous (fun x => d4BMCompletedEisensteinSignedSqrtWhittakerTail u u negative x 0 0 Y) := by
  simp_rw [signedSqrtWhittakerTail_eq_tsum_term]
  exact continuous_tsum (fun N => continuous_eisensteinTailTerm_x' negative Y N u)
    (summable_eisensteinTailMajorant hY u)
    (fun N x => norm_eisensteinTailTerm_le negative x hY u N (Metric.mem_ball_self one_pos))

/-- **Zero mean of a signed tail** over one period, for every parameter. -/
theorem setIntegral_Ioc_signedSqrtWhittakerTail (negative : Bool) {Y : ℝ} (hY : 0 < Y) (u : ℂ) :
    ∫ x in Ioc (0 : ℝ) 1,
      d4BMCompletedEisensteinSignedSqrtWhittakerTail u u negative x 0 0 Y = 0 := by
  simp_rw [signedSqrtWhittakerTail_eq_tsum_term]
  have hint : ∀ N : ℕ, Integrable (fun x => eisensteinTailTerm negative x Y N u)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    fun N => (continuous_eisensteinTailTerm_x' negative Y N u).integrableOn_Ioc
  have hsum : Summable (fun N : ℕ =>
      ∫ x in Ioc (0 : ℝ) 1, ‖eisensteinTailTerm negative x Y N u‖) := by
    refine Summable.of_nonneg_of_le (fun N => integral_nonneg fun x => norm_nonneg _)
      (fun N => ?_) (summable_eisensteinTailMajorant hY u)
    calc ∫ x in Ioc (0 : ℝ) 1, ‖eisensteinTailTerm negative x Y N u‖
        ≤ ∫ x in Ioc (0 : ℝ) 1, eisensteinTailMajorant Y u N := by
          refine setIntegral_mono_on (hint N).norm (integrableOn_const (by simp))
            measurableSet_Ioc fun x _ => ?_
          exact norm_eisensteinTailTerm_le negative x hY u N (Metric.mem_ball_self one_pos)
      _ = eisensteinTailMajorant Y u N := by simp
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [setIntegral_Ioc_eisensteinTailTerm']
  exact tsum_zero

theorem cuspTailPart_scalar_eq (u : ℂ) (x Y : ℝ) :
    d4BMCompletedEisensteinCuspTailPart .scalar u x Y =
      2 * (d4BMCompletedEisensteinSignedSqrtWhittakerTail u u false x 0 0 Y +
        d4BMCompletedEisensteinSignedSqrtWhittakerTail u u true x 0 0 Y) := rfl

theorem continuous_cuspTailPart_x' {Y : ℝ} (hY : 0 < Y) (u : ℂ) :
    Continuous (fun x => d4BMCompletedEisensteinCuspTailPart .scalar u x Y) := by
  simp_rw [cuspTailPart_scalar_eq]
  exact continuous_const.mul ((continuous_signedSqrtWhittakerTail_x false hY u).add
    (continuous_signedSqrtWhittakerTail_x true hY u))

/-- **Zero mean of the cusp tail** over one period, for every parameter. -/
theorem setIntegral_Ioc_cuspTailPart' {Y : ℝ} (hY : 0 < Y) (u : ℂ) :
    ∫ x in Ioc (0 : ℝ) 1, d4BMCompletedEisensteinCuspTailPart .scalar u x Y = 0 := by
  simp_rw [cuspTailPart_scalar_eq]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add,
    setIntegral_Ioc_signedSqrtWhittakerTail false hY u,
    setIntegral_Ioc_signedSqrtWhittakerTail true hY u]
  · simp
  · exact (continuous_signedSqrtWhittakerTail_x false hY u).integrableOn_Ioc
  · exact (continuous_signedSqrtWhittakerTail_x true hY u).integrableOn_Ioc

/-- The Fourier model is continuous in `x` at every height and parameter. -/
theorem continuous_cuspLeg_x' {Y : ℝ} (hY : 0 < Y) (u : ℂ) :
    Continuous (fun x => d4BMCompletedEisensteinCuspLeg .scalar u x Y) := by
  unfold d4BMCompletedEisensteinCuspLeg
  exact continuous_const.add (continuous_cuspTailPart_x' hY u)

/-- **The period mean of the Fourier model is its Weyl constant part.** -/
theorem setIntegral_Ioc_cuspLeg {Y : ℝ} (hY : 0 < Y) (u : ℂ) :
    ∫ x in Ioc (0 : ℝ) 1, d4BMCompletedEisensteinCuspLeg .scalar u x Y =
      d4BMCompletedEisensteinCuspConstantPart .scalar u Y := by
  unfold d4BMCompletedEisensteinCuspLeg
  have hc : Integrable (fun _ : ℝ => d4BMCompletedEisensteinCuspConstantPart .scalar u Y)
      (volume.restrict (Ioc (0 : ℝ) 1)) := integrableOn_const (by simp)
  rw [MeasureTheory.integral_add hc (continuous_cuspTailPart_x' hY u).integrableOn_Ioc,
    setIntegral_Ioc_cuspTailPart' hY u, add_zero]
  simp

end

end RHTower
