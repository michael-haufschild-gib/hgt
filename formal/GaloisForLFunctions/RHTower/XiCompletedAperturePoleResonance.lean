import GaloisForLFunctions.RHTower.XiCompletedApertureReflectionKernel
import GaloisForLFunctions.RHTower.CompletedFluxCrossOrderReflection
import GaloisForLFunctions.RHTower.XiHedenmalmJordanNormalCollision
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- The real scalar carried by the reflection-odd completed aperture sector. -/
def xiCompletedApertureOddRealKernel (u x y : ℝ) : ℝ :=
  2 * (xiCompletedApertureOffDiagonalKernel u x y).re

theorem xiCompletedApertureOddKernel_eq_realKernel
    (u x y : ℝ) :
    xiCompletedApertureOddKernel u x y =
      (xiCompletedApertureOddRealKernel u x y : ℂ) := by
  exact xiCompletedApertureOddKernel_eq_two_re u x y

theorem xiCompletedApertureOddRealKernel_swap
    (u x y : ℝ) :
    xiCompletedApertureOddRealKernel u y x =
      xiCompletedApertureOddRealKernel u x y := by
  have h := xiCompletedApertureOddKernel_swap u x y
  rw [xiCompletedApertureOddKernel_eq_realKernel,
    xiCompletedApertureOddKernel_eq_realKernel] at h
  exact_mod_cast h

/-- The two-node determinant sampled at the ordinate of an actual Xi divisor point. -/
def xiCompletedApertureResonantTwoPointDet
    (rho : XiDivisorSupport) (epsilon : ℝ) : ℝ :=
  let u := (rho : ℂ).re - 1 / 2 + epsilon
  (xiCompletedApertureOddRealKernel u 0 0) ^ 2 -
    (xiCompletedApertureOddRealKernel u (rho : ℂ).im 0) ^ 2

/-- Residue-filled scaling of the resonant two-node determinant. -/
def xiCompletedApertureRegularizedResonantTwoPointDet
    (rho : XiDivisorSupport) (epsilon : ℝ) : ℝ :=
  (2 * epsilon *
      (seamFluxCochain ((((rho : ℂ).re + epsilon : ℝ) : ℂ))).re) ^ 2 -
    (2 * (completedFluxGermAt (rho : ℂ) (epsilon : ℂ)).re) ^ 2

theorem xiCompletedApertureOffDiagonalKernel_resonant
    (rho : XiDivisorSupport) (epsilon : ℝ) :
    xiCompletedApertureOffDiagonalKernel
        ((rho : ℂ).re - 1 / 2 + epsilon) (rho : ℂ).im 0 =
      seamFluxCochain ((rho : ℂ) + (epsilon : ℂ)) := by
  rw [xiCompletedApertureOffDiagonalKernel]
  congr 1
  apply Complex.ext
  · norm_num
    ring
  · norm_num

theorem xiCompletedApertureOffDiagonalKernel_resonant_diagonal
    (rho : XiDivisorSupport) (epsilon : ℝ) :
    xiCompletedApertureOffDiagonalKernel
        ((rho : ℂ).re - 1 / 2 + epsilon) 0 0 =
      seamFluxCochain ((((rho : ℂ).re + epsilon : ℝ) : ℂ)) := by
  rw [xiCompletedApertureOffDiagonalKernel]
  congr 1
  apply Complex.ext
  · norm_num
    ring
  · norm_num

theorem epsilon_mul_xiCompletedApertureOddRealKernel_resonant
    (rho : XiDivisorSupport) {epsilon : ℝ} (hepsilon : epsilon ≠ 0) :
    epsilon * xiCompletedApertureOddRealKernel
        ((rho : ℂ).re - 1 / 2 + epsilon) (rho : ℂ).im 0 =
      2 * (completedFluxGermAt (rho : ℂ) (epsilon : ℂ)).re := by
  rw [xiCompletedApertureOddRealKernel,
    xiCompletedApertureOffDiagonalKernel_resonant,
    completedFluxGermAt, if_neg (ofReal_ne_zero.mpr hepsilon)]
  simp only [ofReal_re, ofReal_im, zero_mul, sub_zero, mul_re]
  ring

theorem epsilon_mul_xiCompletedApertureOddRealKernel_resonant_diagonal
    (rho : XiDivisorSupport) (epsilon : ℝ) :
    epsilon * xiCompletedApertureOddRealKernel
        ((rho : ℂ).re - 1 / 2 + epsilon) 0 0 =
      2 * epsilon *
        (seamFluxCochain ((((rho : ℂ).re + epsilon : ℝ) : ℂ))).re := by
  rw [xiCompletedApertureOddRealKernel,
    xiCompletedApertureOffDiagonalKernel_resonant_diagonal]
  ring

/-- Away from the collision, the residue-filled expression is exactly `epsilon^2` times the
unregularized two-node determinant. -/
theorem xiCompletedApertureRegularizedResonantTwoPointDet_eq_scaled
    (rho : XiDivisorSupport) {epsilon : ℝ} (hepsilon : epsilon ≠ 0) :
    xiCompletedApertureRegularizedResonantTwoPointDet rho epsilon =
      epsilon ^ 2 * xiCompletedApertureResonantTwoPointDet rho epsilon := by
  have hdiag :=
    epsilon_mul_xiCompletedApertureOddRealKernel_resonant_diagonal rho epsilon
  have hoff :=
    epsilon_mul_xiCompletedApertureOddRealKernel_resonant rho hepsilon
  rw [xiCompletedApertureRegularizedResonantTwoPointDet,
    xiCompletedApertureResonantTwoPointDet]
  rw [← hdiag, ← hoff]
  ring

/-- The residue-filled determinant is continuous through the resonant collision. -/
theorem continuousAt_xiCompletedApertureRegularizedResonantTwoPointDet
    (rho : XiDivisorSupport) :
    ContinuousAt (xiCompletedApertureRegularizedResonantTwoPointDet rho) 0 := by
  have hxi : xi ((((rho : ℂ).re : ℝ) : ℂ)) ≠ 0 := by
    apply xi_ne_zero_of_abs_im_le_nine_halves
    norm_num
  have hlog : AnalyticAt ℂ (logDeriv xi) ((((rho : ℂ).re : ℝ) : ℂ)) := by
    change AnalyticAt ℂ (fun z => deriv xi z / xi z) _
    exact (xi_analyticOnNhd_univ _ (Set.mem_univ _)).deriv.div
      (xi_analyticOnNhd_univ _ (Set.mem_univ _)) hxi
  have hflux : AnalyticAt ℂ seamFluxCochain ((((rho : ℂ).re : ℝ) : ℂ)) := by
    change AnalyticAt ℂ (fun z => -logDeriv xi z) _
    exact hlog.neg
  have hdiagComplex : ContinuousAt
      (fun epsilon : ℝ =>
        seamFluxCochain ((((rho : ℂ).re + epsilon : ℝ) : ℂ))) 0 := by
    have hshift : ContinuousAt
        (fun epsilon : ℝ => ((((rho : ℂ).re + epsilon : ℝ) : ℂ))) 0 := by
      fun_prop
    simpa only [Function.comp_def, add_zero] using
      hflux.continuousAt.comp_of_eq hshift (by simp)
  have hdiag : ContinuousAt
      (fun epsilon : ℝ =>
        (seamFluxCochain ((((rho : ℂ).re + epsilon : ℝ) : ℂ))).re) 0 :=
    Complex.continuous_re.continuousAt.comp hdiagComplex
  have hgermComplex : ContinuousAt
      (fun epsilon : ℝ => completedFluxGermAt (rho : ℂ) (epsilon : ℂ)) 0 := by
    have hcast : ContinuousAt (fun epsilon : ℝ => (epsilon : ℂ)) 0 := by
      fun_prop
    simpa only [Function.comp_def] using
      (completedFluxGermAt_analyticAt_zero (rho : ℂ)).continuousAt.comp_of_eq
        hcast (by simp)
  have hgerm : ContinuousAt
      (fun epsilon : ℝ => (completedFluxGermAt (rho : ℂ) (epsilon : ℂ)).re) 0 :=
    Complex.continuous_re.continuousAt.comp hgermComplex
  unfold xiCompletedApertureRegularizedResonantTwoPointDet
  fun_prop

/-- **Multiplicity tomography.** The filled collision value is the negative square of twice the
Xi divisor multiplicity. -/
theorem xiCompletedApertureRegularizedResonantTwoPointDet_zero
    (rho : XiDivisorSupport) :
    xiCompletedApertureRegularizedResonantTwoPointDet rho 0 =
      -4 * (xiSupportMultiplicity rho : ℝ) ^ 2 := by
  simp only [xiCompletedApertureRegularizedResonantTwoPointDet,
    ofReal_zero, completedFluxGermAt_zero]
  rw [← xiSupportMultiplicity_eq_analyticOrderAt_toNat]
  norm_num
  ring

/-- Exact scaled collision limit. -/
theorem tendsto_xiCompletedApertureRegularizedResonantTwoPointDet
    (rho : XiDivisorSupport) :
    Tendsto (xiCompletedApertureRegularizedResonantTwoPointDet rho) (nhds 0)
      (nhds (-4 * (xiSupportMultiplicity rho : ℝ) ^ 2)) := by
  simpa [xiCompletedApertureRegularizedResonantTwoPointDet_zero] using
    (continuousAt_xiCompletedApertureRegularizedResonantTwoPointDet rho).tendsto

/-- Every Xi divisor point forces a punctured positive aperture interval on which the raw
reflection-odd two-node determinant is strictly negative. -/
theorem exists_pos_xiCompletedApertureResonantTwoPointDet_neg
    (rho : XiDivisorSupport) :
    ∃ eta > 0, ∀ epsilon, 0 < epsilon → epsilon < eta →
      xiCompletedApertureResonantTwoPointDet rho epsilon < 0 := by
  have hm : 0 < (xiSupportMultiplicity rho : ℝ) := by
    exact_mod_cast xiSupportMultiplicity_pos rho
  have hvalue :
      xiCompletedApertureRegularizedResonantTwoPointDet rho 0 < 0 := by
    rw [xiCompletedApertureRegularizedResonantTwoPointDet_zero]
    nlinarith
  have hevent : {epsilon : ℝ |
      xiCompletedApertureRegularizedResonantTwoPointDet rho epsilon < 0} ∈ nhds 0 :=
    (continuousAt_xiCompletedApertureRegularizedResonantTwoPointDet rho).tendsto
      (Iio_mem_nhds hvalue)
  obtain ⟨eta, heta, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨eta, heta, ?_⟩
  intro epsilon hepsilon hepsilonEta
  have hepsilonBall : epsilon ∈ Metric.ball (0 : ℝ) eta := by
    rw [Real.ball_zero_eq_Ioo]
    exact ⟨by linarith, hepsilonEta⟩
  have hregNeg := hball hepsilonBall
  change xiCompletedApertureRegularizedResonantTwoPointDet rho epsilon < 0 at hregNeg
  rw [xiCompletedApertureRegularizedResonantTwoPointDet_eq_scaled rho
    (ne_of_gt hepsilon)] at hregNeg
  have hepsilonSq : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
  nlinarith

end

end RHTower
