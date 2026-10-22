import GaloisForLFunctions.RHTower.PolynomialGaussianLocalConcentration
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanPhaseTraceFormula
import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic
import GaloisForLFunctions.HTGeometry.HermiteOrthogonality

/-!
# Route-U polynomial--Gaussian Gamma radial envelope

This file closes C43-Y (24.136) in its exact all-radius form.  The native Route-U density is
first realized as a scaled Schwartz function.  Consequently its mass and its product with the
exact Gamma phase rate are genuinely integrable, rather than assigned values by a nonintegrable
integral convention.

Evenness and radial monotonicity of `gammaHardyPhaseRate` then give, for every nonnegative radius
`R`,

`integral f*g >= (g(R) - 18 R (g(R)-g(0)) sqrt(t(deg Q+1))) integral f`.

The estimate is unconditional, coefficient-uniform, valid for the zero polynomial and contains no
chosen cutoff or hidden positivity premise.
-/

open scoped Real SchwartzMap
open Complex Real MeasureTheory Set

noncomputable section

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

private def routeUEnergySchwartz (P : Polynomial ℝ) : SchwartzMap ℝ ℂ :=
  GaloisForLFunctions.mulS (polyGaussSchwartz P) (polyGaussSchwartz P)

private theorem routeUEnergySchwartz_apply (P : Polynomial ℝ) (x : ℝ) :
    routeUEnergySchwartz P x = polynomialGaussianEnergy P x := by
  rw [routeUEnergySchwartz, GaloisForLFunctions.mulS_apply,
    polyGaussSchwartz_apply, polynomialGaussianEnergy]
  push_cast
  rw [gaussReal]
  push_cast
  ring_nf
  have hexp : Complex.exp (-((Real.pi : ℂ) * (x : ℂ) ^ 2)) ^ 2 =
      Complex.exp (-((Real.pi : ℂ) * (x : ℂ) ^ 2 * 2)) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  rw [hexp]

private def routeUDensitySchwartz
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) : SchwartzMap ℝ ℂ :=
  let δ := Real.sqrt (2 * Real.pi / (t : ℝ))
  let u : ℝˣ := Units.mk0 δ⁻¹ (inv_ne_zero (Real.sqrt_pos.2
    (div_pos (by positivity) t.property)).ne')
  let A : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft u
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A)
    (routeUEnergySchwartz (routeURescaledEvenPolynomial Q t))

private theorem routeUDensitySchwartz_apply
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) (x : ℝ) :
    routeUDensitySchwartz Q t x = routeUPolynomialGaussianDensity Q t x := by
  rw [routeUDensitySchwartz, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  change routeUEnergySchwartz (routeURescaledEvenPolynomial Q t)
      ((Real.sqrt (2 * Real.pi / (t : ℝ)))⁻¹ * x) = _
  rw [routeUEnergySchwartz_apply, routeUPolynomialGaussianDensity_eq_dilate]
  congr 1
  simp only [div_eq_mul_inv]
  ring

/-- The native Route-U density has finite total mass. -/
theorem integrable_norm_routeUPolynomialGaussianDensity
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    Integrable (fun x : ℝ => ‖routeUPolynomialGaussianDensity Q t x‖) := by
  exact (routeUDensitySchwartz Q t).integrable.norm.congr
    (Filter.Eventually.of_forall fun x => by simp only [routeUDensitySchwartz_apply])

private theorem gammaHardyPhaseRate_zero_le (x : ℝ) :
    gammaHardyPhaseRate 0 ≤ gammaHardyPhaseRate x := by
  have hmono := strictMonoOn_gammaHardyPhaseRate.monotoneOn
  by_cases hx : 0 ≤ x
  · exact hmono (by simp) hx hx
  · rw [← gammaHardyPhaseRate_neg x]
    have hnx : 0 ≤ -x := neg_nonneg.mpr (le_of_not_ge hx)
    exact hmono (by simp) hnx hnx

private theorem gammaHardyPhaseRate_radius_le_of_not_mem_Icc
    (R : {R : ℝ // 0 ≤ R}) {x : ℝ} (hx : x ∉ Set.Icc (-(R : ℝ)) (R : ℝ)) :
    gammaHardyPhaseRate R ≤ gammaHardyPhaseRate x := by
  have hRabs : (R : ℝ) ≤ |x| := by
    rw [Set.mem_Icc, not_and_or] at hx
    rcases hx with hx | hx
    · have hlt : x < -(R : ℝ) := lt_of_not_ge hx
      rw [abs_of_neg (lt_of_lt_of_le hlt (neg_nonpos.mpr R.property))]
      exact le_of_lt (by linarith only [hlt])
    · have hlt : (R : ℝ) < x := lt_of_not_ge hx
      rw [abs_of_nonneg (le_trans R.property hlt.le)]
      exact hlt.le
  have hmono := strictMonoOn_gammaHardyPhaseRate.monotoneOn
  have h := hmono R.property (abs_nonneg x) hRabs
  by_cases hx0 : 0 ≤ x
  · simpa [abs_of_nonneg hx0] using h
  · rw [abs_of_neg (lt_of_not_ge hx0), gammaHardyPhaseRate_neg] at h
    exact h

private theorem integrable_gammaHardyPhaseRate_mul_norm_routeUPolynomialGaussianDensity
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    Integrable (fun x : ℝ =>
      gammaHardyPhaseRate x * ‖routeUPolynomialGaussianDensity Q t x‖) := by
  have hc : Integrable
      (ccmGammaHardyPhaseRateMul (routeUDensitySchwartz Q t) : ℝ → ℂ)
      (volume : Measure ℝ) :=
    (ccmGammaHardyPhaseRateMul (routeUDensitySchwartz Q t)).integrable
  have hre := hc.re
  refine hre.congr (Filter.Eventually.of_forall fun x => ?_)
  change (ccmGammaHardyPhaseRateMul (routeUDensitySchwartz Q t) x).re = _
  rw [ccmGammaHardyPhaseRateMul_apply, routeUDensitySchwartz_apply]
  unfold routeUPolynomialGaussianDensity evenSquarePolynomial
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]

private theorem routeUGammaPenalty_le
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t})
    (R : {R : ℝ // 0 ≤ R}) :
    (gammaHardyPhaseRate R - gammaHardyPhaseRate 0) *
        (∫ x in Set.Icc (-(R : ℝ)) (R : ℝ),
          ‖routeUPolynomialGaussianDensity Q t x‖) ≤
      (gammaHardyPhaseRate R - gammaHardyPhaseRate 0) *
        (18 * (R : ℝ) * Real.sqrt ((t : ℝ) * (Q.natDegree + 1)) *
          routeUPolynomialGaussianMass Q t) := by
  apply mul_le_mul_of_nonneg_left
  · exact integral_Icc_norm_routeUPolynomialGaussianDensity_le Q t R
  · linarith [gammaHardyPhaseRate_zero_le (R : ℝ)]

/-- **Exact Route-U Gamma radial aperture envelope (GRAE.1 / C43-Y (24.136)).**

Heat positivity and radius nonnegativity are encoded in the input types.  There are no analytic,
sign, nonzero-polynomial or cutoff premises. -/
theorem integral_norm_routeUPolynomialGaussianDensity_mul_gammaHardyPhaseRate_ge
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t})
    (R : {R : ℝ // 0 ≤ R}) :
    (gammaHardyPhaseRate R -
          18 * (R : ℝ) * (gammaHardyPhaseRate R - gammaHardyPhaseRate 0) *
            Real.sqrt ((t : ℝ) * (Q.natDegree + 1))) *
        routeUPolynomialGaussianMass Q t ≤
      ∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q t x‖ * gammaHardyPhaseRate x := by
  let S : Set ℝ := Set.Icc (-(R : ℝ)) (R : ℝ)
  let f : ℝ → ℝ := fun x => ‖routeUPolynomialGaussianDensity Q t x‖
  let g : ℝ → ℝ := gammaHardyPhaseRate
  have hf : Integrable f := by
    simpa only [f] using integrable_norm_routeUPolynomialGaussianDensity Q t
  have hgf : Integrable (fun x => g x * f x) := by
    simpa only [g, f] using
      integrable_gammaHardyPhaseRate_mul_norm_routeUPolynomialGaussianDensity Q t
  have hlocal :
      (∫ x in S, gammaHardyPhaseRate 0 * f x) ≤
        ∫ x in S, g x * f x := by
    apply setIntegral_mono_on
        (hf.const_mul (gammaHardyPhaseRate 0)).integrableOn hgf.integrableOn
        (by simpa only [S] using measurableSet_Icc)
    intro x _
    exact mul_le_mul_of_nonneg_right (gammaHardyPhaseRate_zero_le x) (norm_nonneg _)
  have houtside :
      (∫ x in Sᶜ, gammaHardyPhaseRate R * f x) ≤
        ∫ x in Sᶜ, g x * f x := by
    apply setIntegral_mono_on
        (hf.const_mul (gammaHardyPhaseRate R)).integrableOn hgf.integrableOn
        (by
          have hS : MeasurableSet S := by simpa only [S] using measurableSet_Icc
          exact hS.compl)
    intro x hx
    exact mul_le_mul_of_nonneg_right
      (gammaHardyPhaseRate_radius_le_of_not_mem_Icc R hx)
      (norm_nonneg _)
  have hsplitf :
      (∫ x in S, f x) + (∫ x in Sᶜ, f x) = ∫ x, f x :=
    integral_add_compl (by simpa only [S] using measurableSet_Icc) hf
  have hsplitgf :
      (∫ x in S, g x * f x) + (∫ x in Sᶜ, g x * f x) =
        ∫ x, g x * f x :=
    integral_add_compl (by simpa only [S] using measurableSet_Icc) hgf
  have hradial :
      gammaHardyPhaseRate 0 * (∫ x in S, f x) +
          gammaHardyPhaseRate R * (∫ x in Sᶜ, f x) ≤
        ∫ x, g x * f x := by
    calc
      gammaHardyPhaseRate 0 * (∫ x in S, f x) +
            gammaHardyPhaseRate R * (∫ x in Sᶜ, f x) =
          (∫ x in S, gammaHardyPhaseRate 0 * f x) +
            ∫ x in Sᶜ, gammaHardyPhaseRate R * f x := by
              rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      _ ≤ (∫ x in S, g x * f x) + ∫ x in Sᶜ, g x * f x :=
        add_le_add hlocal houtside
      _ = ∫ x, g x * f x := hsplitgf
  have hbase :
      gammaHardyPhaseRate R * routeUPolynomialGaussianMass Q t -
          (gammaHardyPhaseRate R - gammaHardyPhaseRate 0) * (∫ x in S, f x) ≤
        ∫ x, g x * f x := by
    rw [routeUPolynomialGaussianMass]
    change gammaHardyPhaseRate R * (∫ x, f x) -
          (gammaHardyPhaseRate R - gammaHardyPhaseRate 0) * (∫ x in S, f x) ≤ _
    rw [← hsplitf]
    calc
      gammaHardyPhaseRate R *
            ((∫ x in S, f x) + ∫ x in Sᶜ, f x) -
          (gammaHardyPhaseRate R - gammaHardyPhaseRate 0) * (∫ x in S, f x) =
        gammaHardyPhaseRate 0 * (∫ x in S, f x) +
          gammaHardyPhaseRate R * (∫ x in Sᶜ, f x) := by ring
      _ ≤ ∫ x, g x * f x := hradial
  have hpenalty := routeUGammaPenalty_le Q t R
  calc
    (gammaHardyPhaseRate R -
          18 * (R : ℝ) * (gammaHardyPhaseRate R - gammaHardyPhaseRate 0) *
            Real.sqrt ((t : ℝ) * (Q.natDegree + 1))) *
        routeUPolynomialGaussianMass Q t =
      gammaHardyPhaseRate R * routeUPolynomialGaussianMass Q t -
        (gammaHardyPhaseRate R - gammaHardyPhaseRate 0) *
          (18 * (R : ℝ) * Real.sqrt ((t : ℝ) * (Q.natDegree + 1)) *
            routeUPolynomialGaussianMass Q t) := by ring
    _ ≤ gammaHardyPhaseRate R * routeUPolynomialGaussianMass Q t -
        (gammaHardyPhaseRate R - gammaHardyPhaseRate 0) * (∫ x in S, f x) := by
      exact sub_le_sub_left (by simpa only [S, f] using hpenalty) _
    _ ≤ ∫ x, g x * f x := hbase
    _ = ∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q t x‖ *
        gammaHardyPhaseRate x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by simp only [g, f]; ring

end RHTower
