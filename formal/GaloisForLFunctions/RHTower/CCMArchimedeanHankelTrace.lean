import GaloisForLFunctions.RHTower.CCMArchimedeanHankelTraceClass
import GaloisForLFunctions.HTGeometry.SeparableBuresIncidenceLaw
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Exact trace of the CCM positive Hankel block

The trace-class factorization of `ccmPositiveHankel g` has two vector fields on the positive
half-line.  Their diagonal overlap is not postulated as a kernel-diagonal rule: it is computed
inside the actual Bochner `L²` factorization.  The anchored Volterra integral and the fundamental
theorem of calculus give

`⟨B(t), A_g(t)⟩ = g(t) - g(2t)`.

Integrating this identity and applying the exact half-line dilation formula proves

`Tr(H_g⁺) = (1/2) ∫₀∞ g(t) dt`.

Thus this file supplies the first literal operator-trace evaluation needed for the
Connes--Consani archimedean trace formula; no abstract "trace equals diagonal integral" premise is
introduced.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Real SchwartzMap Topology symmDiff

namespace RHTower

-- These instances expose separability of the concrete real-line `L²` space used by `opTrace`.
local instance factOneLeTwoArchimedeanHankelTrace :
    Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
local instance factTwoNeTopArchimedeanHankelTrace :
    Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩

/-- Exact diagonal overlap of the two Hilbert--Schmidt fields in the positive Hankel
factorization.  The subtraction is the finite Volterra boundary term, not a regularized
diagonal. -/
theorem inner_ccmVolterraObserverVec_hankelDerivativeSlice
    (g : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 ≤ t) :
    inner ℂ (ccmVolterraObserverVec t) (ccmHankelDerivativeSlice g t) =
      g t - g (2 * t) := by
  rw [inner_ccmVolterraObserverVec _ ht]
  have hrep := ccmHankelDerivativeSlice_coeFn g t
  have hinterval :
      (∫ y in Icc 0 t, ccmHankelDerivativeSlice g t y) =
        ∫ y in Icc 0 t, (-(1 + t ^ 2) : ℂ) * deriv g (y + t) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hrep, ae_restrict_mem measurableSet_Icc]
      with y hy hmem
    rw [hy, if_pos hmem.1]
  rw [hinterval, integral_const_mul]
  have hscale : ((1 + t ^ 2) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (1 + t ^ 2 : ℝ) ≠ 0)
  have hderiv : deriv (fun y : ℝ => g (y + t)) = fun y => deriv g (y + t) := by
    funext y
    exact (HasDerivAt.comp_add_const y t
      (((g.smooth ⊤).differentiable (by simp)).differentiableAt.hasDerivAt)).deriv
  have hfund : (∫ y in (0 : ℝ)..t, deriv g (y + t)) = g (2 * t) - g t := by
    have hdiff : ∀ y ∈ uIcc (0 : ℝ) t,
        DifferentiableAt ℝ (fun z : ℝ => g (z + t)) y := by
      intro y _
      exact (HasDerivAt.comp_add_const y t
        (((g.smooth ⊤).differentiable (by simp)).differentiableAt.hasDerivAt)).differentiableAt
    have hcont : ContinuousOn (fun y : ℝ => deriv g (y + t)) (uIcc (0 : ℝ) t) := by
      exact ((SchwartzMap.derivCLM ℂ ℂ g).continuous.comp
        (continuous_id.add continuous_const)).continuousOn
    have h := intervalIntegral.integral_deriv_eq_sub' (fun y : ℝ => g (y + t))
      hderiv hdiff hcont
    simpa [two_mul] using h
  have hfundset : (∫ y in Icc 0 t, deriv g (y + t)) = g (2 * t) - g t := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht, hfund]
  rw [hfundset]
  field_simp
  ring

/-- **Exact positive Hankel trace formula.**  The actual operator trace of the trace-class
positive-quadrant Hankel block is half the positive-half-line integral of its Schwartz kernel.
This is the rigorous diagonal evaluation underlying the corresponding CCM block trace. -/
theorem opTrace_ccmPositiveHankel_eq_half_integral (g : 𝓢(ℝ, ℂ)) :
    ContinuousLinearMap.opTrace (ccmPositiveHankel g) =
      (1 / 2 : ℂ) * ∫ t in Ici (0 : ℝ), g t := by
  rw [ccmPositiveHankel, ccmHankelDerivativeSynthesis, ccmVolterraObserver,
    opTrace_l2Synthesis_comp_observer_eq_inner ccmPositiveMeasure
      ccmVolterraObserverField (ccmHankelDerivativeField g),
    MeasureTheory.L2.inner_def]
  have hobserver : (ccmVolterraObserverField : ℝ → SoninL2) =ᵐ[ccmPositiveMeasure]
      ccmVolterraObserverVec := by
    simpa [ccmVolterraObserverField] using ccmVolterraObserverVec_memLp.coeFn_toLp
  have hderivative : (ccmHankelDerivativeField g : ℝ → SoninL2) =ᵐ[ccmPositiveMeasure]
      ccmHankelDerivativeSlice g := by
    simpa [ccmHankelDerivativeField] using
      (ccmHankelDerivativeSlice_memLp g).coeFn_toLp
  calc
    (∫ t, inner ℂ (ccmVolterraObserverField t) (ccmHankelDerivativeField g t)
        ∂ccmPositiveMeasure) =
        ∫ t, g t - g (2 * t) ∂ccmPositiveMeasure := by
      apply integral_congr_ae
      filter_upwards [hobserver, hderivative, ae_restrict_mem measurableSet_Ici]
        with t htObs htDer ht
      rw [htObs, htDer,
        inner_ccmVolterraObserverVec_hankelDerivativeSlice g ht]
    _ = ∫ t in Ici (0 : ℝ), g t - g (2 * t) := by
      rw [ccmPositiveMeasure]
    _ = (∫ t in Ici (0 : ℝ), g t) - ∫ t in Ici (0 : ℝ), g (2 * t) := by
      rw [integral_sub g.integrable.integrableOn
        (g.integrable.comp_mul_left' (by norm_num : (2 : ℝ) ≠ 0)).integrableOn]
    _ = (∫ t in Ici (0 : ℝ), g t) -
        (2 : ℝ)⁻¹ • ∫ t in Ici (0 : ℝ), g t := by
      congr 1
      rw [integral_Ici_eq_integral_Ioi, integral_Ici_eq_integral_Ioi,
        integral_comp_mul_left_Ioi (fun t : ℝ => g t) 0 (by norm_num : (0 : ℝ) < 2),
        mul_zero]
    _ = (1 / 2 : ℂ) * ∫ t in Ici (0 : ℝ), g t := by
      norm_num [smul_eq_mul]
      ring

end RHTower
