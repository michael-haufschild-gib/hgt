import GaloisForLFunctions.RHTower.ConnesLogMomentPV
import GaloisForLFunctions.RHTower.ConnesGaussianPV
import GaloisForLFunctions.RHTower.ConnesLocalTraceCore

/-!
# The last identification of §V

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068, §V.

The Fourier transform of `−log|u|` is Connes' logarithmically regularized principal value
`d^*x = dx/(2|x|)` plus `(γ + log 2π)` times the Dirac mass at the origin:

  `lim_{ε→0⁺} [ ∫_{|x| ≥ ε} g(x) d^*x + g(0) log ε ]
      = −∫_ℝ 𝓕g(u) log|u| du − (γ + log 2π) g(0)`   for every Schwartz `g`.

Away from the origin this is `connes_logPV_tendsto_of_zero`; the `δ`-coefficient is read off from
the self-dual Gaussian, where the two sides are `½log π + γ/2 + log 2` (App. II (32)) and
`−γ/2 − (log π)/2` (`connes_gaussian_logPV_tendsto`).
-/

open MeasureTheory Set Filter Topology FourierTransform Real
open scoped FourierTransform SchwartzMap

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The Fourier log moment of a Schwartz function. -/
def connesFourierLogMoment (h : 𝓢(ℝ, ℂ)) : ℂ :=
  ∫ u : ℝ, ((SchwartzMap.fourierTransformCLM ℂ h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ)

theorem connesFourierLogMoment_eq (h : 𝓢(ℝ, ℂ)) :
    connesFourierLogMoment h
      = ∫ u : ℝ, 𝓕 ((h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ) := by
  rw [connesFourierLogMoment, connes_fourierCLM_coe]

theorem connes_schwartz_integrable_logu (G : 𝓢(ℝ, ℂ)) :
    Integrable (fun u : ℝ => (G : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ)) volume := by
  have h := connes_schwartz_integrable_log G
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  show (G : ℝ → ℂ) u * ((Real.log |u| : ℝ) : ℂ)
      = (G : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ)
  rw [Real.log_abs]

theorem connesFourierLogMoment_sub (h₁ h₂ : 𝓢(ℝ, ℂ)) :
    connesFourierLogMoment (h₁ - h₂)
      = connesFourierLogMoment h₁ - connesFourierLogMoment h₂ := by
  rw [connesFourierLogMoment, connesFourierLogMoment, connesFourierLogMoment, map_sub,
    ← MeasureTheory.integral_sub
      (connes_schwartz_integrable_logu (SchwartzMap.fourierTransformCLM ℂ h₁))
      (connes_schwartz_integrable_logu (SchwartzMap.fourierTransformCLM ℂ h₂))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show (((SchwartzMap.fourierTransformCLM ℂ h₁ - SchwartzMap.fourierTransformCLM ℂ h₂ :
        𝓢(ℝ, ℂ)) : ℝ → ℂ) u) * ((Real.log u : ℝ) : ℂ) = _
  rw [SchwartzMap.sub_apply]
  ring

theorem connesFourierLogMoment_smul (c : ℂ) (h : 𝓢(ℝ, ℂ)) :
    connesFourierLogMoment (c • h) = c * connesFourierLogMoment h := by
  rw [connesFourierLogMoment, connesFourierLogMoment, map_smul,
    ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show (((c • SchwartzMap.fourierTransformCLM ℂ h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u)
      * ((Real.log u : ℝ) : ℂ) = _
  rw [SchwartzMap.smul_apply, smul_eq_mul]
  ring

/-- The multiplicative-Haar integrand of a Schwartz function is integrable on every tail. -/
theorem connes_tail_haar_integrable (h : 𝓢(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ => (h : ℝ → ℂ) x * ((connesRealMultHaarDensity x : ℝ) : ℂ))
      {x : ℝ | ε ≤ |x|} volume := by
  have hSm : MeasurableSet {x : ℝ | ε ≤ |x|} := measurableSet_le measurable_const measurable_norm
  have hmaj : IntegrableOn (fun x : ℝ => (2 * ε)⁻¹ * ‖(h : ℝ → ℂ) x‖)
      {x : ℝ | ε ≤ |x|} volume :=
    ((h.integrable (μ := volume)).norm.const_mul (2 * ε)⁻¹).integrableOn
  refine Integrable.mono' hmaj ?_ ?_
  · exact (h.continuous.aestronglyMeasurable.mul
      ((Complex.measurable_ofReal.comp measurable_connesRealMultHaarDensity)).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem hSm] with x hx
    have hx' : ε ≤ |x| := hx
    have hxpos : (0:ℝ) < |x| := lt_of_lt_of_le hε hx'
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, connesRealMultHaarDensity,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (2 * |x|)⁻¹)]
    have hle : (2 * |x|)⁻¹ ≤ (2 * ε)⁻¹ := by
      have h2e : (0:ℝ) < 2 * ε := by linarith
      have h2x : (2:ℝ) * ε ≤ 2 * |x| := by linarith
      have hone := one_div_le_one_div_of_le h2e h2x
      rwa [one_div, one_div] at hone
    calc ‖(h : ℝ → ℂ) x‖ * (2 * |x|)⁻¹ ≤ ‖(h : ℝ → ℂ) x‖ * (2 * ε)⁻¹ :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = (2 * ε)⁻¹ * ‖(h : ℝ → ℂ) x‖ := by ring

theorem connes_logPV_sub {ε : ℝ} (hε : 0 < ε) (h₁ h₂ : 𝓢(ℝ, ℂ)) :
    connesRealLogPV ((h₁ - h₂ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ε
      = connesRealLogPV ((h₁ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ε
        - connesRealLogPV ((h₂ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ε := by
  have hSm : MeasurableSet {x : ℝ | ε ≤ |x|} := measurableSet_le measurable_const measurable_norm
  have hsplit : (∫ x in {x : ℝ | ε ≤ |x|},
        ((h₁ - h₂ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x * ((connesRealMultHaarDensity x : ℝ) : ℂ))
      = (∫ x in {x : ℝ | ε ≤ |x|},
          (h₁ : ℝ → ℂ) x * ((connesRealMultHaarDensity x : ℝ) : ℂ))
        - ∫ x in {x : ℝ | ε ≤ |x|},
          (h₂ : ℝ → ℂ) x * ((connesRealMultHaarDensity x : ℝ) : ℂ) := by
    rw [← MeasureTheory.integral_sub (connes_tail_haar_integrable h₁ hε)
      (connes_tail_haar_integrable h₂ hε)]
    refine setIntegral_congr_fun hSm fun x _ => ?_
    rw [SchwartzMap.sub_apply]
    ring
  have hzero : ((h₁ - h₂ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) 0 = (h₁ : ℝ → ℂ) 0 - (h₂ : ℝ → ℂ) 0 :=
    SchwartzMap.sub_apply h₁ h₂ 0
  rw [connesRealLogPV, connesRealLogPV, connesRealLogPV, hsplit, hzero]
  ring

theorem connes_logPV_smul {ε : ℝ} (hε : 0 < ε) (c : ℂ) (h : 𝓢(ℝ, ℂ)) :
    connesRealLogPV ((c • h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ε
      = c * connesRealLogPV ((h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ε := by
  have hSm : MeasurableSet {x : ℝ | ε ≤ |x|} := measurableSet_le measurable_const measurable_norm
  have hsplit : (∫ x in {x : ℝ | ε ≤ |x|},
        ((c • h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x * ((connesRealMultHaarDensity x : ℝ) : ℂ))
      = c * ∫ x in {x : ℝ | ε ≤ |x|},
          (h : ℝ → ℂ) x * ((connesRealMultHaarDensity x : ℝ) : ℂ) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun hSm fun x _ => ?_
    rw [SchwartzMap.smul_apply, smul_eq_mul]
    ring
  have hzero : ((c • h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) 0 = c * (h : ℝ → ℂ) 0 := by
    rw [SchwartzMap.smul_apply, smul_eq_mul]
  rw [connesRealLogPV, connesRealLogPV, hsplit, hzero]
  ring

/-- The Fourier log moment of the self-dual Gaussian (App. II (32)). -/
theorem connes_gauss_fourierLogMoment :
    connesFourierLogMoment GaloisForLFunctions.gaussianSchwartz
      = ((-((1:ℝ)/2 * Real.log π + Real.eulerMascheroniConstant / 2 + Real.log 2) : ℝ) : ℂ) := by
  rw [connesFourierLogMoment_eq]
  have hF : 𝓕 ((GaloisForLFunctions.gaussianSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = ((GaloisForLFunctions.gaussianSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    have h := GaloisForLFunctions.fourier_gaussianSchwartz
    have h2 := congrArg (fun f : 𝓢(ℝ, ℂ) => (f : ℝ → ℂ)) h
    simpa [SchwartzMap.fourier_coe] using h2
  rw [hF]
  have hreal : (∫ u : ℝ, GaloisForLFunctions.gaussReal u * Real.log u)
      = -((1:ℝ)/2 * Real.log π + Real.eulerMascheroniConstant / 2 + Real.log 2) := by
    have hA := connes_integral_neg_log_abs_mul_gaussian
    have hcongr : (∫ u : ℝ, (-Real.log |u|) * Real.exp (-π * u ^ (2 : ℕ)))
        = - ∫ u : ℝ, GaloisForLFunctions.gaussReal u * Real.log u := by
      rw [← MeasureTheory.integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      have hexp : Real.exp (-π * u ^ (2 : ℕ)) = Real.exp (-(π * u ^ (2 : ℕ))) := by ring_nf
      show (-Real.log |u|) * Real.exp (-π * u ^ (2 : ℕ))
          = -(GaloisForLFunctions.gaussReal u * Real.log u)
      unfold GaloisForLFunctions.gaussReal
      rw [Real.log_abs, hexp]
      ring
    rw [hcongr] at hA
    linarith [hA]
  rw [← hreal, ← _root_.integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show (GaloisForLFunctions.gaussianSchwartz : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ)
      = ((GaloisForLFunctions.gaussReal u * Real.log u : ℝ) : ℂ)
  rw [GaloisForLFunctions.gaussianSchwartz_apply, ← Complex.ofReal_mul]

/-- **The last identification of §V.**  The Fourier transform of `−log|u|` is Connes'
logarithmically regularized principal value for `d^*x = dx/(2|x|)`, plus `(γ + log 2π) δ₀`. -/
theorem connes_arch_logPV_identification (g : 𝓢(ℝ, ℂ)) :
    Tendsto (fun ε : ℝ => connesRealLogPV ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ε) (𝓝[>] 0)
      (𝓝 (- connesFourierLogMoment g
          - (g : ℝ → ℂ) 0
            * ((Real.eulerMascheroniConstant + Real.log (2 * π) : ℝ) : ℂ))) := by
  set c : ℂ := (g : ℝ → ℂ) 0 with hc
  set φ : 𝓢(ℝ, ℂ) := g - c • GaloisForLFunctions.gaussianSchwartz with hφdef
  have hφ0 : (φ : ℝ → ℂ) 0 = 0 := by
    rw [hφdef, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul,
      connes_gauss_zero, mul_one, ← hc, sub_self]
  have h1 := connes_logPV_tendsto_of_zero φ hφ0
  have h2 := connes_gaussian_logPV_tendsto
  have hsum := h1.add (h2.const_mul c)
  have hεexpr : ∀ ε : ℝ, 0 < ε →
      connesRealLogPV ((φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ε
        + c * connesRealLogPV
            ((GaloisForLFunctions.gaussianSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ε
        = connesRealLogPV ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ε := by
    intro ε hε
    rw [hφdef, connes_logPV_sub hε, connes_logPV_smul hε]
    ring
  have hfinal : Tendsto (fun ε : ℝ => connesRealLogPV ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ε) (𝓝[>] 0)
      (𝓝 ((- ∫ u : ℝ, 𝓕 ((φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ))
          + c * (((-Real.eulerMascheroniConstant / 2 - Real.log π / 2 : ℝ)) : ℂ))) := by
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hεexpr ε hε
  have hvalue : (- ∫ u : ℝ, 𝓕 ((φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ))
        + c * (((-Real.eulerMascheroniConstant / 2 - Real.log π / 2 : ℝ)) : ℂ)
      = - connesFourierLogMoment g
        - c * ((Real.eulerMascheroniConstant + Real.log (2 * π) : ℝ) : ℂ) := by
    rw [← connesFourierLogMoment_eq φ, hφdef, connesFourierLogMoment_sub,
      connesFourierLogMoment_smul, connes_gauss_fourierLogMoment]
    have hlog2pi : Real.log (2 * π) = Real.log 2 + Real.log π :=
      Real.log_mul (by norm_num) (ne_of_gt Real.pi_pos)
    rw [hlog2pi]
    push_cast
    ring
  rw [hvalue] at hfinal
  exact hfinal

end

end GaloisForLFunctions.RHTower
