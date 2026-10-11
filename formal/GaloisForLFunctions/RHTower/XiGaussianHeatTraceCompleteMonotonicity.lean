import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalLineReceiver
import GaloisForLFunctions.RHTower.ThetaCriticalFluxBernstein
import GaloisForLFunctions.RHTower.ThetaRateLaplaceBernstein
import GaloisForLFunctions.RHTower.LiClockThetaSingleDampingStrip

/-!
# RH as complete monotonicity of the zero heat trace

**Theorem** (`riemannHypothesis_iff_completelyMonotoneOn_xiGaussianHeatTraceReal`).  RH holds iff
the real zero heat trace `ν(t) = Σ_q e^{-t w_q}` is completely monotone on `(0, ∞)`.  Equivalently,
the heat moments `M_n(t) = (−1)^n ν^{(n)}(t)` are all nonnegative: a sign-only criterion for the
explicit arithmetic moments `(−1)^n (Arch − Prime)^{(n)}(t)/π + 2(−¼)^n e^{t/4}`.

Proof.
* Under RH every frequency `w_q = γ_q²` is real and nonnegative, so `ν` is a positive exponential
  sum (`completelyMonotoneOn_tsum_exp`).
* Conversely, Bernstein–Widder (`exists_rateMeasure_of_completelyMonotoneOn`) writes
  `ν(t) = ∫ e^{-tλ} dμ(λ)` with a positive measure `μ` on `[0, ∞)`.
  - The complex Laplace transform `F(τ) = ∫ e^{-τλ} dμ` is holomorphic on `Re τ > 0`, by
    differentiation under the integral sign with the domination `λ e^{-3cλ} ≤ c⁻¹ e^{-2cλ}`.
  - It agrees with the complex heat trace on `(0, ∞)`, hence on the right half-plane by the identity
    theorem.
  - So `‖ν(a+ib)‖ ≤ ∫ e^{-aλ} dμ = ν(a)`, which is RH
    (`riemannHypothesis_iff_forall_norm_xiGaussianHeatTraceC_le_real`).
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped ENNReal
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The complex Laplace transform of a rate measure -/

/-- The complex Laplace transform `F(τ) = ∫ e^{-τλ} dμ(λ)`. -/
def rateLaplaceC (μ : Measure ℝ) (τ : ℂ) : ℂ := ∫ l, Complex.exp (-(τ * l)) ∂μ

theorem norm_cexp_neg_mul_ofReal_rateLaplace (τ : ℂ) (l : ℝ) :
    ‖Complex.exp (-(τ * l))‖ = Real.exp (-(τ.re * l)) := by
  rw [Complex.norm_exp]
  congr 1
  simp

theorem integrable_exp_of_rateLaplace_ne_top {μ : Measure ℝ} {t : ℝ} (hfin : rateLaplace μ t ≠ ∞) :
    Integrable (fun l : ℝ => Real.exp (-(t * l))) μ := by
  refine ⟨(by fun_prop : Continuous fun l : ℝ => Real.exp (-(t * l))).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lt_top_iff_ne_top]
  convert hfin using 2 with l
  rw [rateLaplace]
  congr 1
  funext l
  rw [← ofReal_norm, Real.norm_of_nonneg (Real.exp_pos _).le]

theorem integrable_cexp_of_rateLaplace_ne_top {μ : Measure ℝ} {τ : ℂ}
    (hfin : rateLaplace μ τ.re ≠ ∞) : Integrable (fun l : ℝ => Complex.exp (-(τ * l))) μ := by
  refine (integrable_exp_of_rateLaplace_ne_top hfin).mono'
    (by fun_prop : Continuous fun l : ℝ => Complex.exp (-(τ * l))).aestronglyMeasurable ?_
  exact Eventually.of_forall fun l => (norm_cexp_neg_mul_ofReal_rateLaplace τ l).le

theorem integral_exp_eq_rateLaplace_toReal {μ : Measure ℝ} (t : ℝ) :
    ∫ l, Real.exp (-(t * l)) ∂μ = (rateLaplace μ t).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun l => (Real.exp_pos _).le)
    (by fun_prop : Continuous fun l : ℝ => Real.exp (-(t * l))).aestronglyMeasurable, rateLaplace]

theorem rateLaplaceC_ofReal {μ : Measure ℝ} (t : ℝ) :
    rateLaplaceC μ t = ((rateLaplace μ t).toReal : ℂ) := by
  rw [rateLaplaceC, ← integral_exp_eq_rateLaplace_toReal,
    ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun l => ?_)
  simp only [ofReal_exp, ofReal_neg, ofReal_mul]

theorem norm_rateLaplaceC_le (μ : Measure ℝ) (τ : ℂ) :
    ‖rateLaplaceC μ τ‖ ≤ (rateLaplace μ τ.re).toReal := by
  rw [rateLaplaceC, ← integral_exp_eq_rateLaplace_toReal]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  exact integral_congr_ae (Eventually.of_forall fun l => norm_cexp_neg_mul_ofReal_rateLaplace τ l)

theorem mul_exp_neg_le_inv_rateLaplace {c l : ℝ} (hc : 0 < c) : l * Real.exp (-(c * l)) ≤ 1 / c := by
  have h := Real.add_one_le_exp (c * l)
  have hpos := Real.exp_pos (c * l)
  rw [Real.exp_neg, le_div_iff₀ hc]
  calc l * (Real.exp (c * l))⁻¹ * c = (c * l) / Real.exp (c * l) := by field_simp
    _ ≤ 1 := by rw [div_le_one hpos]; linarith

/-- The complex Laplace transform of a rate measure with finite real transforms is holomorphic on the
right half-plane. -/
theorem differentiableAt_rateLaplaceC {μ : Measure ℝ} (hsupp : μ (Ici 0)ᶜ = 0)
    (hfin : ∀ t, 0 < t → rateLaplace μ t ≠ ∞) {τ₀ : ℂ} (hτ₀ : 0 < τ₀.re) :
    DifferentiableAt ℂ (rateLaplaceC μ) τ₀ := by
  set c := τ₀.re / 4 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hae : ∀ᵐ l ∂μ, 0 ≤ l := by
    rw [ae_iff]
    simpa [compl_def, mem_Ici, not_le] using hsupp
  have hball : ∀ τ ∈ ball τ₀ c, 3 * c ≤ τ.re := by
    intro τ hτ
    rw [mem_ball, dist_eq_norm] at hτ
    have := abs_re_le_norm (τ - τ₀)
    rw [sub_re] at this
    have h1 := (abs_lt.1 (lt_of_le_of_lt this hτ)).1
    rw [hc] at h1 ⊢
    linarith
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun τ (l : ℝ) => Complex.exp (-(τ * l)))
    (F' := fun τ (l : ℝ) => -(l : ℂ) * Complex.exp (-(τ * l)))
    (bound := fun l => 1 / c * Real.exp (-(2 * c * l)))
    (ball_mem_nhds τ₀ hc0)
    (Eventually.of_forall fun τ =>
      (by fun_prop : Continuous fun l : ℝ => Complex.exp (-(τ * l))).aestronglyMeasurable)
    (integrable_cexp_of_rateLaplace_ne_top (hfin _ hτ₀))
    (by fun_prop : Continuous fun l : ℝ => -(l : ℂ) * Complex.exp (-(τ₀ * l))).aestronglyMeasurable
    (hae.mono fun l hl τ hτ => by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hl, norm_cexp_neg_mul_ofReal_rateLaplace]
      have h3 := hball τ hτ
      have hexp : Real.exp (-(τ.re * l)) ≤ Real.exp (-(c * l)) * Real.exp (-(2 * c * l)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.2 (by nlinarith)
      calc l * Real.exp (-(τ.re * l)) ≤ l * (Real.exp (-(c * l)) * Real.exp (-(2 * c * l))) :=
            mul_le_mul_of_nonneg_left hexp hl
        _ = (l * Real.exp (-(c * l))) * Real.exp (-(2 * c * l)) := by ring
        _ ≤ 1 / c * Real.exp (-(2 * c * l)) :=
            mul_le_mul_of_nonneg_right (mul_exp_neg_le_inv_rateLaplace hc0) (Real.exp_pos _).le)
    ((integrable_exp_of_rateLaplace_ne_top (hfin _ (by linarith))).const_mul _)
    (Eventually.of_forall fun l τ _ => by
      have h : HasDerivAt (fun x : ℂ => Complex.exp (-(x * l)))
          (Complex.exp (-(τ * l)) * -(1 * (l : ℂ))) τ :=
        ((hasDerivAt_id' τ).mul_const (l : ℂ)).neg.cexp
      exact h.congr_deriv (by ring))
  exact hderiv.2.differentiableAt

/-! ## The criterion -/

theorem xiGaussianHeatTraceC_ofReal_eq (t : ℝ) :
    xiGaussianHeatTraceC (t : ℂ) = ((xiGaussianHeatTraceReal t : ℝ) : ℂ) := by
  have him := xiGaussianHeatTrace_im_eq_zero t
  have h : xiGaussianHeatTraceC (t : ℂ) = xiGaussianHeatTrace t := rfl
  rw [h, xiGaussianHeatTraceReal]
  exact (Complex.ext rfl (by simp [him]))

/-- Under RH the real heat trace is a positive exponential sum, hence completely monotone. -/
theorem completelyMonotoneOn_xiGaussianHeatTraceReal_of_riemannHypothesis
    (hRH : RiemannHypothesis) : CompletelyMonotoneOn xiGaussianHeatTraceReal := by
  have hreal := (riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero).1 hRH
  set lam : XiZeroCopy → ℝ := fun q => (xiSpectralPoint q).re ^ 2 with hlam
  have hterm : ∀ t : ℝ, ∀ q, (xiGaussianHeatTerm t q).re = 1 * Real.exp (-lam q * t) := by
    intro t q
    have hz : xiSpectralPoint q = ((xiSpectralPoint q).re : ℂ) := by
      apply Complex.ext <;> simp [hreal q]
    rw [xiGaussianHeatTerm, hz, one_mul, hlam]
    rw [show -(t : ℂ) * ((xiSpectralPoint q).re : ℂ) ^ 2 =
      ((-((xiSpectralPoint q).re ^ 2) * t : ℝ) : ℂ) by push_cast; ring, ← ofReal_exp, ofReal_re]
  have hsum : ∀ t, 0 < t → Summable fun q => 1 * Real.exp (-lam q * t) := fun t ht => by
    have := (summable_xiGaussianHeatTerm ht).mapL Complex.reCLM
    simpa [hterm t] using this
  have hcm := completelyMonotoneOn_tsum_exp (fun _ : XiZeroCopy => (1 : ℝ)) lam
    (fun _ => zero_le_one) (fun q => sq_nonneg _) hsum
  have heq : EqOn (fun t => ∑' q, 1 * Real.exp (-lam q * t)) xiGaussianHeatTraceReal (Ioi 0) := by
    intro t ht
    rw [xiGaussianHeatTraceReal_eq_tsum_re ht]
    exact tsum_congr fun q => (hterm t q).symm
  exact ⟨completelyMonotoneDiff_congr_Ioi heq hcm.1, hcm.2.congr fun t ht => (heq ht).symm⟩

/-- **RH as complete monotonicity of the zero heat trace.** -/
theorem riemannHypothesis_iff_completelyMonotoneOn_xiGaussianHeatTraceReal :
    RiemannHypothesis ↔ CompletelyMonotoneOn xiGaussianHeatTraceReal := by
  refine ⟨completelyMonotoneOn_xiGaussianHeatTraceReal_of_riemannHypothesis, fun hcm => ?_⟩
  obtain ⟨μ, hsupp, hfin, hrep⟩ := exists_rateMeasure_of_completelyMonotoneOn hcm
  set U : Set ℂ := {τ | 0 < τ.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconv : Convex ℝ U := convex_halfSpace_re_gt 0
  have hF : AnalyticOnNhd ℂ (rateLaplaceC μ) U :=
    DifferentiableOn.analyticOnNhd (fun τ hτ =>
      (differentiableAt_rateLaplaceC hsupp hfin hτ).differentiableWithinAt) hUopen
  have hG : AnalyticOnNhd ℂ xiGaussianHeatTraceC U :=
    DifferentiableOn.analyticOnNhd (fun τ hτ =>
      (differentiableAt_xiGaussianHeatTraceC hτ).differentiableWithinAt) hUopen
  have hreal : ∀ t : ℝ, 0 < t → rateLaplaceC μ t = xiGaussianHeatTraceC t := by
    intro t ht
    rw [rateLaplaceC_ofReal, xiGaussianHeatTraceC_ofReal_eq, hrep t ht]
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), rateLaplaceC μ z = xiGaussianHeatTraceC z := by
    have hseq : Tendsto (fun n : ℕ => (((1 : ℝ) + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop
        (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
          simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
        have hc := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp h
        rw [Complex.ofReal_one] at hc
        exact hc
      · simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        have h' : (1 : ℝ) + 1 / ((n : ℝ) + 1) = 1 := by exact_mod_cast h
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    exact hseq.frequently (Frequently.of_forall fun n => hreal _ (by positivity))
  have heq := hF.eqOn_of_preconnected_of_frequently_eq hG hUconv.isPreconnected
    (show (1 : ℂ) ∈ U by simp [hU]) hfreq
  rw [riemannHypothesis_iff_forall_norm_xiGaussianHeatTraceC_le_real one_pos]
  intro b
  have hmem : ((1 : ℝ) : ℂ) + b * I ∈ U := by simp [hU]
  rw [← heq hmem]
  have hre : ((((1 : ℝ) : ℂ) + b * I)).re = 1 := by simp
  have h := norm_rateLaplaceC_le μ (((1 : ℝ) : ℂ) + b * I)
  rw [hre] at h
  rw [hrep 1 one_pos]
  exact h

end

end RHTower
