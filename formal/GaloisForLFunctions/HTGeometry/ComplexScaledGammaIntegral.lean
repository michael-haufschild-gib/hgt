import GaloisForLFunctions.HTGeometry.BarnesMellinRepresentation
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# The Euler integral with a complex scale

For `Re a > 0` and `Re c > 0`,

`∫₀^∞ t^{a-1} e^{-ct} dt = Γ(a) / c^a`.

Mathlib supplies this for a positive real scale.  Both sides are holomorphic in the scale on the
open right half-plane, which is convex and therefore preconnected, so the identity theorem extends
the real-scale evaluation to every complex scale with positive real part.  This is the analytic
continuation that carries the Euler integral toward the oscillatory boundary values used by the
half-log scattering classification.
-/

open Complex MeasureTheory Set Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Euler integral with a complex scale. -/
def gammaScaledIntegral (a c : ℂ) : ℂ :=
  ∫ t in Ioi (0:ℝ), (t : ℂ) ^ (a - 1) * Complex.exp (-(c * t))

theorem norm_cpow_mul_cexp {a c : ℂ} {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (a - 1) * Complex.exp (-(c * t))‖
      = t ^ (a.re - 1) * Real.exp (-(c.re * t)) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]

/-- The scaled Euler integrand is integrable on the ray. -/
theorem integrableOn_cpow_mul_cexp {a c : ℂ} (ha : 0 < a.re) (hc : 0 < c.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) * Complex.exp (-(c * t))) (Ioi 0) volume := by
  have hbase := integrableOn_rpow_mul_exp_neg_mul_Ioi (σ := a.re - 1) (a := c.re)
    (by linarith) hc
  refine Integrable.mono' hbase ?_ ?_
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0:ℝ) < t := ht
    rw [norm_cpow_mul_cexp ht0]

/-- The scaled Euler integral is complex differentiable in the scale. -/
theorem hasDerivAt_gammaScaledIntegral {a c₀ : ℂ} (ha : 0 < a.re) (hc : 0 < c₀.re) :
    HasDerivAt (gammaScaledIntegral a)
      (∫ t in Ioi (0:ℝ), -((t : ℂ) * ((t : ℂ) ^ (a - 1) * Complex.exp (-(c₀ * t))))) c₀ := by
  set μ : Measure ℝ := volume.restrict (Ioi (0:ℝ)) with hμ
  set F : ℂ → ℝ → ℂ := fun c t => (t : ℂ) ^ (a - 1) * Complex.exp (-(c * t)) with hF
  set F' : ℂ → ℝ → ℂ :=
    fun c t => -((t : ℂ) * ((t : ℂ) ^ (a - 1) * Complex.exp (-(c * t)))) with hF'
  set δ : ℝ := c₀.re / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hballmem : Metric.ball c₀ δ ∈ nhds c₀ := Metric.ball_mem_nhds c₀ hδ0
  have hre : ∀ c ∈ Metric.ball c₀ δ, δ < c.re := by
    intro c hcb
    have hdist : ‖c - c₀‖ < δ := by
      rw [← Complex.dist_eq]
      exact Metric.mem_ball.mp hcb
    have hle : |c.re - c₀.re| ≤ ‖c - c₀‖ := by
      have := Complex.abs_re_le_norm (c - c₀)
      simpa [Complex.sub_re] using this
    have := abs_lt.mp (lt_of_le_of_lt hle hdist)
    rw [hδ] at this ⊢
    linarith [this.1]
  have hmeas : ∀ c : ℂ, AEStronglyMeasurable (F c) μ := by
    intro c
    apply Measurable.aestronglyMeasurable
    rw [hF]
    fun_prop
  have hmeas' : ∀ c : ℂ, AEStronglyMeasurable (F' c) μ := by
    intro c
    apply Measurable.aestronglyMeasurable
    rw [hF']
    fun_prop
  have hint : Integrable (F c₀) μ := integrableOn_cpow_mul_cexp ha hc
  set bound : ℝ → ℝ := fun t => t ^ a.re * Real.exp (-(δ * t)) with hbound
  have hboundint : Integrable bound μ :=
    integrableOn_rpow_mul_exp_neg_mul_Ioi (σ := a.re) (a := δ) (by linarith) hδ0
  have hderivbound : ∀ᵐ t ∂μ, ∀ c ∈ Metric.ball c₀ δ, ‖F' c t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht c hcb
    have ht0 : (0:ℝ) < t := ht
    have hcre := hre c hcb
    have hnorm : ‖F' c t‖ = t * (t ^ (a.re - 1) * Real.exp (-(c.re * t))) := by
      have hval : ‖F' c t‖ = ‖(t : ℂ)‖ * ‖(t : ℂ) ^ (a - 1) * Complex.exp (-(c * t))‖ := by
        rw [hF']
        rw [norm_neg, norm_mul]
      rw [hval, norm_cpow_mul_cexp ht0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    rw [hnorm, hbound]
    have hpow : t * t ^ (a.re - 1) = t ^ a.re := by
      have h1 : t = t ^ (1:ℝ) := (Real.rpow_one t).symm
      calc t * t ^ (a.re - 1) = t ^ (1:ℝ) * t ^ (a.re - 1) := by rw [← h1]
        _ = t ^ ((1:ℝ) + (a.re - 1)) := (Real.rpow_add ht0 1 (a.re - 1)).symm
        _ = t ^ a.re := by ring_nf
    have hexp : Real.exp (-(c.re * t)) ≤ Real.exp (-(δ * t)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hcre, ht0]
    calc t * (t ^ (a.re - 1) * Real.exp (-(c.re * t)))
        = (t * t ^ (a.re - 1)) * Real.exp (-(c.re * t)) := by ring
      _ = t ^ a.re * Real.exp (-(c.re * t)) := by rw [hpow]
      _ ≤ t ^ a.re * Real.exp (-(δ * t)) := by
          apply mul_le_mul_of_nonneg_left hexp (by positivity)
  have hdiff : ∀ᵐ t ∂μ, ∀ c ∈ Metric.ball c₀ δ, HasDerivAt (fun c => F c t) (F' c t) c := by
    filter_upwards with t c _
    have hinner0 : HasDerivAt (fun c : ℂ => -(c * (t : ℂ))) (-(1 * (t : ℂ))) c :=
      ((hasDerivAt_id c).mul_const (t : ℂ)).neg
    rw [one_mul] at hinner0
    have hinner : HasDerivAt (fun c : ℂ => -(c * (t : ℂ))) (-(t : ℂ)) c := hinner0
    have hexp : HasDerivAt (fun c : ℂ => Complex.exp (-(c * (t : ℂ))))
        (Complex.exp (-(c * (t : ℂ))) * -(t : ℂ)) c := hinner.cexp
    have hmul := hexp.const_mul ((t : ℂ) ^ (a - 1))
    show HasDerivAt (fun c : ℂ => (t : ℂ) ^ (a - 1) * Complex.exp (-(c * (t : ℂ))))
      (-((t : ℂ) * ((t : ℂ) ^ (a - 1) * Complex.exp (-(c * (t : ℂ)))))) c
    have hval : -((t : ℂ) * ((t : ℂ) ^ (a - 1) * Complex.exp (-(c * (t : ℂ)))))
        = (t : ℂ) ^ (a - 1) * (Complex.exp (-(c * (t : ℂ))) * -(t : ℂ)) := by ring
    rw [hval]
    exact hmul
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (x₀ := c₀)
    (bound := bound) (μ := μ) hballmem (Filter.Eventually.of_forall hmeas) hint (hmeas' c₀)
    hderivbound hboundint hdiff
  exact h.2

/-! ## The identity theorem in the scale -/

theorem isOpen_rightHalfPlane : IsOpen {c : ℂ | 0 < c.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem isPreconnected_rightHalfPlane : IsPreconnected {c : ℂ | 0 < c.re} :=
  (convex_halfSpace_re_gt 0).isPreconnected

/-- **The complex-scaled Euler integral.** -/
theorem gammaScaledIntegral_eq {a : ℂ} (ha : 0 < a.re) {c : ℂ} (hc : 0 < c.re) :
    gammaScaledIntegral a c = Complex.Gamma a / c ^ a := by
  set S : Set ℂ := {z : ℂ | 0 < z.re} with hS
  have hopen : IsOpen S := isOpen_rightHalfPlane
  have hslit : ∀ z ∈ S, z ∈ Complex.slitPlane := by
    intro z hz
    exact Or.inl hz
  have hLdiff : DifferentiableOn ℂ (gammaScaledIntegral a) S := by
    intro z hz
    exact ((hasDerivAt_gammaScaledIntegral ha hz).differentiableAt).differentiableWithinAt
  have hRdiff : DifferentiableOn ℂ (fun z : ℂ => Complex.Gamma a / z ^ a) S := by
    intro z hz
    have hzs : z ∈ Complex.slitPlane := hslit z hz
    have hcpow : DifferentiableAt ℂ (fun w : ℂ => w ^ a) z :=
      (differentiableAt_id).cpow_const hzs
    have hz0 : z ≠ 0 := by
      intro h
      rw [hS] at hz
      rw [h] at hz
      simp at hz
    have hne : (z : ℂ) ^ a ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      intro hcon
      exact hz0 hcon.1
    exact (((differentiableAt_const _).div hcpow hne)).differentiableWithinAt
  have hLan : AnalyticOnNhd ℂ (gammaScaledIntegral a) S := hLdiff.analyticOnNhd hopen
  have hRan : AnalyticOnNhd ℂ (fun z : ℂ => Complex.Gamma a / z ^ a) S :=
    hRdiff.analyticOnNhd hopen
  have hreal : ∀ r : ℝ, 0 < r → gammaScaledIntegral a (r : ℂ)
      = Complex.Gamma a / (r : ℂ) ^ a := by
    intro r hr
    have hbase := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := a) (r := r) ha hr
    have harg : (r : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hr.le]
      exact ne_of_lt Real.pi_pos
    have hval : ((1 : ℂ) / (r : ℂ)) ^ a = ((r : ℂ) ^ a)⁻¹ := by
      rw [one_div, Complex.inv_cpow _ _ harg]
    rw [gammaScaledIntegral, hbase, hval, div_eq_mul_inv, mul_comm]
  have hone : (1 : ℂ) ∈ S := by
    rw [hS]
    simp
  have hfreq : ∃ᶠ z : ℂ in nhdsWithin 1 {(1 : ℂ)}ᶜ,
      gammaScaledIntegral a z = Complex.Gamma a / z ^ a := by
    have hu : Filter.Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ))
        Filter.atTop (nhdsWithin 1 {(1 : ℂ)}ᶜ) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hzero : Filter.Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ))
            Filter.atTop (nhds (0:ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
        have hreal : Filter.Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1) : ℝ))
            Filter.atTop (nhds (1:ℝ)) := by
          have h2 := (tendsto_const_nhds (x := (1:ℝ))
            (f := Filter.atTop (α := ℕ))).add hzero
          rw [add_zero] at h2
          exact h2
        exact (Complex.continuous_ofReal.tendsto (1:ℝ)).comp hreal
      · filter_upwards with n
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hcon
        have hreq : (1 + 1 / ((n : ℝ) + 1) : ℝ) = 1 := by
          exact_mod_cast hcon
        have hpos : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    refine hu.frequently (Filter.Eventually.frequently ?_)
    filter_upwards with n
    exact hreal (1 + 1 / ((n : ℝ) + 1)) (by positivity)
  have heq := hLan.eqOn_of_preconnected_of_frequently_eq hRan isPreconnected_rightHalfPlane
    hone hfreq
  exact heq hc

end

end GaloisForLFunctions.HTGeometry
