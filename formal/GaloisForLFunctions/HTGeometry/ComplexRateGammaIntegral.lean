import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The Gamma integral at a complex rate

**Theorem** (`integral_cpow_mul_cexp_neg_mul_complex`).  For `Re w > 0` and `Re κ > 0`,

`∫_0^∞ y^{w-1} e^{-κ y} dy = Γ(w) κ^{-w}`.

Both sides are holomorphic in `κ` on the right half-plane.  The integral is differentiated under the
integral sign, with domination `y^{Re w} e^{-(Re κ₀/2) y}` on the disc of radius `Re κ₀/2`.  The two
sides agree for real `κ > 0`, so the identity theorem extends the formula.
-/

open MeasureTheory Set Filter Complex
open scoped Topology

noncomputable section

namespace HTGeometry

/-- The integrand `y^{w-1} e^{-κ y}`. -/
def complexRateGammaIntegrand (w κ : ℂ) (y : ℝ) : ℂ := (y : ℂ) ^ (w - 1) * cexp (-(κ * y))

theorem norm_complexRateGammaIntegrand {w κ : ℂ} {y : ℝ} (hy : 0 < y) :
    ‖complexRateGammaIntegrand w κ y‖ = y ^ (w.re - 1) * Real.exp (-(κ.re * y)) := by
  rw [complexRateGammaIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
    Complex.norm_exp]
  simp

theorem integrableOn_rpow_mul_exp_neg_mul {s b : ℝ} (hs : 0 < s) (hb : 0 < b) :
    IntegrableOn (fun y : ℝ => y ^ (s - 1) * Real.exp (-(b * y))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1) (b := b)
    (by linarith) le_rfl hb
  refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
  simp [Real.rpow_one, neg_mul]

theorem integrableOn_complexRateGammaIntegrand {w κ : ℂ} (hw : 0 < w.re) (hκ : 0 < κ.re) :
    IntegrableOn (complexRateGammaIntegrand w κ) (Ioi 0) := by
  refine Integrable.congr' (integrableOn_rpow_mul_exp_neg_mul hw hκ) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    refine (ContinuousAt.mul ?_ ?_).continuousWithinAt
    · exact (continuousAt_ofReal_cpow_const _ _ (Or.inr hy0.ne'))
    · exact (Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal).neg).continuousAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : (0 : ℝ) < y := hy
    rw [norm_complexRateGammaIntegrand hy0, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]

theorem integral_complexRateGammaIntegrand_ofReal {w : ℂ} (hw : 0 < w.re) {r : ℝ} (hr : 0 < r) :
    ∫ y in Ioi (0 : ℝ), complexRateGammaIntegrand w r y = Complex.Gamma w * (r : ℂ) ^ (-w) := by
  have h := integral_cpow_mul_exp_neg_mul_Ioi hw hr
  unfold complexRateGammaIntegrand
  rw [h, mul_comm, one_div, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_pos.ne), Complex.cpow_neg]

theorem hasDerivAt_integral_complexRateGammaIntegrand {w κ₀ : ℂ} (hw : 0 < w.re)
    (hκ : 0 < κ₀.re) :
    HasDerivAt (fun κ => ∫ y in Ioi (0 : ℝ), complexRateGammaIntegrand w κ y)
      (∫ y in Ioi (0 : ℝ), -((y : ℂ) * complexRateGammaIntegrand w κ₀ y)) κ₀ := by
  set ε : ℝ := κ₀.re / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hball : ∀ κ ∈ Metric.ball κ₀ ε, ε < κ.re := by
    intro κ hκb
    have h1 : |(κ - κ₀).re| ≤ ‖κ - κ₀‖ := Complex.abs_re_le_norm _
    have h2 : ‖κ - κ₀‖ < ε := by simpa [dist_eq_norm] using hκb
    rw [Complex.sub_re] at h1
    have := (abs_lt.mp (lt_of_le_of_lt h1 h2)).1
    linarith
  have hbound_int : IntegrableOn (fun y : ℝ => y ^ (w.re + 1 - 1) * Real.exp (-(ε * y)))
      (Ioi 0) := integrableOn_rpow_mul_exp_neg_mul (by linarith) hε0
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ) (μ := volume.restrict (Ioi 0))
    (F := fun κ y => complexRateGammaIntegrand w κ y)
    (F' := fun κ y => -((y : ℂ) * complexRateGammaIntegrand w κ y)) (x₀ := κ₀)
    (bound := fun y : ℝ => y ^ (w.re + 1 - 1) * Real.exp (-(ε * y)))
    (Metric.ball_mem_nhds κ₀ hε0) ?_ ?_ ?_ ?_ hbound_int ?_).2
  · filter_upwards [Metric.ball_mem_nhds κ₀ hε0] with κ hκb
    exact (integrableOn_complexRateGammaIntegrand hw
      (by linarith [hball κ hκb])).aestronglyMeasurable
  · exact integrableOn_complexRateGammaIntegrand hw hκ
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    refine (ContinuousAt.neg (ContinuousAt.mul continuous_ofReal.continuousAt
      (ContinuousAt.mul ?_ ?_))).continuousWithinAt
    · exact (continuousAt_ofReal_cpow_const _ _ (Or.inr hy0.ne'))
    · exact (Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal).neg).continuousAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy κ hκb
    have hy0 : (0 : ℝ) < y := hy
    rw [norm_neg, norm_mul, norm_complexRateGammaIntegrand hy0, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hy0]
    have hexp : Real.exp (-(κ.re * y)) ≤ Real.exp (-(ε * y)) := by
      rw [Real.exp_le_exp]
      nlinarith [hball κ hκb]
    calc y * (y ^ (w.re - 1) * Real.exp (-(κ.re * y)))
        = y ^ (w.re + 1 - 1) * Real.exp (-(κ.re * y)) := by
          rw [show w.re + 1 - 1 = (w.re - 1) + 1 by ring, Real.rpow_add_one hy0.ne']; ring
      _ ≤ y ^ (w.re + 1 - 1) * Real.exp (-(ε * y)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y _ κ _
    unfold complexRateGammaIntegrand
    have h := ((hasDerivAt_id κ).mul_const (y : ℂ)).neg.cexp.const_mul ((y : ℂ) ^ (w - 1))
    refine h.congr_deriv ?_
    simp only [id, one_mul, Pi.neg_apply]
    ring

theorem analyticOnNhd_integral_complexRateGammaIntegrand {w : ℂ} (hw : 0 < w.re) :
    AnalyticOnNhd ℂ (fun κ => ∫ y in Ioi (0 : ℝ), complexRateGammaIntegrand w κ y)
      {κ : ℂ | 0 < κ.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro κ hκ
  exact (hasDerivAt_integral_complexRateGammaIntegrand hw hκ).differentiableAt.differentiableWithinAt

/-- **The Gamma integral at a complex rate.**  `∫_0^∞ y^{w-1} e^{-κy} dy = Γ(w) κ^{-w}` for
`Re w > 0` and `Re κ > 0`. -/
theorem integral_cpow_mul_cexp_neg_mul_complex {w κ : ℂ} (hw : 0 < w.re) (hκ : 0 < κ.re) :
    ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (w - 1) * cexp (-(κ * y)) = Complex.Gamma w * κ ^ (-w) := by
  set U : Set ℂ := {κ : ℂ | 0 < κ.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hleft := analyticOnNhd_integral_complexRateGammaIntegrand hw
  have hright : AnalyticOnNhd ℂ (fun κ : ℂ => Complex.Gamma w * κ ^ (-w)) U := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro κ hκ
    have hslit : κ ∈ Complex.slitPlane := Or.inl hκ
    exact ((differentiableAt_id.cpow (differentiableAt_const (-w)) hslit).const_mul
      _).differentiableWithinAt
  have hone : (1 : ℂ) ∈ U := by simp [hU]
  -- agreement on the positive reals, which accumulate at `1`
  have hfreq : ∃ᶠ κ in 𝓝[≠] (1 : ℂ), (fun κ => ∫ y in Ioi (0 : ℝ), complexRateGammaIntegrand w κ y)
      κ = (fun κ : ℂ => Complex.Gamma w * κ ^ (-w)) κ := by
    have hmap : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      simpa using hr
    have hpos : ∀ᶠ r : ℝ in 𝓝[≠] (1 : ℝ), 0 < r :=
      eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds (by norm_num))
    refine hmap.frequently (hpos.frequently.mono fun r hr => ?_)
    exact integral_complexRateGammaIntegrand_ofReal hw hr
  have heq := hleft.eqOn_of_preconnected_of_frequently_eq hright hUconn hone hfreq
  exact heq hκ

end HTGeometry
