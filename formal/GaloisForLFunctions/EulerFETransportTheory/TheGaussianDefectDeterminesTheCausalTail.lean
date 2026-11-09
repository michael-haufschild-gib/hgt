import GaloisForLFunctions.HTGeometry.LaplaceAtomicRigidity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Recovery of a causal tail from the literal Gaussian defect

The rate coordinate `u = exp(2t) - 1` turns outward translation of the Gaussian
base into a half-line Laplace transform. Its first-order differential defect
is the Laplace transform of the rate density multiplied by `u`. Thus the
differential defect retains the entire signed causal density; the scalar
identity term is invisible.
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.EulerFETransportTheory

noncomputable section

/-- Laplace transform of the integrable density in the Gaussian rate coordinate. -/
def gaussianRateLaplace (q : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), q u * Complex.exp (-z * u)

/-- The rate moment measured by the Gaussian differential defect. -/
def gaussianRateMoment (q : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), (u : ℂ) * q u * Complex.exp (-z * u)

private theorem norm_rate_exp (z : ℂ) (u : ℝ) :
    ‖Complex.exp (-z * u)‖ = Real.exp (-z.re * u) := by
  rw [Complex.norm_exp]
  congr 1
  simp

private theorem rate_moment_bound {c u : ℝ} (hc : 0 < c) :
    u * Real.exp (-c * u) ≤ c⁻¹ := by
  have h1 : c * u ≤ Real.exp (c * u) := by
    linarith [Real.add_one_le_exp (c * u)]
  have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-c * u)).le
  have he : Real.exp (c * u) * Real.exp (-c * u) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [he] at h2
  rw [← one_div]
  exact (le_div_iff₀ hc).2 (by nlinarith)

theorem integrable_gaussianRateLaplace {q : ℝ → ℂ}
    (hq : IntegrableOn q (Ioi 0)) {z : ℂ} (hz : 0 ≤ z.re) :
    IntegrableOn (fun u : ℝ => q u * Complex.exp (-z * u)) (Ioi 0) := by
  refine hq.norm.mono' (hq.aestronglyMeasurable.mul (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [norm_mul, norm_rate_exp]
  exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.2
    (by rw [neg_mul]; exact neg_nonpos.2 (mul_nonneg hz hu.le)))

theorem integrable_gaussianRateMoment {q : ℝ → ℂ}
    (hq : IntegrableOn q (Ioi 0)) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) * q u * Complex.exp (-z * u)) (Ioi 0) := by
  refine (hq.norm.const_mul z.re⁻¹).mono'
    (((by fun_prop : AEStronglyMeasurable (fun u : ℝ => (u : ℂ))
      (volume.restrict (Ioi 0))).mul hq.aestronglyMeasurable).mul (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu.le, norm_rate_exp]
  nlinarith [mul_le_mul_of_nonneg_right (rate_moment_bound (u := u) hz) (norm_nonneg (q u))]

/-- Differentiation retains the full causal density, with no moment assumption. -/
theorem hasDerivAt_gaussianRateLaplace {q : ℝ → ℂ}
    (hq : IntegrableOn q (Ioi 0)) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (gaussianRateLaplace q) (-gaussianRateMoment q z) z := by
  let c := z.re / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hball : ∀ w ∈ Metric.ball z c, c < w.re := by
    intro w hw
    have h1 := Complex.abs_re_le_norm (w - z)
    have h2 : ‖w - z‖ < c := by simpa [dist_eq_norm] using hw
    simp only [Complex.sub_re] at h1
    have h3 := (abs_lt.1 (h1.trans_lt h2)).1
    dsimp [c] at *
    linarith
  have hd : IntegrableOn (fun u : ℝ => -((u : ℂ) * q u * Complex.exp (-z * u))) (Ioi 0) ∧
      HasDerivAt (gaussianRateLaplace q)
        (∫ u in Ioi (0 : ℝ), -((u : ℂ) * q u * Complex.exp (-z * u))) z :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun w u => q u * Complex.exp (-w * u))
    (F' := fun w u => -((u : ℂ) * q u * Complex.exp (-w * u)))
    (bound := fun u => c⁻¹ * ‖q u‖) (x₀ := z)
    (Metric.ball_mem_nhds z hc)
    (Eventually.of_forall fun w => hq.aestronglyMeasurable.mul (by fun_prop))
    (integrable_gaussianRateLaplace hq hz.le)
    ((((by fun_prop : AEStronglyMeasurable (fun u : ℝ => (u : ℂ))
      (volume.restrict (Ioi 0))).mul hq.aestronglyMeasurable).mul (by fun_prop)).neg)
    ?_ (hq.norm.const_mul c⁻¹) ?_
  · simpa only [gaussianRateLaplace, gaussianRateMoment, integral_neg] using hd.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu w hw
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hu.le, norm_rate_exp]
    have h1 : Real.exp (-w.re * u) ≤ Real.exp (-c * u) :=
      Real.exp_le_exp.2 (by
        have := mul_le_mul_of_nonneg_right (hball w hw).le hu.le
        linarith)
    calc u * ‖q u‖ * Real.exp (-w.re * u)
        ≤ u * ‖q u‖ * Real.exp (-c * u) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hu.le (norm_nonneg _))
      _ ≤ c⁻¹ * ‖q u‖ := by
        nlinarith [mul_le_mul_of_nonneg_right (rate_moment_bound (u := u) hc) (norm_nonneg (q u))]
  · exact Eventually.of_forall fun u w _ =>
      (((hasDerivAt_id w).neg.mul_const (u : ℂ)).cexp.const_mul (q u)).congr_deriv
        (by simp only [Pi.neg_apply, id]; ring)

theorem analyticOnNhd_gaussianRateLaplace {q : ℝ → ℂ}
    (hq : IntegrableOn q (Ioi 0)) :
    AnalyticOnNhd ℂ (gaussianRateLaplace q) {z : ℂ | 0 < z.re} := by
  have hd : DifferentiableOn ℂ (gaussianRateLaplace q) {z : ℂ | 0 < z.re} :=
    fun z hz => (hasDerivAt_gaussianRateLaplace hq hz).differentiableAt.differentiableWithinAt
  exact fun z hz => hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)

theorem analyticOnNhd_gaussianRateMoment {q : ℝ → ℂ}
    (hq : IntegrableOn q (Ioi 0)) :
    AnalyticOnNhd ℂ (gaussianRateMoment q) {z : ℂ | 0 < z.re} := by
  intro z hz
  have heq : gaussianRateMoment q =ᶠ[𝓝 z] fun w => -deriv (gaussianRateLaplace q) w := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
    rw [(hasDerivAt_gaussianRateLaplace hq hw).deriv, neg_neg]
  exact ((analyticOnNhd_gaussianRateLaplace hq z hz).deriv.neg).congr heq.symm

/-- Local values of the rate moment determine the whole integrable causal density. -/
theorem ae_eq_zero_of_gaussianRateMoment_local {q : ℝ → ℂ}
    (hq : IntegrableOn q (Ioi 0)) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hzero : ∀ r ∈ Ioo a b, gaussianRateMoment q r = 0) :
    q =ᵐ[volume.restrict (Ioi 0)] 0 := by
  let c := (a + b) / 2
  have hc : c ∈ Ioo a b := by dsimp [c]; constructor <;> linarith
  have hev : ∀ᶠ r : ℝ in 𝓝[≠] c, gaussianRateMoment q r = 0 :=
    (eventually_nhdsWithin_of_eventually_nhds (Ioo_mem_nhds hc.1 hc.2)).mono
      (fun r hr => hzero r hr)
  have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] c) (𝓝[≠] (c : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨(Complex.continuous_ofReal.tendsto c).mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj] using hr
  have hall := (analyticOnNhd_gaussianRateMoment hq).eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected
    (show 0 < (c : ℂ).re from ha.trans hc.1) (ht.frequently hev.frequently)
  let g : ℝ → ℂ := fun u => (u : ℂ) * q u * Complex.exp (-(u : ℂ))
  have hg : IntegrableOn g (Ioi 0) := by
    simpa only [neg_mul, one_mul] using
      (integrable_gaussianRateMoment hq (z := 1) (by norm_num))
  have hg0 : g =ᵐ[volume.restrict (Ioi 0)] 0 := by
    apply HTGeometry.ae_eq_zero_of_laplace_ae_eq_zero hg
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hz : gaussianRateMoment q ((r + 1 : ℝ) : ℂ) = 0 :=
      hall (show 0 < (((r + 1 : ℝ) : ℂ)).re from add_pos hr zero_lt_one)
    rw [← hz, gaussianRateMoment]
    apply integral_congr_ae
    filter_upwards with u
    dsimp [g]
    rw [Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  filter_upwards [hg0, ae_restrict_mem measurableSet_Ioi] with u hu hupos
  have he : (u : ℂ) * q u = 0 :=
    (mul_eq_zero.1 hu).resolve_right (Complex.exp_ne_zero _)
  exact (mul_eq_zero.1 he).resolve_left (by exact_mod_cast hupos.ne')

/-- Equality of the observed rate moments identifies arbitrary complex causal densities. -/
theorem ae_eq_of_gaussianRateMoment_local {q r : ℝ → ℂ}
    (hq : IntegrableOn q (Ioi 0)) (hr : IntegrableOn r (Ioi 0))
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (heq : ∀ s ∈ Ioo a b, gaussianRateMoment q s = gaussianRateMoment r s) :
    q =ᵐ[volume.restrict (Ioi 0)] r := by
  have hzero := ae_eq_zero_of_gaussianRateMoment_local (hq.sub hr) ha hab (fun s hs => by
    have hs0 : 0 < (s : ℂ).re := ha.trans hs.1
    simp only [gaussianRateMoment, Pi.sub_apply, mul_sub, sub_mul]
    rw [integral_sub (integrable_gaussianRateMoment hq hs0)
      (integrable_gaussianRateMoment hr hs0)]
    exact sub_eq_zero.2 (heq s hs))
  filter_upwards [hzero] with u hu
  exact sub_eq_zero.1 hu

#print axioms ae_eq_of_gaussianRateMoment_local

end

end GaloisForLFunctions.EulerFETransportTheory
