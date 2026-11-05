import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicFactorExtendsToTheSlitPlane
import GaloisForLFunctions.HTGeometry.ReflectionSplitIntegral

/-!
# Reflection identity of the logarithmic factor

Analytic uniqueness identifies the slit-plane factor with its right-half-plane
Poisson integral. Real-part partial fractions give its exact squared modulus.
After an affine substitution, dominated convergence reproduces the logarithmic
symbol at every real boundary frequency. Conjugation and a second analytic
uniqueness argument give the factorization across both nonreal half-planes.
-/

open MeasureTheory Set Filter Topology Complex Metric
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open GaloisForLFunctions.HTGeometry

theorem log_positiveLogarithmicSymbol_nonneg (t : ℝ) :
    0 ≤ Real.log (positiveLogarithmicSymbol t) :=
  Real.log_nonneg (one_le_positiveLogarithmicSymbol t)

theorem log_positiveLogarithmicSymbol_le (t : ℝ) :
    Real.log (positiveLogarithmicSymbol t) ≤ Real.log (1 + t ^ 2) := by
  apply Real.log_le_log (zero_lt_one.trans_le (one_le_positiveLogarithmicSymbol t))
  have hl := Real.log_le_sub_one_of_pos (show 0 < 1 + t ^ 2 by positivity)
  unfold positiveLogarithmicSymbol
  nlinarith only [hl, sq_nonneg t]

theorem continuous_log_positiveLogarithmicSymbol :
    Continuous (fun t => Real.log (positiveLogarithmicSymbol t)) :=
  continuous_positiveLogarithmicSymbol.log
    (fun t => (zero_lt_one.trans_le (one_le_positiveLogarithmicSymbol t)).ne')

private theorem sq_mem_slitPlane_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    z ^ 2 ∈ slitPlane := by
  rcases eq_or_ne z.im 0 with hi | hi
  · apply Or.inl
    simp only [pow_two, Complex.mul_re, hi, mul_zero, sub_zero]
    exact mul_pos hz hz
  · apply Or.inr
    simp only [pow_two, Complex.mul_im]
    rw [show z.re * z.im + z.im * z.re = (2 * z.re) * z.im by ring]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hz.ne') hi

private def rightLogFactorIntegrand (z : ℂ) (t : ℝ) : ℂ :=
  z * (Real.log (positiveLogarithmicSymbol t) : ℂ) / (z ^ 2 + (t : ℂ) ^ 2)

/-- The Poisson integral defining the logarithmic factor on the right half-plane. -/
def rightLogReferenceFactor (z : ℂ) : ℂ :=
  Complex.exp ((1 / (Real.pi : ℂ)) * ∫ t in Ioi (0 : ℝ), rightLogFactorIntegrand z t)

private theorem rightLogFactor_den_ne {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    z ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by
  simpa only [Complex.ofReal_pow, add_comm] using
    ofReal_add_ne_zero (sq_mem_slitPlane_of_re_pos hz) (sq_nonneg t)

private theorem continuous_rightLogFactorIntegrand {z : ℂ} (hz : 0 < z.re) :
    Continuous (rightLogFactorIntegrand z) := by
  have hl : Continuous (fun t : ℝ => (Real.log (positiveLogarithmicSymbol t) : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_log_positiveLogarithmicSymbol
  exact (continuous_const.mul hl).div (by fun_prop) (rightLogFactor_den_ne hz)

private theorem differentiableAt_rightLogFactorIntegrand {z : ℂ} (hz : 0 < z.re)
    (t : ℝ) : DifferentiableAt ℂ (fun w => rightLogFactorIntegrand w t) z := by
  have hn : DifferentiableAt ℂ
      (fun w : ℂ => w * (Real.log (positiveLogarithmicSymbol t) : ℂ)) z := by fun_prop
  have hd : DifferentiableAt ℂ (fun w : ℂ => w ^ 2 + (t : ℂ) ^ 2) z := by fun_prop
  simpa only [rightLogFactorIntegrand] using! hn.div hd (rightLogFactor_den_ne hz t)

private theorem compact_rightLogFactorIntegrand_bound {K : Set ℂ} (hK : IsCompact K)
    (hKs : K ⊆ {z : ℂ | 0 < z.re}) :
    ∃ B : ℝ, 0 < B ∧ ∀ z ∈ K, ∀ t : ℝ,
      ‖rightLogFactorIntegrand z t‖ ≤ B * logFactorMajorant t := by
  have hK2 : IsCompact ((fun z : ℂ => z ^ 2) '' K) := hK.image (by fun_prop)
  have hK2s : (fun z : ℂ => z ^ 2) '' K ⊆ slitPlane := by
    rintro w ⟨z, hz, rfl⟩
    exact sq_mem_slitPlane_of_re_pos (hKs hz)
  obtain ⟨c, C, hc, _, hden⟩ := compact_slit_ray_bounds hK2 hK2s
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (continuous_id.continuousOn)
  refine ⟨(|M| + 1) / c, by positivity, fun z hz t => ?_⟩
  have hdb : c * (1 + t ^ 2) ≤ ‖z ^ 2 + (t : ℂ) ^ 2‖ := by
    simpa only [Complex.ofReal_pow] using
      (hden (z ^ 2) ⟨z, hz, rfl⟩ (t ^ 2) (sq_nonneg t)).1
  have hzM : ‖z‖ ≤ |M| + 1 := by
    have hzm : ‖z‖ ≤ M := by simpa only [id_eq] using hM z hz
    linarith only [hzm, le_abs_self M]
  have hl : Real.log (positiveLogarithmicSymbol t) ≤ 1 + Real.log (1 + t ^ 2) := by
    linarith only [log_positiveLogarithmicSymbol_le t]
  have hl0 : 0 ≤ Real.log (1 + t ^ 2) := Real.log_nonneg (by nlinarith only [sq_nonneg t])
  unfold rightLogFactorIntegrand
  rw [norm_div, norm_mul, Complex.norm_of_nonneg (log_positiveLogarithmicSymbol_nonneg t)]
  calc
    _ ≤ ((|M| + 1) * (1 + Real.log (1 + t ^ 2))) / (c * (1 + t ^ 2)) :=
      div_le_div₀ (by positivity)
        (mul_le_mul hzM hl (log_positiveLogarithmicSymbol_nonneg t) (by positivity))
        (mul_pos hc (by positivity)) hdb
    _ = _ := by
      simp only [logFactorMajorant, div_eq_mul_inv, mul_inv_rev]
      ring

/-- The actual right-half-plane integral is holomorphic. -/
theorem differentiableOn_rightLogReferenceFactor :
    DifferentiableOn ℂ rightLogReferenceFactor {z : ℂ | 0 < z.re} := by
  intro z hz
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp hopen z hz
  let R : ℝ := r / 2
  have hR : 0 < R := by dsimp only [R]; positivity
  have hKs : closedBall z R ⊆ {w : ℂ | 0 < w.re} := by
    intro w hw
    apply hrs
    apply Metric.mem_ball.mpr
    exact (Metric.mem_closedBall.mp hw).trans_lt (by dsimp only [R]; linarith only [hr])
  obtain ⟨B, _, hb⟩ := compact_rightLogFactorIntegrand_bound (isCompact_closedBall z R) hKs
  have hd : DifferentiableAt ℂ
      (fun w : ℂ => ∫ t in Ioi (0 : ℝ), rightLogFactorIntegrand w t) z := by
    apply differentiableAt_integral_of_cauchy_dominated
      (μ := volume.restrict (Ioi (0 : ℝ))) (bound := fun t => B * logFactorMajorant t) hR
    · intro w hw
      exact (continuous_rightLogFactorIntegrand (hKs (ball_subset_closedBall hw))).aestronglyMeasurable
    · intro t w hw
      exact (differentiableAt_rightLogFactorIntegrand (hKs (ball_subset_closedBall hw)) t).differentiableWithinAt
    · intro t w hw
      exact hb w (ball_subset_closedBall hw) t
    · exact (integrable_logFactorMajorant.const_mul B).integrableOn
  exact ((hd.const_mul (1 / (Real.pi : ℂ))).cexp).differentiableWithinAt

private theorem rightLogReferenceFactor_ofReal {s : ℝ} (hs : 0 < s) :
    rightLogReferenceFactor (s : ℂ) = (logReferenceFactor s : ℂ) := by
  have he (t : ℝ) : rightLogFactorIntegrand (s : ℂ) t =
      ((s * Real.log (positiveLogarithmicSymbol t) / (s ^ 2 + t ^ 2) : ℝ) : ℂ) := by
    unfold rightLogFactorIntegrand
    push_cast
    rfl
  unfold rightLogReferenceFactor
  rw [show rightLogFactorIntegrand (s : ℂ) = _ from funext he,
    integral_complex_ofReal, logReferenceFactor_eq_poisson hs, Complex.ofReal_exp]
  congr 1
  push_cast
  rfl

/-- Analytic uniqueness identifies the slit-plane factor with its Poisson integral. -/
theorem complexLogReferenceFactor_eq_right {z : ℂ} (hz : 0 < z.re) :
    complexLogReferenceFactor z = rightLogReferenceFactor z := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ complexLogReferenceFactor U :=
    (differentiableOn_complexLogReferenceFactor.mono (fun _ h => Or.inl h)).analyticOnNhd hUo
  have hg : AnalyticOnNhd ℂ rightLogReferenceFactor U :=
    differentiableOn_rightLogReferenceFactor.analyticOnNhd hUo
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), complexLogReferenceFactor w = rightLogReferenceFactor w := by
    let u : ℕ → ℂ := fun k => ((1 + 1 / ((k : ℝ) + 1) : ℝ) : ℂ)
    have hlim : Tendsto u atTop (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
        rw [add_zero] at h
        have h2 := (Complex.continuous_ofReal.tendsto 1).comp h
        rw [Complex.ofReal_one] at h2
        exact h2
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, u]
        intro h
        have he : (1 + 1 / ((k : ℝ) + 1) : ℝ) = 1 := by exact_mod_cast h
        have hp : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith only [he, hp]
    refine hlim.frequently (Frequently.of_forall fun k => ?_)
    have hk : (0 : ℝ) < 1 + 1 / ((k : ℝ) + 1) := by positivity
    exact (complexLogReferenceFactor_ofReal hk).trans (rightLogReferenceFactor_ofReal hk).symm
  exact hf.eqOn_of_preconnected_of_frequently_eq hg (convex_halfSpace_re_gt 0).isPreconnected
    (by simp [U]) hfreq hz

#print axioms complexLogReferenceFactor_eq_right

private theorem log_symbol_affine_bound (y u : ℝ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.log (positiveLogarithmicSymbol (y + x * u)) ≤
      Real.log (2 + 2 * y ^ 2) + Real.log (1 + u ^ 2) := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith only [hx0, hx1]
  have hxu : (x * u) ^ 2 ≤ u ^ 2 := by
    rw [mul_pow]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hx2 (sq_nonneg u)
  have hsq : 1 + (y + x * u) ^ 2 ≤ (2 + 2 * y ^ 2) * (1 + u ^ 2) := by
    nlinarith only [sq_nonneg (y - x * u), hxu, sq_nonneg u,
      mul_nonneg (sq_nonneg y) (sq_nonneg u)]
  have hlog := Real.log_le_log (by positivity : 0 < 1 + (y + x * u) ^ 2) hsq
  rw [Real.log_mul (by positivity : (2 + 2 * y ^ 2 : ℝ) ≠ 0)
    (by positivity : (1 + u ^ 2 : ℝ) ≠ 0)] at hlog
  exact (log_positiveLogarithmicSymbol_le _).trans hlog

/-- Poisson boundary reproduction holds at every real frequency. -/
theorem tendsto_logarithmic_poisson_boundary (y : ℝ) :
    Tendsto (fun x : ℝ => (1 / Real.pi) * ∫ u : ℝ,
      Real.log (positiveLogarithmicSymbol (y + x * u)) / (1 + u ^ 2))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (Real.log (positiveLogarithmicSymbol y))) := by
  let C : ℝ := Real.log (2 + 2 * y ^ 2)
  have hC : 0 ≤ C := Real.log_nonneg (by nlinarith only [sq_nonneg y])
  have hlim : Tendsto (fun x : ℝ => ∫ u : ℝ,
      Real.log (positiveLogarithmicSymbol (y + x * u)) / (1 + u ^ 2))
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds (∫ u : ℝ, Real.log (positiveLogarithmicSymbol y) / (1 + u ^ 2))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun u => (C + 1) * logFactorMajorant u)
    · exact Eventually.of_forall fun x =>
        ((continuous_log_positiveLogarithmicSymbol.comp
          (continuous_const.add (continuous_const.mul continuous_id))).div
          (continuous_const.add (continuous_id.pow 2))
          (fun u => (show 0 < 1 + u ^ 2 by positivity).ne')).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
        with x hx hx1
      filter_upwards with u
      have hlog0 : 0 ≤ Real.log (1 + u ^ 2) := Real.log_nonneg (by nlinarith only [sq_nonneg u])
      rw [Real.norm_of_nonneg (div_nonneg (log_positiveLogarithmicSymbol_nonneg _) (by positivity))]
      calc
        _ ≤ (C + Real.log (1 + u ^ 2)) / (1 + u ^ 2) :=
          div_le_div_of_nonneg_right (log_symbol_affine_bound y u hx.le hx1.le) (by positivity)
        _ ≤ ((C + 1) * (1 + Real.log (1 + u ^ 2))) / (1 + u ^ 2) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith only [mul_nonneg hC hlog0, hC]
        _ = _ := by unfold logFactorMajorant; ring
    · exact integrable_logFactorMajorant.const_mul (C + 1)
    · filter_upwards with u
      have hc : Continuous (fun x : ℝ =>
          Real.log (positiveLogarithmicSymbol (y + x * u)) / (1 + u ^ 2)) :=
        (continuous_log_positiveLogarithmicSymbol.comp
          (continuous_const.add (continuous_id.mul continuous_const))).div_const _
      simpa only [zero_mul, add_zero] using
        (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have he : (∫ u : ℝ, Real.log (positiveLogarithmicSymbol y) / (1 + u ^ 2)) =
      Real.log (positiveLogarithmicSymbol y) * Real.pi := by
    simp only [div_eq_mul_inv, integral_const_mul, integral_univ_inv_one_add_sq]
  rw [he] at hlim
  have hp := hlim.const_mul (1 / Real.pi)
  have hval : (1 / Real.pi) * (Real.log (positiveLogarithmicSymbol y) * Real.pi) =
      Real.log (positiveLogarithmicSymbol y) := by field_simp
  rwa [hval] at hp

#print axioms tendsto_logarithmic_poisson_boundary

/-- Every affine pullback of the logarithmic symbol is integrable against the unit Poisson kernel. -/
theorem integrable_affine_logarithmic_poisson (x y : ℝ) :
    Integrable (fun u : ℝ => Real.log (positiveLogarithmicSymbol (y + x * u)) /
      (1 + u ^ 2)) := by
  let C : ℝ := 2 + 2 * y ^ 2 + 2 * x ^ 2
  have hC1 : 1 ≤ C := by dsimp only [C]; nlinarith only [sq_nonneg x, sq_nonneg y]
  have hC : 0 < C := zero_lt_one.trans_le hC1
  apply (integrable_logFactorMajorant.const_mul (Real.log C + 1)).mono'
  · exact ((continuous_log_positiveLogarithmicSymbol.comp
      (continuous_const.add (continuous_const.mul continuous_id))).div
      (continuous_const.add (continuous_id.pow 2))
      (fun u => (show 0 < 1 + u ^ 2 by positivity).ne')).aestronglyMeasurable
  · filter_upwards with u
    have hsq : 1 + (y + x * u) ^ 2 ≤ C * (1 + u ^ 2) := by
      dsimp only [C]
      nlinarith only [sq_nonneg (y - x * u), sq_nonneg x, sq_nonneg y, sq_nonneg u,
        mul_nonneg (sq_nonneg y) (sq_nonneg u)]
    have hlog := Real.log_le_log (by positivity : 0 < 1 + (y + x * u) ^ 2) hsq
    rw [Real.log_mul hC.ne' (by positivity : (1 + u ^ 2 : ℝ) ≠ 0)] at hlog
    have hl := (log_positiveLogarithmicSymbol_le _).trans hlog
    have hlog0 := Real.log_nonneg hC1
    have hlu : 0 ≤ Real.log (1 + u ^ 2) := Real.log_nonneg (by nlinarith only [sq_nonneg u])
    rw [Real.norm_of_nonneg (div_nonneg (log_positiveLogarithmicSymbol_nonneg _) (by positivity))]
    calc
      _ ≤ (Real.log C + Real.log (1 + u ^ 2)) / (1 + u ^ 2) :=
        div_le_div_of_nonneg_right hl (by positivity)
      _ ≤ ((Real.log C + 1) * (1 + Real.log (1 + u ^ 2))) / (1 + u ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith only [mul_nonneg hlog0 hlu, hlog0]
      _ = _ := by unfold logFactorMajorant; ring

private def logarithmicPoissonDensity (x y t : ℝ) : ℝ :=
  x * Real.log (positiveLogarithmicSymbol t) / (x ^ 2 + (t - y) ^ 2)

private theorem logarithmicPoissonDensity_affine {x : ℝ} (hx : 0 < x) (y t : ℝ) :
    logarithmicPoissonDensity x y t = x⁻¹ *
      (Real.log (positiveLogarithmicSymbol (y + x * ((t - y) / x))) /
        (1 + ((t - y) / x) ^ 2)) := by
  have he : y + x * ((t - y) / x) = t := by field_simp; ring
  rw [he]
  unfold logarithmicPoissonDensity
  field_simp

private theorem integrable_logarithmicPoissonDensity {x : ℝ} (hx : 0 < x) (y : ℝ) :
    Integrable (logarithmicPoissonDensity x y) := by
  have hg := ((integrable_affine_logarithmic_poisson x y).comp_div hx.ne').comp_sub_right y
  exact (hg.const_mul x⁻¹).congr (Eventually.of_forall fun t =>
    (logarithmicPoissonDensity_affine hx y t).symm)

private theorem integral_logarithmicPoissonDensity {x : ℝ} (hx : 0 < x) (y : ℝ) :
    (∫ t : ℝ, logarithmicPoissonDensity x y t) =
      ∫ u : ℝ, Real.log (positiveLogarithmicSymbol (y + x * u)) / (1 + u ^ 2) := by
  let g : ℝ → ℝ := fun u => Real.log (positiveLogarithmicSymbol (y + x * u)) / (1 + u ^ 2)
  have he : logarithmicPoissonDensity x y = (fun t => x⁻¹ * g ((t - y) / x)) :=
    funext (logarithmicPoissonDensity_affine hx y)
  rw [he, integral_const_mul]
  have hs : (∫ t : ℝ, g ((t - y) / x)) = ∫ t : ℝ, g (t / x) := by
    simpa only [sub_eq_add_neg] using
      integral_add_right_eq_self (μ := volume) (fun t : ℝ => g (t / x)) (-y)
  rw [hs, MeasureTheory.Measure.integral_comp_div g x, abs_of_pos hx, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hx.ne', one_mul]

private theorem integrable_rightLogFactorIntegrand {z : ℂ} (hz : 0 < z.re) :
    Integrable (rightLogFactorIntegrand z) := by
  obtain ⟨B, _, hb⟩ := compact_rightLogFactorIntegrand_bound isCompact_singleton
    (show {z} ⊆ {w : ℂ | 0 < w.re} by simpa)
  exact (integrable_logFactorMajorant.const_mul B).mono'
    (continuous_rightLogFactorIntegrand hz).aestronglyMeasurable
    (Eventually.of_forall fun t => hb z (mem_singleton z) t)

private theorem rightLogFactorIntegrand_re {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    2 * (rightLogFactorIntegrand z t).re =
      logarithmicPoissonDensity z.re z.im t + logarithmicPoissonDensity z.re z.im (-t) := by
  have hp : z + (t : ℂ) * I ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at he
    exact hz.ne' he
  have hm : z - (t : ℂ) * I ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.zero_re] at he
    exact hz.ne' he
  have hs : z / (z ^ 2 + (t : ℂ) ^ 2) =
      (1 / 2 : ℂ) * ((z - (t : ℂ) * I)⁻¹ + (z + (t : ℂ) * I)⁻¹) := by
    field_simp [rightLogFactor_den_ne hz t, hp, hm]
    ring_nf
    rw [Complex.I_sq]
    ring
  have he : rightLogFactorIntegrand z t =
      (Real.log (positiveLogarithmicSymbol t) : ℂ) *
        ((1 / 2 : ℂ) * ((z - (t : ℂ) * I)⁻¹ + (z + (t : ℂ) * I)⁻¹)) := by
    rw [← hs]
    unfold rightLogFactorIntegrand
    ring
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [he, hhalf]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.add_re, Complex.inv_re, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    add_zero, logarithmicPoissonDensity, positiveLogarithmicSymbol, neg_sq]
  ring

private theorem twice_re_integral_rightLogFactorIntegrand {z : ℂ} (hz : 0 < z.re) :
    2 * (∫ t in Ioi (0 : ℝ), rightLogFactorIntegrand z t).re =
      ∫ t : ℝ, logarithmicPoissonDensity z.re z.im t := by
  have hi := (integrable_rightLogFactorIntegrand hz).integrableOn (s := Ioi (0 : ℝ))
  have hf := integrable_logarithmicPoissonDensity hz z.im
  calc
    _ = ∫ t in Ioi (0 : ℝ), 2 * (rightLogFactorIntegrand z t).re := by
      rw [integral_const_mul]
      congr 1
      simpa only using! (integral_re hi).symm
    _ = ∫ t in Ioi (0 : ℝ),
        logarithmicPoissonDensity z.re z.im t + logarithmicPoissonDensity z.re z.im (-t) :=
      integral_congr_ae (Eventually.of_forall (rightLogFactorIntegrand_re hz))
    _ = _ := by
      rw [integral_add hf.integrableOn hf.comp_neg.integrableOn,
        ← integral_eq_add_reflect hf]

/-- The squared modulus is the exponential of the actual Poisson average. -/
theorem complexLogReferenceFactor_norm_sq {z : ℂ} (hz : 0 < z.re) :
    ‖complexLogReferenceFactor z‖ ^ 2 = Real.exp ((1 / Real.pi) * ∫ u : ℝ,
      Real.log (positiveLogarithmicSymbol (z.im + z.re * u)) / (1 + u ^ 2)) := by
  rw [complexLogReferenceFactor_eq_right hz, rightLogReferenceFactor,
    Complex.norm_exp, pow_two, ← Real.exp_add]
  have hc : (1 / (Real.pi : ℂ)) = ((1 / Real.pi : ℝ) : ℂ) := by push_cast; rfl
  rw [hc]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  calc
    _ = (1 / Real.pi) * (2 * (∫ t in Ioi (0 : ℝ), rightLogFactorIntegrand z t).re) := by ring
    _ = _ := by
      rw [twice_re_integral_rightLogFactorIntegrand hz, integral_logarithmicPoissonDensity hz]

/-- Continuity of the slit-plane factor upgrades Poisson boundary reproduction to an identity. -/
theorem complexLogReferenceFactor_imaginary_norm_sq {y : ℝ} (hy : y ≠ 0) :
    ‖complexLogReferenceFactor ((y : ℂ) * I)‖ ^ 2 = positiveLogarithmicSymbol y := by
  have hm : (y : ℂ) * I ∈ slitPlane := Or.inr (by simpa using hy)
  have hc : ContinuousAt complexLogReferenceFactor ((y : ℂ) * I) :=
    differentiableOn_complexLogReferenceFactor.continuousOn.continuousAt
      (Complex.isOpen_slitPlane.mem_nhds hm)
  have hp : ContinuousAt (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) 0 := by fun_prop
  have hpath : Tendsto (fun x : ℝ => (x : ℂ) + (y : ℂ) * I)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds ((y : ℂ) * I)) := by
    simpa only [Complex.ofReal_zero, zero_add] using hp.tendsto.mono_left nhdsWithin_le_nhds
  have hlim1 := ((hc.tendsto.comp hpath).norm).pow 2
  have hlim2 : Tendsto (fun x : ℝ => ‖complexLogReferenceFactor ((x : ℂ) + (y : ℂ) * I)‖ ^ 2)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (positiveLogarithmicSymbol y)) := by
    have he := Real.continuous_exp.continuousAt.tendsto.comp (tendsto_logarithmic_poisson_boundary y)
    rw [Real.exp_log (zero_lt_one.trans_le (one_le_positiveLogarithmicSymbol y))] at he
    apply he.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxr : 0 < ((x : ℂ) + (y : ℂ) * I).re := by simpa using hx
    simpa only [Function.comp_def, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      zero_mul, sub_zero, add_zero, zero_add] using
      (complexLogReferenceFactor_norm_sq hxr).symm
  exact tendsto_nhds_unique hlim1 hlim2

#print axioms complexLogReferenceFactor_norm_sq
#print axioms complexLogReferenceFactor_imaginary_norm_sq

theorem complexLogReferenceFactor_imaginary_mul {y : ℝ} (hy : y ≠ 0) :
    complexLogReferenceFactor ((y : ℂ) * I) * complexLogReferenceFactor (-((y : ℂ) * I)) =
      (positiveLogarithmicSymbol y : ℂ) := by
  have hm : (y : ℂ) * I ∈ slitPlane := Or.inr (by simpa using hy)
  have he : -((y : ℂ) * I) = (starRingEnd ℂ) ((y : ℂ) * I) := by simp
  rw [he, complexLogReferenceFactor_conj hm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    complexLogReferenceFactor_imaginary_norm_sq hy]

/-- The reflection argument avoids the logarithmic cut away from the real axis. -/
theorem one_sub_sq_mem_slitPlane {z : ℂ} (hz : z.im ≠ 0) :
    1 - z ^ 2 ∈ slitPlane := by
  rcases eq_or_ne z.re 0 with hr | hr
  · apply Or.inl
    simp only [Complex.sub_re, Complex.one_re, pow_two, Complex.mul_re, hr,
      zero_mul, zero_sub, sub_neg_eq_add]
    nlinarith only [sq_nonneg z.im]
  · apply Or.inr
    simp only [Complex.sub_im, Complex.one_im, pow_two, Complex.mul_im, zero_sub]
    rw [show -(z.re * z.im + z.im * z.re) = -((2 * z.re) * z.im) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) hr) hz)

private theorem complexLogReferenceFactor_reflection_upper {z : ℂ} (hz : 0 < z.im) :
    complexLogReferenceFactor z * complexLogReferenceFactor (-z) = logarithmicLaplaceSymbol (-z ^ 2) := by
  let U : Set ℂ := {w : ℂ | 0 < w.im}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hf : AnalyticOnNhd ℂ
      (fun w => complexLogReferenceFactor w * complexLogReferenceFactor (-w)) U := by
    apply DifferentiableOn.analyticOnNhd _ hUo
    intro w hw
    have hwm : w ∈ slitPlane := Or.inr (ne_of_gt hw)
    have hwn : -w ∈ slitPlane := Or.inr (by simpa using ne_of_gt hw)
    have hd := differentiableOn_complexLogReferenceFactor.differentiableAt
      (Complex.isOpen_slitPlane.mem_nhds hwm)
    have hdn := differentiableOn_complexLogReferenceFactor.differentiableAt
      (Complex.isOpen_slitPlane.mem_nhds hwn)
    have hneg : DifferentiableAt ℂ (fun v : ℂ => -v) w := by fun_prop
    have hcomp : DifferentiableAt ℂ (fun v => complexLogReferenceFactor (-v)) w := by
      simpa only [Function.comp_def] using! hdn.comp w hneg
    exact (hd.mul hcomp).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (fun w : ℂ => logarithmicLaplaceSymbol (-w ^ 2)) U := by
    apply DifferentiableOn.analyticOnNhd _ hUo
    intro w hw
    have hslit : 1 + -w ^ 2 ∈ slitPlane := by
      simpa only [sub_eq_add_neg] using one_sub_sq_mem_slitPlane (ne_of_gt hw)
    have hp : DifferentiableAt ℂ (fun v : ℂ => 1 + -v ^ 2) w := by fun_prop
    have hl : DifferentiableAt ℂ (fun v : ℂ => Complex.log (1 + -v ^ 2)) w := by
      simpa only [Function.comp_def] using! (Complex.hasDerivAt_log hslit).differentiableAt.comp w hp
    exact ((hl.const_mul ((1 / 2 : ℝ) : ℂ)).const_add (1 : ℂ)).differentiableWithinAt
  have hfreq : ∃ᶠ w in 𝓝[≠] I,
      complexLogReferenceFactor w * complexLogReferenceFactor (-w) = logarithmicLaplaceSymbol (-w ^ 2) := by
    let u : ℕ → ℂ := fun k => ((1 + 1 / ((k : ℝ) + 1) : ℝ) : ℂ) * I
    have hlim : Tendsto u atTop (𝓝[≠] I) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
        rw [add_zero] at h
        have hc := ((Complex.continuous_ofReal.tendsto 1).comp h).mul_const I
        simpa only [u, Function.comp_def, Complex.ofReal_one, one_mul] using! hc
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, u]
        intro h
        have he : ((1 + 1 / ((k : ℝ) + 1) : ℝ) : ℂ) = 1 :=
          mul_right_cancel₀ Complex.I_ne_zero (by simpa only [one_mul] using h)
        have heR : (1 + 1 / ((k : ℝ) + 1) : ℝ) = 1 := by exact_mod_cast he
        have hp : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith only [heR, hp]
    refine hlim.frequently (Frequently.of_forall fun k => ?_)
    let y : ℝ := 1 + 1 / ((k : ℝ) + 1)
    have hy : 0 < y := by dsimp only [y]; positivity
    have hs : -((y : ℂ) * I) ^ 2 = (y : ℂ) ^ 2 := by
      rw [mul_pow, Complex.I_sq]
      ring
    change complexLogReferenceFactor ((y : ℂ) * I) * complexLogReferenceFactor (-((y : ℂ) * I)) = _
    rw [complexLogReferenceFactor_imaginary_mul hy.ne', hs, logarithmicLaplaceSymbol_ofReal_sq]
  exact hf.eqOn_of_preconnected_of_frequently_eq hg (convex_halfSpace_im_gt 0).isPreconnected
    (by simp [U]) hfreq hz

/-- The logarithmic factorization identity holds throughout both nonreal half-planes. -/
theorem complexLogReferenceFactor_reflection {z : ℂ} (hz : z.im ≠ 0) :
    complexLogReferenceFactor z * complexLogReferenceFactor (-z) =
      1 + ((1 / 2 : ℝ) : ℂ) * Complex.log (1 - z ^ 2) := by
  suffices h : complexLogReferenceFactor z * complexLogReferenceFactor (-z) =
      logarithmicLaplaceSymbol (-z ^ 2) by
    simpa only [logarithmicLaplaceSymbol, sub_eq_add_neg] using h
  rcases lt_or_gt_of_ne hz with hm | hp
  · have hc : 0 < ((starRingEnd ℂ) z).im := by simpa only [Complex.conj_im] using neg_pos.mpr hm
    have hu := complexLogReferenceFactor_reflection_upper hc
    have hzm : z ∈ slitPlane := Or.inr hz
    have hzn : -z ∈ slitPlane := Or.inr (by simpa using hz)
    have he : -((starRingEnd ℂ) z) = (starRingEnd ℂ) (-z) := by simp
    have hleft : complexLogReferenceFactor ((starRingEnd ℂ) z) *
        complexLogReferenceFactor (-((starRingEnd ℂ) z)) =
          (starRingEnd ℂ) (complexLogReferenceFactor z * complexLogReferenceFactor (-z)) := by
      rw [he, complexLogReferenceFactor_conj hzm, complexLogReferenceFactor_conj hzn, map_mul]
    have hright : logarithmicLaplaceSymbol (-((starRingEnd ℂ) z) ^ 2) =
        (starRingEnd ℂ) (logarithmicLaplaceSymbol (-z ^ 2)) := by
      have harg : 1 + -((starRingEnd ℂ) z) ^ 2 = (starRingEnd ℂ) (1 + -z ^ 2) := by simp
      have hs : 1 + -z ^ 2 ∈ slitPlane := by
        simpa only [sub_eq_add_neg] using one_sub_sq_mem_slitPlane hz
      unfold logarithmicLaplaceSymbol
      rw [harg, Complex.log_conj _ (Complex.mem_slitPlane_iff_arg.mp hs).1]
      simp only [map_add, map_mul, map_one, Complex.conj_ofReal]
    rw [hleft, hright] at hu
    have h := congrArg (starRingEnd ℂ) hu
    simpa only [starRingEnd_self_apply] using h
  · exact complexLogReferenceFactor_reflection_upper hp

#print axioms complexLogReferenceFactor_reflection


end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
