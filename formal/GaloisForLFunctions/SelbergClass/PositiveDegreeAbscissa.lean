import GaloisForLFunctions.SelbergClass.QuarterLineGammaRatio
import GaloisForLFunctions.SelbergClass.DirichletVerticalDecay

/-!
# Positive degree excludes absolute convergence at zero

Absolute convergence at zero identifies the Dirichlet series with the Selberg
continuation in the positive half-plane. The functional equation and the
quarter-line Gamma ratio force vertical decay on a line of absolute convergence,
contradicting the nonzero coefficient sequence.
-/

noncomputable section
open Complex Filter Topology Set MeasureTheory
open RHTower

namespace GaloisForLFunctions.SelbergClass

private theorem analyticOnNhd_lSeries_of_summable_zero (F : ExtendedSelbergClass)
    (hsum : LSeriesSummable F.coeff 0) :
    AnalyticOnNhd ℂ (LSeries F.coeff) {s : ℂ | 0 < s.re} := by
  have hd : DifferentiableOn ℂ (LSeries F.coeff) {s : ℂ | 0 < s.re} := by
    intro s hs
    have habs : LSeries.abscissaOfAbsConv F.coeff < s.re :=
      lt_of_le_of_lt hsum.abscissaOfAbsConv_le (by exact_mod_cast hs)
    exact (LSeries_hasDerivAt habs).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

/-- Absolute convergence at zero extends the Dirichlet representation to every
positive real part away from the displayed pole. -/
theorem lSeries_eq_value_of_summable_zero (F : ExtendedSelbergClass)
    (hsum : LSeriesSummable F.coeff 0) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    LSeries F.coeff s = F s := by
  have hL : AnalyticOnNhd ℂ
      (fun z => LSeries F.coeff z * (z - 1) ^ F.continuation.poleOrder)
      {z : ℂ | 0 < z.re} := by
    intro z hz
    exact (analyticOnNhd_lSeries_of_summable_zero F hsum z hz).mul (by fun_prop)
  have hR : AnalyticOnNhd ℂ F.continuation.regularized {z : ℂ | 0 < z.re} :=
    fun z _ => F.continuation.regularized.analytic z (mem_univ z)
  have hnear : (fun z => LSeries F.coeff z * (z - 1) ^ F.continuation.poleOrder)
      =ᶠ[𝓝 (2 : ℂ)] F.continuation.regularized := by
    have hU : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hU.mem_nhds (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    have hz1 : z ≠ 1 := by intro he; simp [he] at hz
    have hv := F.lSeries_eq_value z hz
    exact (eq_div_iff (pow_ne_zero _ (sub_ne_zero.mpr hz1))).mp hv
  have heq := hL.eqOn_of_preconnected_of_eventuallyEq hR
    (convex_halfSpace_re_gt 0).isPreconnected
    (by norm_num : (2 : ℂ) ∈ {z : ℂ | 0 < z.re}) hnear hs
  exact (eq_div_iff (pow_ne_zero _ (sub_ne_zero.mpr hs1))).mpr heq

private theorem norm_value_quarter_le (F : ExtendedSelbergClass)
    (hsum : LSeriesSummable F.coeff 0) (t : ℝ) :
    ‖F ((1 / 4 : ℂ) + (t : ℂ) * I)‖ ≤ ∑' n, ‖LSeries.term F.coeff 0 n‖ := by
  have hs : 0 < ((1 / 4 : ℂ) + (t : ℂ) * I).re := by norm_num
  have hs1 : (1 / 4 : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro h; have := congrArg Complex.re h; norm_num at this
  rw [← lSeries_eq_value_of_summable_zero F hsum hs hs1]
  have ht := hsum.of_re_le_re (s' := (1 / 4 : ℂ) + (t : ℂ) * I) (by norm_num)
  exact (norm_tsum_le_tsum_norm ht.norm).trans
    (ht.norm.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re F.coeff
      (s := 0) (by norm_num) n) hsum.norm)

private theorem norm_value_three_quarters (F : ExtendedSelbergClass) (t : ℝ) :
    ‖F ((3 / 4 : ℂ) + (t : ℂ) * I)‖ =
      (‖F.gammaData.gammaFactor ((1 / 4 : ℂ) + (t : ℂ) * I)‖ /
        ‖F.gammaData.gammaFactor ((3 / 4 : ℂ) + (t : ℂ) * I)‖) *
        ‖F ((1 / 4 : ℂ) + (t : ℂ) * I)‖ := by
  have hreflect : 1 - star ((1 / 4 : ℂ) + (t : ℂ) * I) =
      (3 / 4 : ℂ) + (t : ℂ) * I := by
    apply Complex.ext <;> simp
    ring
  have han : ∀ σ : ℝ, 0 < σ → σ ≠ 1 →
      AnalyticAt ℂ (selbergCompletedValue F.gammaData F.continuation)
        ((σ : ℂ) + (t : ℂ) * I) := by
    intro σ hσ hσ1
    apply (gammaFactor_analyticAt_of_re_pos F.gammaData (by simpa using hσ)).mul
    apply F.continuation.analyticAt_value_of_ne_one
    intro h
    apply hσ1
    simpa using congrArg Complex.re h
  have hfe := F.completedFE_eq_of_analytic_pair (s := (1 / 4 : ℂ) + (t : ℂ) * I)
    (by convert han (1 / 4) (by norm_num) (by norm_num) using 1 <;> push_cast <;> rfl)
    (by rw [hreflect]; convert han (3 / 4) (by norm_num) (by norm_num) using 1 <;> push_cast <;> rfl)
  have hn := congrArg norm hfe
  simp only [selbergCompletedValue, selbergConjugateReflection, hreflect, norm_mul,
    norm_star, F.gammaData.rootNumber_norm, one_mul] at hn
  change ‖F.gammaData.gammaFactor ((1 / 4 : ℂ) + (t : ℂ) * I)‖ *
      ‖F ((1 / 4 : ℂ) + (t : ℂ) * I)‖ =
    ‖F.gammaData.gammaFactor ((3 / 4 : ℂ) + (t : ℂ) * I)‖ *
      ‖F ((3 / 4 : ℂ) + (t : ℂ) * I)‖ at hn
  have hg : ‖F.gammaData.gammaFactor ((3 / 4 : ℂ) + (t : ℂ) * I)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gammaFactor_ne_zero_of_re_pos F.gammaData (by norm_num))
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hg).mpr
  nlinarith only [hn]

/-- Every extended Selberg function with absolute convergence at zero has degree zero. -/
theorem degree_eq_zero_of_summable_zero (F : ExtendedSelbergClass)
    (hsum : LSeriesSummable F.coeff 0) : F.gammaData.degree = 0 := by
  by_contra hne
  have hd : 0 < F.gammaData.degree := lt_of_le_of_ne F.gammaData.degree_nonneg (Ne.symm hne)
  let C : ℝ := ∑' n, ‖LSeries.term F.coeff 0 n‖
  have hlim := (tendsto_gammaFactor_quarter_ratio F.gammaData hd).mul_const C
  rw [zero_mul] at hlim
  have hnorm : Tendsto (fun t : ℝ => ‖F ((3 / 4 : ℂ) + (t : ℂ) * I)‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
    intro t
    rw [norm_value_three_quarters]
    exact mul_le_mul_of_nonneg_left (norm_value_quarter_le F hsum t)
      (div_nonneg (norm_nonneg _) (norm_nonneg _))
  have hval : Tendsto (fun t : ℝ => F ((3 / 4 : ℂ) + (t : ℂ) * I)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have heq : ∀ t : ℝ, LSeries F.coeff (((3 / 4 : ℝ) : ℂ) + (t : ℂ) * I) =
      F ((3 / 4 : ℂ) + (t : ℂ) * I) := by
    intro t
    push_cast
    apply lSeries_eq_value_of_summable_zero F hsum (by norm_num)
    intro h; have := congrArg Complex.re h; norm_num at this
  have hzero := coeff_eq_zero_of_lSeries_vertical_tendsto_zero
    (hsum.of_re_le_re (s' := ((3 / 4 : ℝ) : ℂ)) (by norm_num))
    (hval.congr fun t => (heq t).symm)
  apply F.coeff_ne_zero
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact hzero n hn

end GaloisForLFunctions.SelbergClass
