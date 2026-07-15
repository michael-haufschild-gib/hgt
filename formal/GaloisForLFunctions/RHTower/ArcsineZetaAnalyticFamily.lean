import GaloisForLFunctions.HTGeometry.ArcsineEndpointSeries
import GaloisForLFunctions.RHTower.ArcsineZetaTransform
import GaloisForLFunctions.RHTower.SqrtCarrierCertificate

/-!
# The analytic arcsine Dirichlet transform

For `Re s > 0`, the Dirichlet series with coefficients `arcsin (1 / n)` converges locally
normally and equals the locally normally convergent superposition
`∑ j, c_j ζ(s + 2j + 1)`.  Absolute convergence of the underlying double series makes the
identity a genuine Tonelli/Fubini theorem, including the endpoint contribution at `n = 1`.
Differentiation at `s = 1` is justified both on the Dirichlet and shifted-zeta sides.
-/

namespace GaloisForLFunctions

open Complex Filter Function
open scoped Topology

noncomputable def arcsineDirichletCoefficient (n : ℕ) : ℂ :=
  (Real.arcsin (1 / (n : ℝ)) : ℂ)

noncomputable def arcsineDirichletTransform (s : ℂ) : ℂ :=
  LSeries arcsineDirichletCoefficient s

theorem norm_arcsineDirichletCoefficient_le (n : ℕ) (hn : n ≠ 0) :
    ‖arcsineDirichletCoefficient n‖ ≤
      Real.pi / 2 * (n : ℝ) ^ (-1 : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : 1 / (n : ℝ) ≤ 1 := (div_le_one hnpos).2 (by exact_mod_cast Nat.pos_of_ne_zero hn)
  rw [arcsineDirichletCoefficient, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.arcsin_nonneg.mpr (by positivity)), Real.rpow_neg_one]
  simpa [one_div] using arcsin_le_pi_half_mul (1 / (n : ℝ)) (by positivity) hn1

theorem abscissaOfAbsConv_arcsineDirichletCoefficient_le_zero :
    LSeries.abscissaOfAbsConv arcsineDirichletCoefficient ≤ (0 : ℝ) := by
  have h := LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow
    (x := (-1 : ℝ)) (f := arcsineDirichletCoefficient)
    ⟨Real.pi / 2, norm_arcsineDirichletCoefficient_le⟩
  calc
    LSeries.abscissaOfAbsConv arcsineDirichletCoefficient ≤ ((-1 : ℝ) : EReal) + 1 := h
    _ = 0 := by
      change ((-1 : ℝ) : EReal) + ((1 : ℝ) : EReal) = ((0 : ℝ) : EReal)
      rw [← EReal.coe_add]
      norm_num

theorem analyticOnNhd_arcsineDirichletTransform :
    AnalyticOnNhd ℂ arcsineDirichletTransform {s : ℂ | 0 < s.re} := by
  intro s hs
  unfold arcsineDirichletTransform
  apply LSeries_analyticOnNhd _ s
  exact abscissaOfAbsConv_arcsineDirichletCoefficient_le_zero.trans_lt
    (by exact_mod_cast hs)

noncomputable def arcsineDirichletTerm (n : ℕ) (s : ℂ) : ℂ :=
  LSeries.term arcsineDirichletCoefficient s n

/-- The arcsine Dirichlet series converges locally normally on `Re s > 0`. -/
theorem summableLocallyUniformlyOn_arcsineDirichletTerm :
    SummableLocallyUniformlyOn (fun n : ℕ => arcsineDirichletTerm n)
      {s : ℂ | 0 < s.re} := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro s hs
  change 0 < s.re at hs
  let r : ℝ := s.re / 2
  have hr : 0 < r := by dsimp only [r]; linarith
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + r)) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  have hmajor : Summable (fun n : ℕ => Real.pi / 2 *
      (1 / (n : ℝ) ^ (1 + r))) := hp.mul_left _
  refine ⟨Metric.ball s r,
    mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self hr)), ?_⟩
  apply HasSumUniformlyOn.of_norm_le_summable hmajor
  intro n x hx
  have hxnorm : ‖x - s‖ < r := by
    simpa [dist_eq_norm] using Metric.mem_ball.mp hx
  have hxre : r < x.re := by
    have hre := Complex.abs_re_le_norm (x - s)
    rw [Complex.sub_re] at hre
    have hreLower := (abs_le.mp hre).1
    have hstrict := lt_of_lt_of_le (neg_lt_neg hxnorm) hreLower
    dsimp only [r] at hstrict ⊢
    linarith
  rcases n.eq_zero_or_pos with rfl | hn
  · norm_num [arcsineDirichletTerm, LSeries.term_zero,
      Real.zero_rpow (by linarith : 1 + r ≠ 0)]
  · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [arcsineDirichletTerm, LSeries.term_of_ne_zero hn0, norm_div,
      Complex.norm_natCast_cpow_of_pos hn]
    calc
      ‖arcsineDirichletCoefficient n‖ / (n : ℝ) ^ x.re ≤
          (Real.pi / 2 * (n : ℝ) ^ (-1 : ℝ)) / (n : ℝ) ^ x.re := by
        exact div_le_div_of_nonneg_right (norm_arcsineDirichletCoefficient_le n hn0)
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = Real.pi / 2 * (1 / (n : ℝ) ^ (1 + x.re)) := by
        simp only [div_eq_mul_inv, ← Real.rpow_neg hnreal.le]
        simp only [one_mul]
        rw [show Real.pi * (2 : ℝ)⁻¹ * (n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (-x.re) =
          Real.pi * (2 : ℝ)⁻¹ * ((n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (-x.re)) by ring,
          ← Real.rpow_add hnreal]
        congr 2
        ring
      _ ≤ Real.pi / 2 * (1 / (n : ℝ) ^ (1 + r)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hnreal _)
        exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)

noncomputable def arcsineZetaTerm (j : ℕ) (s : ℂ) : ℂ :=
  (arcsinCoeff j : ℂ) * riemannZeta (s + ((2 * j + 1 : ℕ) : ℂ))

noncomputable def arcsineZetaSuperposition (s : ℂ) : ℂ :=
  ∑' j : ℕ, arcsineZetaTerm j s

theorem differentiableAt_arcsineZetaTerm {s : ℂ} (hs : 0 < s.re) (j : ℕ) :
    DifferentiableAt ℂ (arcsineZetaTerm j) s := by
  unfold arcsineZetaTerm
  apply DifferentiableAt.const_mul
  apply (differentiableAt_riemannZeta ?_).comp s (differentiableAt_id.add_const _)
  intro h
  have hre := congrArg Complex.re h
  simp only [id_eq, Complex.add_re, Complex.natCast_re, Complex.one_re] at hre
  have hj : (1 : ℝ) ≤ (2 * j + 1 : ℕ) := by exact_mod_cast (show 1 ≤ 2 * j + 1 by omega)
  linarith

theorem deriv_arcsineZetaTerm {s : ℂ} (hs : 0 < s.re) (j : ℕ) :
    deriv (arcsineZetaTerm j) s = (arcsinCoeff j : ℂ) *
      deriv riemannZeta (s + ((2 * j + 1 : ℕ) : ℂ)) := by
  have hne : s + ((2 * j + 1 : ℕ) : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re] at hre
    have hj : (1 : ℝ) ≤ (2 * j + 1 : ℕ) := by exact_mod_cast (show 1 ≤ 2 * j + 1 by omega)
    linarith
  have hinner := (differentiableAt_riemannZeta hne).hasDerivAt.comp s
    ((hasDerivAt_id s).add_const ((2 * j + 1 : ℕ) : ℂ))
  unfold arcsineZetaTerm
  simpa [Function.comp_def] using (hinner.const_mul (arcsinCoeff j : ℂ)).deriv

/-- The shifted-zeta superposition converges locally normally on `Re s > 0`. -/
theorem summableLocallyUniformlyOn_arcsineZetaTerm :
    SummableLocallyUniformlyOn (fun j : ℕ => arcsineZetaTerm j)
      {s : ℂ | 0 < s.re} := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro s hs
  change 0 < s.re at hs
  let r : ℝ := s.re / 2
  have hr : 0 < r := by dsimp only [r]; linarith
  have hmajor : Summable (fun j : ℕ => arcsinCoeff j * (1 + 1 / r)) :=
    summable_arcsinCoeff.mul_right _
  refine ⟨Metric.ball s r,
    mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self hr)), ?_⟩
  apply HasSumUniformlyOn.of_norm_le_summable hmajor
  intro j x hx
  have hxnorm : ‖x - s‖ < r := by
    simpa [dist_eq_norm] using Metric.mem_ball.mp hx
  have hxre : r < x.re := by
    have hre := Complex.abs_re_le_norm (x - s)
    rw [Complex.sub_re] at hre
    have hreLower := (abs_le.mp hre).1
    have hstrict := lt_of_lt_of_le (neg_lt_neg hxnorm) hreLower
    dsimp only [r] at hstrict ⊢
    linarith
  have harg : 1 + r ≤ (x + ((2 * j + 1 : ℕ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    have hj : (1 : ℝ) ≤ (2 * j + 1 : ℕ) := by exact_mod_cast (show 1 ≤ 2 * j + 1 by omega)
    linarith
  rw [arcsineZetaTerm, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (arcsinCoeff_pos j)]
  exact mul_le_mul_of_nonneg_left (RHTower.norm_riemannZeta_le hr harg)
    (arcsinCoeff_nonneg j)

theorem differentiableOn_arcsineZetaSuperposition :
    DifferentiableOn ℂ arcsineZetaSuperposition {s : ℂ | 0 < s.re} := by
  apply SummableLocallyUniformlyOn.differentiableOn
    (isOpen_lt continuous_const Complex.continuous_re)
    summableLocallyUniformlyOn_arcsineZetaTerm
  intro j s hs
  exact differentiableAt_arcsineZetaTerm hs j

noncomputable def arcsineZetaDoubleTerm (s : ℂ) (j k : ℕ) : ℂ :=
  (arcsinCoeff j : ℂ) *
    LSeries.term (1 : ℕ → ℂ) (s + ((2 * j + 1 : ℕ) : ℂ)) k

/-- Absolute summability of the double series underlying the analytic transform. -/
theorem summable_arcsineZetaDoubleTerm {s : ℂ} (hs : 0 < s.re) :
    Summable (Function.uncurry (arcsineZetaDoubleTerm s)) := by
  let eps : ℝ := s.re / 2
  have heps : 0 < eps := by dsimp only [eps]; linarith
  let q : ℕ → ℝ := fun k => 1 / (k : ℝ) ^ (1 + eps)
  have hq : Summable q := by
    apply Real.summable_one_div_nat_rpow.mpr
    dsimp only [q]
    linarith
  have hmajor : Summable (fun p : ℕ × ℕ => arcsinCoeff p.1 * q p.2) := by
    rw [summable_prod_of_nonneg (fun p => mul_nonneg (arcsinCoeff_nonneg p.1) (by
      dsimp only [q]; positivity))]
    constructor
    · intro j
      exact hq.mul_left (arcsinCoeff j)
    · have houter := summable_arcsinCoeff.mul_right (∑' k : ℕ, q k)
      apply houter.congr
      intro j
      rw [← tsum_mul_left]
  apply hmajor.of_norm_bounded
  rintro ⟨j, k⟩
  rcases k.eq_zero_or_pos with rfl | hk
  · norm_num [arcsineZetaDoubleTerm, LSeries.term_zero, q,
      Real.zero_rpow (by linarith : 1 + eps ≠ 0)]
  · have hk0 : k ≠ 0 := Nat.ne_of_gt hk
    have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hexp : 1 + eps ≤ (s + ((2 * j + 1 : ℕ) : ℂ)).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      have hj : (1 : ℝ) ≤ (2 * j + 1 : ℕ) := by exact_mod_cast (show 1 ≤ 2 * j + 1 by omega)
      dsimp only [eps]
      linarith
    change ‖arcsineZetaDoubleTerm s j k‖ ≤ arcsinCoeff j * q k
    rw [arcsineZetaDoubleTerm, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_pos (arcsinCoeff_pos j), LSeries.term_of_ne_zero hk0,
      Pi.one_apply, norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hk]
    apply mul_le_mul_of_nonneg_left _ (arcsinCoeff_nonneg j)
    apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hkreal _)
    exact Real.rpow_le_rpow_of_exponent_le hk1 hexp

theorem arcsineZetaDoubleTerm_hasSum_column (s : ℂ) (k : ℕ) :
    HasSum (fun j : ℕ => arcsineZetaDoubleTerm s j k)
      (LSeries.term arcsineDirichletCoefficient s k) := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp [arcsineZetaDoubleTerm, LSeries.term_zero]
  · have hk0 : k ≠ 0 := Nat.ne_of_gt hk
    have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
    have hk1 : 1 / (k : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact_mod_cast hk
    have hsreal := arcsin_hasSum_closed (u := 1 / (k : ℝ)) (by
      rw [abs_of_nonneg (by positivity)]
      exact hk1)
    have hscomp : HasSum
        (fun j : ℕ => ((arcsinCoeff j * (1 / (k : ℝ)) ^ (2 * j + 1) : ℝ) : ℂ))
        (Real.arcsin (1 / (k : ℝ)) : ℂ) := Complex.hasSum_ofReal.mpr hsreal
    have hmul := hscomp.mul_right (1 / (k : ℂ) ^ s)
    have hval : (Real.arcsin (1 / (k : ℝ)) : ℂ) * (1 / (k : ℂ) ^ s) =
        LSeries.term arcsineDirichletCoefficient s k := by
      rw [LSeries.term_of_ne_zero hk0, arcsineDirichletCoefficient, one_div]
      ring
    rw [← hval]
    apply HasSum.congr_fun hmul
    intro j
    rw [arcsineZetaDoubleTerm, LSeries.term_of_ne_zero hk0,
      Pi.one_apply, Complex.cpow_add _ _ (by exact_mod_cast hk0),
      Complex.cpow_natCast]
    push_cast
    field_simp
    ring

theorem arcsineZetaDoubleTerm_hasSum_row {s : ℂ} (hs : 0 < s.re) (j : ℕ) :
    HasSum (fun k : ℕ => arcsineZetaDoubleTerm s j k) (arcsineZetaTerm j s) := by
  have harg : 1 < (s + ((2 * j + 1 : ℕ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    have hj : (1 : ℝ) ≤ (2 * j + 1 : ℕ) := by exact_mod_cast (show 1 ≤ 2 * j + 1 by omega)
    linarith
  have h := (LSeriesHasSum_one harg).mul_left (arcsinCoeff j : ℂ)
  simpa [arcsineZetaDoubleTerm, arcsineZetaTerm] using h

/-- **Analytic arcsine/zeta superposition law.** -/
theorem arcsineDirichletTransform_eq_arcsineZetaSuperposition {s : ℂ} (hs : 0 < s.re) :
    arcsineDirichletTransform s = arcsineZetaSuperposition s := by
  have hdouble := summable_arcsineZetaDoubleTerm hs
  calc
    arcsineDirichletTransform s =
        ∑' k : ℕ, ∑' j : ℕ, arcsineZetaDoubleTerm s j k := by
      unfold arcsineDirichletTransform LSeries
      apply tsum_congr
      intro k
      exact (arcsineZetaDoubleTerm_hasSum_column s k).tsum_eq.symm
    _ = ∑' j : ℕ, ∑' k : ℕ, arcsineZetaDoubleTerm s j k := by
      exact Summable.tsum_comm hdouble
    _ = arcsineZetaSuperposition s := by
      unfold arcsineZetaSuperposition
      apply tsum_congr
      intro j
      exact (arcsineZetaDoubleTerm_hasSum_row hs j).tsum_eq

theorem analyticOnNhd_arcsineZetaSuperposition :
    AnalyticOnNhd ℂ arcsineZetaSuperposition {s : ℂ | 0 < s.re} :=
  differentiableOn_arcsineZetaSuperposition.analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

theorem deriv_arcsineDirichletTransform_one :
    deriv arcsineDirichletTransform 1 =
      -((∑' k : ℕ, Real.log k / k * Real.arcsin (1 / (k : ℝ)) : ℝ) : ℂ) := by
  have habs : LSeries.abscissaOfAbsConv arcsineDirichletCoefficient <
      (((1 : ℂ).re : ℝ) : EReal) :=
    abscissaOfAbsConv_arcsineDirichletCoefficient_le_zero.trans_lt (by norm_num)
  unfold arcsineDirichletTransform
  rw [LSeries_deriv habs]
  congr 1
  unfold LSeries
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro k
  rw [LSeries.term_def]
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, if_false, LSeries.logMul, arcsineDirichletCoefficient]
    have hlog : Complex.log (k : ℂ) = ((Real.log k : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast k]
      exact (Complex.ofReal_log (Nat.cast_nonneg k)).symm
    rw [hlog, Complex.cpow_one]
    push_cast
    ring

theorem neg_deriv_arcsineDirichletTransform_one :
    -deriv arcsineDirichletTransform 1 =
      ((∑' k : ℕ, Real.log k / k * Real.arcsin (1 / (k : ℝ)) : ℝ) : ℂ) := by
  rw [deriv_arcsineDirichletTransform_one]
  ring

/-- Termwise differentiation of the shifted-zeta superposition at `s = 1`. -/
theorem hasSum_even_zeta_derivative_arcsineSpectrum :
    HasSum (fun j : ℕ => (arcsinCoeff j : ℂ) *
      deriv riemannZeta (((2 * j + 2 : ℕ) : ℝ) : ℂ))
      (deriv arcsineZetaSuperposition 1) := by
  let U : Set ℂ := Metric.ball 1 (1 / 2 : ℝ)
  let u : ℕ → ℝ := fun j => 3 * arcsinCoeff j
  have hu : Summable u := summable_arcsinCoeff.mul_left 3
  have hU : IsOpen U := Metric.isOpen_ball
  have hdiff : ∀ j : ℕ, DifferentiableOn ℂ (arcsineZetaTerm j) U := by
    intro j w hw
    have hwre : 0 < w.re := by
      have hnorm : ‖w - 1‖ < (1 / 2 : ℝ) := by
        simpa [U, dist_eq_norm] using Metric.mem_ball.mp hw
      have hre := Complex.abs_re_le_norm (w - 1)
      rw [Complex.sub_re, Complex.one_re] at hre
      have hlower := (abs_le.mp hre).1
      linarith
    exact (differentiableAt_arcsineZetaTerm hwre j).differentiableWithinAt
  have hbound : ∀ (j : ℕ) (w : ℂ), w ∈ U → ‖arcsineZetaTerm j w‖ ≤ u j := by
    intro j w hw
    have hnorm : ‖w - 1‖ < (1 / 2 : ℝ) := by
      simpa [U, dist_eq_norm] using Metric.mem_ball.mp hw
    have hre := Complex.abs_re_le_norm (w - 1)
    rw [Complex.sub_re, Complex.one_re] at hre
    have hlower := (abs_le.mp hre).1
    have hwre : 1 / 2 < w.re := by linarith
    have harg : 1 + (1 / 2 : ℝ) ≤ (w + ((2 * j + 1 : ℕ) : ℂ)).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      have hj : (1 : ℝ) ≤ (2 * j + 1 : ℕ) := by
        exact_mod_cast (show 1 ≤ 2 * j + 1 by omega)
      linarith
    rw [arcsineZetaTerm, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_pos (arcsinCoeff_pos j)]
    have hz := RHTower.norm_riemannZeta_le (by norm_num : (0 : ℝ) < 1 / 2) harg
    dsimp only [u]
    norm_num at hz ⊢
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hz (arcsinCoeff_nonneg j)
  have hzmem : (1 : ℂ) ∈ U := by simp [U]
  have hsum := Complex.hasSum_deriv_of_summable_norm hu hdiff hU hbound hzmem
  apply HasSum.congr_fun hsum
  intro j
  rw [deriv_arcsineZetaTerm (by norm_num : (0 : ℝ) < (1 : ℂ).re)]
  congr 2
  push_cast
  ring

theorem deriv_arcsineDirichletTransform_eq_deriv_arcsineZetaSuperposition_one :
    deriv arcsineDirichletTransform 1 = deriv arcsineZetaSuperposition 1 := by
  have hmem : (1 : ℂ) ∈ {s : ℂ | 0 < s.re} := by norm_num
  have heq : arcsineDirichletTransform =ᶠ[𝓝 (1 : ℂ)] arcsineZetaSuperposition := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem] with s hs
    exact arcsineDirichletTransform_eq_arcsineZetaSuperposition hs
  exact heq.deriv_eq

/-- Differentiating the analytic family at `s = 1` recovers the even-zeta-derivative spectrum. -/
theorem neg_deriv_arcsineDirichletTransform_eq_even_zeta_derivative_spectrum :
    -deriv arcsineDirichletTransform 1 =
      -(∑' j : ℕ, (arcsinCoeff j : ℂ) *
        deriv riemannZeta (((2 * j + 2 : ℕ) : ℝ) : ℂ)) := by
  rw [deriv_arcsineDirichletTransform_eq_deriv_arcsineZetaSuperposition_one,
    ← hasSum_even_zeta_derivative_arcsineSpectrum.tsum_eq]

end GaloisForLFunctions
