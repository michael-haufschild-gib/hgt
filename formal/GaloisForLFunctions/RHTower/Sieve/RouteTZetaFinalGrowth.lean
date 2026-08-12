import GaloisForLFunctions.RHTower.Sieve.RouteTZetaCanonicalGrowth
import GaloisForLFunctions.RHTower.Sieve.RouteTZetaDepth
import GaloisForLFunctions.RHTower.Sieve.ZetaLineIndexBridge
import GaloisForLFunctions.RHTower.Sieve.DirichletSigmaHeadSimplify

/-!
# Closed canonical Route-T zeta growth

The explicit tenth-power height threshold removes the last receiver-depth premise from the
canonical left-edge estimate.  The remaining Euler--Maclaurin terms are bounded uniformly at the
cubic truncation.
-/

namespace RHTower.Sieve

open Complex

noncomputable section

/-- **Premise-free parameter selection.**  Above one explicit binary-height threshold, every
Route-T receiver and truncation parameter in the canonical left-edge zeta bound is certified. -/
theorem norm_riemannZeta_le_routeT_canonical_large
    {t : ℝ} (ht8 : 8 * Real.pi ≤ t)
    (hlarge : routeTDepthRootThreshold ^ 10 ≤ routeTBinaryHeight t) :
    ‖riemannZeta ((routeTStripAbscissa (routeTGlobalShell t) : ℂ) +
        Complex.I * (t : ℂ))‖ ≤
      2 + (routeTStripDenominator * (routeTGlobalShell t + 1) ^ 9 : ℕ) +
        (routeTGlobalBlocks t : ℝ) * 6912 +
      (((2 ^ topExponent t : ℕ) : ℝ) ^
          (1 - routeTStripAbscissa (routeTGlobalShell t))) /
        ‖(routeTStripAbscissa (routeTGlobalShell t) : ℂ) +
          Complex.I * (t : ℂ) - 1‖ +
      ‖(routeTStripAbscissa (routeTGlobalShell t) : ℂ) +
          Complex.I * (t : ℂ)‖ *
        ((((2 ^ topExponent t : ℕ) : ℝ) ^
          (-routeTStripAbscissa (routeTGlobalShell t))) /
            routeTStripAbscissa (routeTGlobalShell t)) := by
  apply norm_riemannZeta_le_routeT_canonical ht8
  exact routeTCanonicalDepth (by
    have hpi := Real.pi_gt_three
    nlinarith) hlarge

/-- At the cubic truncation, both continuation terms are absolutely bounded throughout the
near-one half-strip.  This estimate is independent of Route T. -/
theorem routeT_cubic_truncation_tails_le_nine
    {t σ : ℝ} (ht8 : 8 * Real.pi ≤ t) (htlarge : 100000 ≤ t)
    (hσhalf : 1 / 2 ≤ σ) (hσone : σ ≤ 1)
    (hthird : 1 - σ ≤ (1 : ℝ) / 3) :
    (((2 ^ topExponent t : ℕ) : ℝ) ^ (1 - σ)) /
        ‖(σ : ℂ) + Complex.I * (t : ℂ) - 1‖ +
      ‖(σ : ℂ) + Complex.I * (t : ℂ)‖ *
        ((((2 ^ topExponent t : ℕ) : ℝ) ^ (-σ)) / σ) ≤ 9 := by
  let N : ℝ := ((2 ^ topExponent t : ℕ) : ℝ)
  let w : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have ht0 : 0 < t := by linarith
  have hσ0 : 0 < σ := by linarith
  have hN1 : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast Nat.one_le_two_pow
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hNroot : N ^ ((1 : ℝ) / 3) =
      (2 : ℝ) ^ (((topExponent t : ℕ) : ℝ) / 3) := by
    dsimp only [N]
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hrootle : N ^ ((1 : ℝ) / 3) ≤ t / (8 * Real.pi) := by
    rw [hNroot]
    rw [le_div_iff₀ (by positivity)]
    simpa only [mul_comm] using topExponent_bound ht8
  have hratiole : t / (8 * Real.pi) ≤ t := by
    have hden : (1 : ℝ) ≤ 8 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hmul := mul_le_mul_of_nonneg_left hden ht0.le
    rw [mul_one] at hmul
    exact (div_le_iff₀ (by positivity)).2 (by simpa only [mul_comm] using hmul)
  have hnum1 : N ^ (1 - σ) ≤ t := by
    calc
      N ^ (1 - σ) ≤ N ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow_of_exponent_le hN1 hthird
      _ ≤ t / (8 * Real.pi) := hrootle
      _ ≤ t := hratiole
  have hdennorm : t ≤ ‖w - 1‖ := by
    have him := Complex.abs_im_le_norm (w - 1)
    have himw : (w - 1).im = t := by simp [w]
    rw [himw, abs_of_pos ht0] at him
    exact him
  have htail1 : N ^ (1 - σ) / ‖w - 1‖ ≤ 1 := by
    rw [div_le_one (lt_of_lt_of_le ht0 hdennorm)]
    exact hnum1.trans hdennorm
  have hcube := cube_le_two_pow_topExponent ht8
  have hcubeN : (t / (8 * Real.pi)) ^ (3 : ℕ) ≤ 2 * N := by
    dsimp only [N]
    rw [show 2 * (((2 ^ topExponent t : ℕ) : ℝ)) =
        (((2 ^ (topExponent t + 1) : ℕ) : ℝ)) by
      push_cast
      rw [pow_succ]
      ring]
    exact hcube
  have hpi2 : Real.pi ^ 2 < 10 := by
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hpi3 : Real.pi ^ 3 < 32 := by
    nlinarith [hpi2, Real.pi_lt_d2, Real.pi_pos]
  have hform : (t / (8 * Real.pi)) ^ (3 : ℕ) =
      t ^ 3 / (512 * Real.pi ^ 3) := by
    field_simp
    ring
  have hcubelower : t ^ 3 / 16384 ≤ (t / (8 * Real.pi)) ^ (3 : ℕ) := by
    rw [hform, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [hpi3, pow_pos ht0 3]
  have hNlower : t ^ 3 ≤ 32768 * N := by
    nlinarith [hcubelower, hcubeN]
  have hsquare : (t + 2) ^ 2 ≤ 2 * t ^ 2 := by
    nlinarith [sq_nonneg (t - 2)]
  have hmul : 4096 * t ^ 2 ≤ t ^ 3 := by
    have h4096 : (4096 : ℝ) ≤ t := by linarith
    have hh := mul_le_mul_of_nonneg_right h4096 (sq_nonneg t)
    nlinarith
  have hNbig : (t + 2) ^ 2 ≤ 16 * N := by
    nlinarith [hsquare, hmul, hNlower]
  have hsqrtmul : Real.sqrt N * Real.sqrt N = N :=
    Real.mul_self_sqrt hN0.le
  have hsqrtnn : 0 ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hsqrtpos : 0 < Real.sqrt N := by nlinarith
  have hsqrt : t + 2 ≤ 4 * Real.sqrt N := by
    have hquarter : (t + 2) / 4 ≤ Real.sqrt N :=
      (Real.le_sqrt (by positivity) hN0.le).mpr (by nlinarith [hNbig])
    linarith
  have hmono : N ^ (-σ) ≤ N ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hsqrtN : N ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring,
      Real.rpow_neg hN0.le]
    exact (one_div _).symm
  have hnum2 : N ^ (-σ) ≤ 1 / Real.sqrt N := by
    rw [← hsqrtN]
    exact hmono
  have hmulnum : N ^ (-σ) * Real.sqrt N ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hnum2 hsqrtnn
    rwa [one_div, inv_mul_cancel₀ hsqrtpos.ne'] at hh
  have hdiv : N ^ (-σ) / σ ≤ 2 / Real.sqrt N := by
    rw [div_le_div_iff₀ hσ0 hsqrtpos]
    exact hmulnum.trans (by linarith [hσhalf])
  have hwnorm : ‖w‖ ≤ t + 2 := by
    have hwre : w.re = σ := by simp [w]
    have hwim : w.im = t := by simp [w]
    calc
      ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ = σ + t := by rw [hwre, hwim, abs_of_pos hσ0, abs_of_pos ht0]
      _ ≤ t + 2 := by linarith
  have htail2 : ‖w‖ * (N ^ (-σ) / σ) ≤ 8 := by
    calc
      ‖w‖ * (N ^ (-σ) / σ) ≤ (t + 2) * (2 / Real.sqrt N) := by
        calc
          ‖w‖ * (N ^ (-σ) / σ) ≤ (t + 2) * (N ^ (-σ) / σ) :=
            mul_le_mul_of_nonneg_right hwnorm (by positivity)
          _ ≤ (t + 2) * (2 / Real.sqrt N) :=
            mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ ≤ 8 := by
        rw [mul_comm, div_mul_eq_mul_div, div_le_iff₀ hsqrtpos]
        nlinarith
  dsimp only [N, w] at htail1 htail2 ⊢
  linarith

/-- The canonical head remains logarithmic at every abscissa between the Route-T edge and one. -/
theorem routeTGlobalHead_le_of_abscissa {V : ℕ} {σ : ℝ}
    (hσlo : routeTStripAbscissa V ≤ σ) (hσone : σ < 1) :
    1 + ((routeTGlobalStart V : ℝ) ^ (1 - σ) - 1) / (1 - σ) +
        (routeTGlobalStart V : ℝ) ^ (-σ) ≤
      2 + 2 * Real.log (routeTGlobalStart V : ℝ) := by
  have hσ0 : 0 < σ := lt_of_lt_of_le (routeTStripAbscissa_pos V) hσlo
  have ha : 0 < 1 - σ := by linarith
  have hA1 : (1 : ℝ) ≤ routeTGlobalStart V := by
    exact_mod_cast Nat.one_le_two_pow
  have hlog0 : 0 ≤ Real.log (routeTGlobalStart V : ℝ) := Real.log_nonneg hA1
  have hdelta : 1 - σ ≤ routeTStripWidth V := by
    unfold routeTStripAbscissa at hσlo
    linarith
  have hpow : (routeTGlobalStart V : ℝ) ^ (1 - σ) ≤ 2 := by
    exact (Real.rpow_le_rpow_of_exponent_le hA1 hdelta).trans
      (routeTGlobalStart_rpow_width_le_two V)
  have hquot := rpow_sub_one_div_le hA1 ha
  have hprod : (routeTGlobalStart V : ℝ) ^ (1 - σ) *
      Real.log (routeTGlobalStart V : ℝ) ≤
        2 * Real.log (routeTGlobalStart V : ℝ) :=
    mul_le_mul_of_nonneg_right hpow hlog0
  have hlast : (routeTGlobalStart V : ℝ) ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hA1 (by linarith)
  linarith

/-- **Uniform Route-T rectangle below one.**  One fixed canonical height supplies every abscissa
between its left edge and `1`; no monotonicity of complex sums is used. -/
theorem norm_riemannZeta_le_routeT_canonical_strip
    {t σ : ℝ} (htlarge : 100000 ≤ t)
    (hlarge : routeTDepthRootThreshold ^ 10 ≤ routeTBinaryHeight t)
    (hσlo : routeTStripAbscissa (routeTGlobalShell t) ≤ σ) (hσone : σ < 1) :
    ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
      11 + 2 * Real.log (routeTGlobalStart (routeTGlobalShell t) : ℝ) +
        (routeTGlobalBlocks t : ℝ) * 6912 := by
  let V := routeTGlobalShell t
  let A := routeTGlobalStart V
  let R := routeTGlobalBlocks t
  have ht8 : 8 * Real.pi ≤ t := by nlinarith [Real.pi_lt_d2]
  have ht : 1 < t := by linarith
  have hdepth := routeTCanonicalDepth ht hlarge
  have hσ0 : 0 < σ := lt_of_lt_of_le (routeTStripAbscissa_pos V) (by
    simpa only [V] using hσlo)
  have hdelta : 1 - σ ≤ routeTStripWidth V := by
    have hlo : routeTStripAbscissa V ≤ σ := by simpa only [V] using hσlo
    unfold routeTStripAbscissa at hlo
    linarith
  have hroute : 2 * (1 - σ) ≤
      1 / (5000000000000000 * (V : ℝ) ^ 4) := by
    exact (mul_le_mul_of_nonneg_left hdelta (by norm_num)).trans
      (routeTStripWidth_route_condition (routeTGlobalShell_pos t))
  have hderivative : 1 - σ ≤ 1 / (3 * (2 : ℝ) ^ (566 : ℕ)) :=
    hdelta.trans (routeTStripWidth_derivative_condition V)
  have hmain := norm_riemannZeta_le_routeT_uniform
    (A := A) (V := V) (R := R) (σ := σ) (t := t)
    (routeTGlobalStart_two_le V) hσ0 hσone ht
    (routeTGlobalStart_size V)
    (by simpa only [A, V] using routeTGlobalHeight_upper ht)
    (routeTGlobalStart_factorial V)
    (by simpa only [A, R, V] using routeTGlobalTruncation_low ht8 hdepth)
    hroute hderivative
  have htrunc := routeTGlobalTruncation_eq (t := t) (by omega)
  rw [htrunc] at hmain
  have hhead := routeTGlobalHead_le_of_abscissa
    (V := V) (σ := σ) (by simpa only [V] using hσlo) hσone
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (566 : ℕ) := one_le_pow₀ (by norm_num)
  have hden : (3 : ℝ) ≤ 3 * (2 : ℝ) ^ (566 : ℕ) := by
    have hh := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 3)
    simpa only [mul_one] using hh
  have hthird : 1 - σ ≤ (1 : ℝ) / 3 :=
    hderivative.trans (one_div_le_one_div_of_le (by norm_num) hden)
  have hσhalf : (1 : ℝ) / 2 ≤ σ := by linarith
  have htail := routeT_cubic_truncation_tails_le_nine ht8 htlarge hσhalf hσone.le hthird
  dsimp only [A, R, V] at hmain hhead ⊢
  linarith

/-- **Closed left-edge growth.**  The exact continuation tails contribute at most nine. -/
theorem norm_riemannZeta_le_routeT_canonical_polynomial
    {t : ℝ} (htlarge : 100000 ≤ t)
    (hlarge : routeTDepthRootThreshold ^ 10 ≤ routeTBinaryHeight t) :
    ‖riemannZeta ((routeTStripAbscissa (routeTGlobalShell t) : ℂ) +
        Complex.I * (t : ℂ))‖ ≤
      11 + (routeTStripDenominator * (routeTGlobalShell t + 1) ^ 9 : ℕ) +
        (routeTGlobalBlocks t : ℝ) * 6912 := by
  have ht8 : 8 * Real.pi ≤ t := by
    nlinarith [Real.pi_lt_d2]
  have hmain := norm_riemannZeta_le_routeT_canonical_large ht8 hlarge
  have hwidth := routeTStripWidth_derivative_condition (routeTGlobalShell t)
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (566 : ℕ) := one_le_pow₀ (by norm_num)
  have hden : (3 : ℝ) ≤ 3 * (2 : ℝ) ^ (566 : ℕ) := by
    have hh := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 3)
    simpa only [mul_one] using hh
  have hthird : routeTStripWidth (routeTGlobalShell t) ≤ (1 : ℝ) / 3 := by
    exact hwidth.trans (one_div_le_one_div_of_le (by norm_num) hden)
  have hσhalf : (1 : ℝ) / 2 ≤ routeTStripAbscissa (routeTGlobalShell t) := by
    unfold routeTStripAbscissa
    linarith
  have hσone : routeTStripAbscissa (routeTGlobalShell t) ≤ 1 := by
    unfold routeTStripAbscissa
    exact sub_le_self 1 (routeTStripWidth_pos (routeTGlobalShell t)).le
  have htail := routeT_cubic_truncation_tails_le_nine ht8 htlarge hσhalf hσone (by
    rw [one_sub_routeTStripAbscissa]
    exact hthird)
  linarith

end

end RHTower.Sieve
