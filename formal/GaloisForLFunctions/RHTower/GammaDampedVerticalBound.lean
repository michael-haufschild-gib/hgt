import GaloisForLFunctions.RHTower.ZetaVerticalLineBound
import GaloisForLFunctions.RHTower.GammaDampedSineSeries

/-!
# Vertical-line bounds for the damped squarefree series

On the strip `1 < re z ≤ 2` the damped series is controlled by the logarithmic vertical-line bound
for zeta:

```text
F(z) = ζ(z)/ζ(2z) + H(z),      ‖1/ζ(2z)‖ ≤ 2,   ‖H(z)‖ ≤ 1/2,
```

so `‖F(z)‖ ≤ 2 (log|Im z| + 5) + 1/2` for `|Im z| ≥ 2`.  Both auxiliary bounds are the Möbius and
the quartic-correction Dirichlet series compared against `∑ n^(-2) ≤ 2`.
-/

open LSeries

namespace RHTower

noncomputable section

/-! ### The inverse-square comparison -/

theorem tsum_inv_natCast_sq_le : (∑' n : ℕ, ((n : ℝ) ^ (2 : ℕ))⁻¹) ≤ 2 := by
  have hval : (∑' n : ℕ, ((n : ℝ) ^ (2 : ℕ))⁻¹) = Real.pi ^ 2 / 6 := by
    rw [← hasSum_zeta_two.tsum_eq]
    exact tsum_congr fun n => by rw [one_div]
  rw [hval]
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

theorem summable_inv_natCast_sq : Summable fun n : ℕ => ((n : ℝ) ^ (2 : ℕ))⁻¹ := by
  refine hasSum_zeta_two.summable.congr fun n => ?_
  rw [one_div]

/-- A Dirichlet series with termwise bounded coefficients is bounded on `re s ≥ 2`. -/
theorem norm_lSeries_le_of_term_bound {f : ℕ → ℂ} {s : ℂ} {u : ℕ → ℝ} (hu : Summable u)
    (hb : ∀ n, ‖LSeries.term f s n‖ ≤ u n) : ‖LSeries f s‖ ≤ ∑' n, u n := by
  have hsum : Summable fun n => ‖LSeries.term f s n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb hu
  calc ‖LSeries f s‖ = ‖∑' n, LSeries.term f s n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n, u n := Summable.tsum_mono hsum hu hb

theorem norm_term_le_inv_sq {f : ℕ → ℂ} {s : ℂ} (hs : 2 ≤ s.re) (hf : ∀ n, ‖f n‖ ≤ 1) (n : ℕ) :
    ‖LSeries.term f s n‖ ≤ ((n : ℝ) ^ (2 : ℕ))⁻¹ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hsq : ((n : ℝ) ^ (2 : ℕ)) = (n : ℝ) ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hsqpos : (0 : ℝ) < (n : ℝ) ^ (2 : ℕ) := by positivity
    have hpospow : (0 : ℝ) < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos hpos _
    have hcmp : ((n : ℝ) ^ (2 : ℕ)) ≤ (n : ℝ) ^ s.re := by
      rw [hsq]
      exact Real.rpow_le_rpow_of_exponent_le hnR hs
    rw [term_of_ne_zero hn, norm_div, norm_natCast_cpow hn1, div_le_iff₀ hpospow]
    have h1 : (1 : ℝ) ≤ ((n : ℝ) ^ (2 : ℕ))⁻¹ * (n : ℝ) ^ s.re := by
      rw [inv_mul_eq_div, le_div_iff₀ hsqpos]
      linarith
    linarith [hf n]

/-! ### The two auxiliary series -/

theorem norm_inv_riemannZeta_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) : ‖(riemannZeta s)⁻¹‖ ≤ 2 := by
  have hs1 : 1 < s.re := by linarith
  rw [← LSeries_moebius_eq_inv_riemannZeta hs1]
  refine le_trans (norm_lSeries_le_of_term_bound summable_inv_natCast_sq ?_)
    tsum_inv_natCast_sq_le
  refine norm_term_le_inv_sq hs fun n => ?_
  by_cases hsf : Squarefree n
  · have h := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
    have hR : ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 = 1 := by exact_mod_cast h
    have habs : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| = 1 := by
      nlinarith [abs_nonneg ((ArithmeticFunction.moebius n : ℤ) : ℝ),
        sq_abs ((ArithmeticFunction.moebius n : ℤ) : ℝ)]
    rw [Complex.norm_intCast, habs]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
    simp

theorem norm_gammaDampedCorrectionLSeries_le {z : ℂ} (hz : 0 ≤ z.re) :
    ‖gammaDampedCorrectionLSeries z‖ ≤ 1 / 2 := by
  have hb : ∀ n : ℕ, ‖LSeries.term gammaDampedCorrectionCoeff z n‖
      ≤ 1 / 4 * ((n : ℝ) ^ (2 : ℕ))⁻¹ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hcoeff := norm_gammaDampedCorrectionCoeff_le n
      have hpospow : (0 : ℝ) < (n : ℝ) ^ z.re := Real.rpow_pos_of_pos hpos _
      have hone : (1 : ℝ) ≤ (n : ℝ) ^ z.re := Real.one_le_rpow hnR hz
      rw [term_of_ne_zero hn, norm_div, norm_natCast_cpow hn1, div_le_iff₀ hpospow]
      have hquart : (n : ℝ) ^ (-4 : ℝ) ≤ ((n : ℝ) ^ (2 : ℕ))⁻¹ := by
        rw [show ((n : ℝ) ^ (2 : ℕ))⁻¹ = (n : ℝ) ^ (-(2 : ℝ)) by
          rw [Real.rpow_neg hpos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]]
        exact Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
      have hnn : (0 : ℝ) ≤ ((n : ℝ) ^ (2 : ℕ))⁻¹ := by positivity
      calc ‖gammaDampedCorrectionCoeff n‖ ≤ 1 / 4 * (n : ℝ) ^ (-4 : ℝ) := hcoeff
        _ ≤ 1 / 4 * ((n : ℝ) ^ (2 : ℕ))⁻¹ := by linarith
        _ ≤ 1 / 4 * ((n : ℝ) ^ (2 : ℕ))⁻¹ * (n : ℝ) ^ z.re := by nlinarith
  refine le_trans (norm_lSeries_le_of_term_bound (summable_inv_natCast_sq.mul_left _) hb) ?_
  rw [tsum_mul_left]
  linarith [tsum_inv_natCast_sq_le]

/-! ### The damped series on a vertical line -/

/-- **The vertical-line bound for the damped squarefree series.** -/
theorem norm_lSeries_gammaDampedCoeff_le {z : ℂ} (h1 : 1 < z.re) (h2 : z.re ≤ 2)
    (ht : 2 ≤ |z.im|) :
    ‖LSeries gammaDampedCoeff z‖ ≤ 2 * (Real.log |z.im| + 5) + 1 / 2 := by
  have hzeta : ‖riemannZeta z‖ ≤ Real.log |z.im| + 5 :=
    norm_riemannZeta_le_log_add (by linarith) h2 ht
  have h2z : (2 : ℝ) ≤ (2 * z).re := by
    rw [re_two_mul]
    linarith
  have hinv : ‖(riemannZeta (2 * z))⁻¹‖ ≤ 2 := norm_inv_riemannZeta_le_of_two_le_re h2z
  have hH : ‖gammaDampedCorrectionLSeries z‖ ≤ 1 / 2 :=
    norm_gammaDampedCorrectionLSeries_le (by linarith)
  rw [lSeries_gammaDampedCoeff h1]
  have hnn : (0 : ℝ) ≤ Real.log |z.im| + 5 := by
    have : (0 : ℝ) ≤ Real.log |z.im| := Real.log_nonneg (by linarith)
    linarith
  calc ‖riemannZeta z / riemannZeta (2 * z) + gammaDampedCorrectionLSeries z‖
      ≤ ‖riemannZeta z / riemannZeta (2 * z)‖ + ‖gammaDampedCorrectionLSeries z‖ :=
        norm_add_le _ _
    _ = ‖riemannZeta z‖ * ‖(riemannZeta (2 * z))⁻¹‖ + ‖gammaDampedCorrectionLSeries z‖ := by
        rw [div_eq_mul_inv, norm_mul]
    _ ≤ (Real.log |z.im| + 5) * 2 + 1 / 2 := by
        have := mul_le_mul hzeta hinv (norm_nonneg _) hnn
        linarith
    _ = 2 * (Real.log |z.im| + 5) + 1 / 2 := by ring

/-! ### The derivative on a vertical line -/

theorem mem_strip_of_dist_le {σ x : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hx : 3 ≤ |x|)
    {w : ℂ} (hw : ‖w - gammaDampedCriticalLinePoint σ x‖ ≤ (σ - 1) / 4) :
    1 < w.re ∧ w.re ≤ 2 ∧ 2 ≤ |w.im| ∧ Real.log |w.im| ≤ Real.log (2 * |x|) := by
  have hRle : (σ - 1) / 4 ≤ 1 / 4 := by linarith
  have hre : |w.re - (gammaDampedCriticalLinePoint σ x).re| ≤ (σ - 1) / 4 := by
    have h := Complex.abs_re_le_norm (w - gammaDampedCriticalLinePoint σ x)
    simpa [Complex.sub_re] using le_trans h hw
  have him : |w.im - (gammaDampedCriticalLinePoint σ x).im| ≤ (σ - 1) / 4 := by
    have h := Complex.abs_im_le_norm (w - gammaDampedCriticalLinePoint σ x)
    simpa [Complex.sub_im] using le_trans h hw
  rw [gammaDampedCriticalLinePoint_re] at hre
  have hims : (gammaDampedCriticalLinePoint σ x).im = -x := by
    simp [gammaDampedCriticalLinePoint]
  rw [hims] at him
  have hre' := abs_le.mp hre
  have hkey : abs (|w.im| - |x|) ≤ (σ - 1) / 4 := by
    have h := abs_abs_sub_abs_le_abs_sub w.im (-x)
    rw [abs_neg] at h
    exact le_trans h him
  have hkey' := abs_le.mp hkey
  refine ⟨by linarith [hre'.1], by linarith [hre'.2], by linarith [hkey'.1], ?_⟩
  have hpos : (0 : ℝ) < |w.im| := by linarith [hkey'.1]
  refine Real.log_le_log hpos ?_
  linarith [hkey'.2]

/-- **Cauchy estimate on the critical vertical line.**  The derivative of the damped series is at
most `4/(σ-1)` times its logarithmic vertical-line bound. -/
theorem norm_deriv_lSeries_gammaDampedCoeff_le {σ x : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (hx : 3 ≤ |x|) :
    ‖deriv (LSeries gammaDampedCoeff) (gammaDampedCriticalLinePoint σ x)‖
      ≤ (2 * (Real.log (2 * |x|) + 5) + 1 / 2) / ((σ - 1) / 4) := by
  have hR : (0 : ℝ) < (σ - 1) / 4 := by linarith
  have hsub : Metric.closedBall (gammaDampedCriticalLinePoint σ x) ((σ - 1) / 4)
      ⊆ {s : ℂ | abscissaOfAbsConv gammaDampedCoeff < (s.re : EReal)} := by
    intro w hw
    have hwle : ‖w - gammaDampedCriticalLinePoint σ x‖ ≤ (σ - 1) / 4 := by
      rw [← Complex.dist_eq]
      exact Metric.mem_closedBall.mp hw
    have hstrip := mem_strip_of_dist_le hσ1 hσ2 hx hwle
    refine lt_of_le_of_lt abscissaOfAbsConv_gammaDampedCoeff_le ?_
    rw [show ((1 : EReal)) = ((1 : ℝ) : EReal) from rfl]
    exact_mod_cast hstrip.1
  have hdiff : DiffContOnCl ℂ (LSeries gammaDampedCoeff)
      (Metric.ball (gammaDampedCriticalLinePoint σ x) ((σ - 1) / 4)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ (ne_of_gt hR)]
    exact (LSeries_differentiableOn gammaDampedCoeff).mono hsub
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdiff fun w hw => ?_
  have hwle : ‖w - gammaDampedCriticalLinePoint σ x‖ ≤ (σ - 1) / 4 := by
    rw [← Complex.dist_eq]
    exact le_of_eq (Metric.mem_sphere.mp hw)
  have hstrip := mem_strip_of_dist_le hσ1 hσ2 hx hwle
  calc ‖LSeries gammaDampedCoeff w‖ ≤ 2 * (Real.log |w.im| + 5) + 1 / 2 :=
        norm_lSeries_gammaDampedCoeff_le hstrip.1 hstrip.2.1 hstrip.2.2.1
    _ ≤ 2 * (Real.log (2 * |x|) + 5) + 1 / 2 := by linarith [hstrip.2.2.2]

end

end RHTower
