import GaloisForLFunctions.RHTower.Sieve.MoebiusAbsorbTwo
import GaloisForLFunctions.RHTower.Sieve.SmoothVsSharp

/-!
# The sharp Möbius sum, with an explicit saving of exponent `1/3`

At the balanced smoothing width the contour bound and the smooth-versus-sharp comparison are of the
same size, and both are

```text
N · exp( -(log N)^{1/3} / 108 ).
```

This is the quantitative form of `tendsto_norm_sum_moebius_div`, at the exponent the exponent-one
zero-free region supports.  The corpus's other explicit rate,
`exists_norm_sum_moebiusTwist_rate`, is for the twisted sum at exponent `1/10`.
-/

namespace RHTower.Sieve

open Complex Filter Topology GaloisForLFunctions.HTGeometry

/-- **The price of the smoothing against the saving.**  A squared ratio `exp(t/27)`, a trivial size
`3N`, a polynomial `4t²` and the saving `exp(-t/18)` leave `exp(-t/108)`. -/
theorem absorb_rate {B₀ R Z N s t : ℝ} (hB₀ : 0 ≤ B₀) (hR : R ^ 2 ≤ 9 * Real.exp (t / 27))
    (hZ : Z ≤ 3 * N) (hZ0 : 0 ≤ Z) (hN0 : 0 ≤ N)
    (hs : s ≤ 2 * t) (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) (hts : t ≤ s) :
    B₀ * R ^ 2 * (Z * s ^ 2 * Real.exp (-(s / 18)))
      ≤ 5038848 * B₀ * N * Real.exp (-(t / 108)) := by
  have hsq : s ^ 2 ≤ 4 * t ^ 2 := by nlinarith
  have hZs : Z * s ^ 2 ≤ 12 * N * t ^ 2 := by
    have h := mul_le_mul hZ hsq (sq_nonneg s) (by linarith : (0 : ℝ) ≤ 3 * N)
    linarith [h]
  have hE : Real.exp (-(s / 18)) ≤ Real.exp (-(t / 18)) := Real.exp_le_exp.mpr (by linarith)
  have hprod : R ^ 2 * (Z * s ^ 2) * Real.exp (-(s / 18))
      ≤ 9 * Real.exp (t / 27) * (12 * N * t ^ 2) * Real.exp (-(t / 18)) :=
    mul_three_le hR hZs hE (sq_nonneg R) (mul_nonneg hZ0 (sq_nonneg s)) (Real.exp_pos _).le
  have hexp1 : Real.exp (t / 27) * Real.exp (-(t / 18)) = Real.exp (-(t / 54)) := by
    rw [← Real.exp_add]; ring_nf
  have hexp2 : Real.exp (t / 108) * Real.exp (-(t / 54)) = Real.exp (-(t / 108)) := by
    rw [← Real.exp_add]; ring_nf
  have hfac : (0 : ℝ) ≤ 108 * N * Real.exp (-(t / 54)) :=
    mul_nonneg (mul_nonneg (by norm_num) hN0) (Real.exp_pos _).le
  have hmid : R ^ 2 * (Z * s ^ 2 * Real.exp (-(s / 18)))
      ≤ 108 * N * t ^ 2 * Real.exp (-(t / 54)) := by
    calc R ^ 2 * (Z * s ^ 2 * Real.exp (-(s / 18)))
        = R ^ 2 * (Z * s ^ 2) * Real.exp (-(s / 18)) := by ring
      _ ≤ 9 * Real.exp (t / 27) * (12 * N * t ^ 2) * Real.exp (-(t / 18)) := hprod
      _ = 108 * N * t ^ 2 * (Real.exp (t / 27) * Real.exp (-(t / 18))) := by ring
      _ = 108 * N * t ^ 2 * Real.exp (-(t / 54)) := by rw [hexp1]
  have hlast : 108 * N * t ^ 2 * Real.exp (-(t / 54))
      ≤ 5038848 * N * Real.exp (-(t / 108)) := by
    calc 108 * N * t ^ 2 * Real.exp (-(t / 54))
        = 108 * N * Real.exp (-(t / 54)) * t ^ 2 := by ring
      _ ≤ 108 * N * Real.exp (-(t / 54)) * (46656 * Real.exp (t / 108)) :=
          mul_le_mul_of_nonneg_left (sq_le_exp_div ht0) hfac
      _ = 5038848 * N * (Real.exp (t / 108) * Real.exp (-(t / 54))) := by ring
      _ = 5038848 * N * Real.exp (-(t / 108)) := by rw [hexp2]
  calc B₀ * R ^ 2 * (Z * s ^ 2 * Real.exp (-(s / 18)))
      = B₀ * (R ^ 2 * (Z * s ^ 2 * Real.exp (-(s / 18)))) := by ring
    _ ≤ B₀ * (5038848 * N * Real.exp (-(t / 108))) :=
        mul_le_mul_of_nonneg_left (le_trans hmid hlast) hB₀
    _ = 5038848 * B₀ * N * Real.exp (-(t / 108)) := by ring

/-- The smoothing width, written multiplicatively. -/
theorem smoothWidthTwo_eq (N : ℝ) :
    smoothWidthTwo N = N * Real.exp (-((Real.log N) ^ ((1 : ℝ) / 3) / 54)) := by
  rw [smoothWidthTwo, smoothRatioTwo, Real.exp_neg, div_eq_mul_inv]

/-- The saving is not yet at the trivial size. -/
theorem one_le_mul_exp_neg {N : ℝ} (hN0 : 0 < N) (hN : 1 ≤ Real.log N) :
    1 ≤ N * Real.exp (-((Real.log N) ^ ((1 : ℝ) / 3) / 108)) := by
  have ht := rpow_third_le_log hN
  have ht0 : (0 : ℝ) ≤ (Real.log N) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
  calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (Real.log N - (Real.log N) ^ ((1 : ℝ) / 3) / 108) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = N * Real.exp (-((Real.log N) ^ ((1 : ℝ) / 3) / 108)) := by
        rw [Real.exp_sub, Real.exp_log hN0, Real.exp_neg, div_eq_mul_inv]

/-- **The sharp Möbius sum, with an explicit saving of exponent `1/3`.** -/
theorem exists_norm_sum_moebius_kappa_two_rate :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℝ in atTop,
      ‖∑ n ∈ Finset.range (⌊N⌋₊ + 1), (ArithmeticFunction.moebius n : ℂ)‖
        ≤ B * N * Real.exp (-((Real.log N) ^ ((1 : ℝ) / 3) / 108)) := by
  obtain ⟨C, C', Ms, K₀, hC, hC', hMs, hmain⟩ :=
    exists_norm_tsum_moebius_smoothWeight_kappa_two_rate
  have hB₀0 : (0 : ℝ) ≤ 80 * Real.exp (22 / 4) * C + 16 * Ms * C' + 9 * Ms * (1 + 2 * C) := by
    have h1 : (0 : ℝ) ≤ 80 * Real.exp (22 / 4) * C := mul_nonneg (by positivity) hC
    have h2 : (0 : ℝ) ≤ 16 * Ms * C' := mul_nonneg (mul_nonneg (by norm_num) hMs) hC'
    have h3 : (0 : ℝ) ≤ 9 * Ms * (1 + 2 * C) :=
      mul_nonneg (mul_nonneg (by norm_num) hMs) (by linarith)
    linarith
  refine ⟨5038848 * (80 * Real.exp (22 / 4) * C + 16 * Ms * C' + 9 * Ms * (1 + 2 * C)) + 2,
    by linarith, ?_⟩
  have htend : Tendsto (fun N : ℝ => Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 3))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp Real.tendsto_log_atTop))
  filter_upwards [eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    htend.eventually_ge_atTop ((K₀ : ℕ) : ℝ)] with N hN3 hlogN hevK
  have hN0 : (0 : ℝ) < N := by linarith
  have hH1 : (1 : ℝ) ≤ smoothWidthTwo N := one_le_smoothWidthTwo hN0 hlogN
  have hHN : smoothWidthTwo N ≤ N := smoothWidthTwo_le hN0.le hlogN
  have hZ0 : (0 : ℝ) < N + smoothWidthTwo N + 1 := by linarith
  have hlogZ : (1 : ℝ) ≤ Real.log (N + smoothWidthTwo N + 1) :=
    le_trans hlogN (Real.log_le_log hN0 (by linarith))
  have hts := rpow_le_shift hN0 hlogN
  have hst := rpow_shift_le hN3 hlogN
  have ht0 : (0 : ℝ) ≤ (Real.log N) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
  have hs0 : (0 : ℝ) ≤ (Real.log (N + smoothWidthTwo N + 1)) ^ ((1 : ℝ) / 3) := by linarith
  -- the parameter is past the threshold
  have hKparam : K₀ ≤ contourParamTwo (N + smoothWidthTwo N + 1) := by
    have h1 : ((K₀ : ℕ) : ℝ)
        ≤ Real.exp (2 * (Real.log (N + smoothWidthTwo N + 1)) ^ ((1 : ℝ) / 3)) :=
      le_trans hevK (Real.exp_le_exp.mpr (by linarith))
    exact_mod_cast le_trans h1 (exp_le_contourParamTwo (N + smoothWidthTwo N + 1))
  -- the contour bound at the balanced width
  have hb := hmain N (smoothWidthTwo N) (smoothRatioTwo N) hN0 hH1
    (le_of_eq (div_smoothWidthTwo hN0)) (by linarith) hlogZ hKparam
  -- the coefficient
  have hrest0 : (0 : ℝ) ≤ (N + smoothWidthTwo N + 1)
      * ((Real.log (N + smoothWidthTwo N + 1)) ^ ((1 : ℝ) / 3)) ^ 2
      * Real.exp (-((Real.log (N + smoothWidthTwo N + 1)) ^ ((1 : ℝ) / 3) / 18)) :=
    mul_nonneg (mul_nonneg hZ0.le (sq_nonneg _)) (Real.exp_pos _).le
  have hcoef := mul_le_mul_of_nonneg_right
    (coeffMajorantTwo_le (C := C) (C' := C') (Ms := Ms) (L := smoothRatioTwo N)
      hC hC' hMs (smoothRatioTwo_pos N).le) hrest0
  have habs := absorb_rate (B₀ := 80 * Real.exp (22 / 4) * C + 16 * Ms * C' + 9 * Ms * (1 + 2 * C))
    (R := smoothRatioTwo N + 2) (Z := N + smoothWidthTwo N + 1) (N := N)
    (s := (Real.log (N + smoothWidthTwo N + 1)) ^ ((1 : ℝ) / 3))
    (t := (Real.log N) ^ ((1 : ℝ) / 3))
    hB₀0 (sq_ratio_le hlogN) (by linarith) hZ0.le hN0.le hst hs0 ht0 hts
  -- the smoothed sum
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hsmooth : ‖(∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ)
        * ((GaloisForLFunctions.HTGeometry.smoothWeight N (smoothWidthTwo N) (n : ℝ) : ℝ) : ℂ))‖
      ≤ 5038848 * (80 * Real.exp (22 / 4) * C + 16 * Ms * C' + 9 * Ms * (1 + 2 * C)) * N
          * Real.exp (-((Real.log N) ^ ((1 : ℝ) / 3) / 108)) := by
    have hscale : ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ)
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N (smoothWidthTwo N) (n : ℝ) : ℝ) : ℂ))‖
        = (2 * Real.pi) * ‖(∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ)
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N (smoothWidthTwo N) (n : ℝ) : ℝ) : ℂ))‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hnn : (0 : ℝ) ≤ ‖(∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ)
        * ((GaloisForLFunctions.HTGeometry.smoothWeight N (smoothWidthTwo N) (n : ℝ) : ℝ) : ℂ))‖ :=
      norm_nonneg _
    nlinarith [hb, hcoef, habs, hscale, hnn, hpi]
  -- the comparison with the sharp sum
  have hcmp := norm_tsum_smoothWeight_sub_sum_le (N := N) (H := smoothWidthTwo N) hN0
    (by linarith)
  have hHle : smoothWidthTwo N ≤ N * Real.exp (-((Real.log N) ^ ((1 : ℝ) / 3) / 108)) := by
    rw [smoothWidthTwo_eq]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hN0.le
  have hone := one_le_mul_exp_neg hN0 hlogN
  have hsplit : ‖∑ n ∈ Finset.range (⌊N⌋₊ + 1), (ArithmeticFunction.moebius n : ℂ)‖
        - ‖(∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ)
            * ((GaloisForLFunctions.HTGeometry.smoothWeight N (smoothWidthTwo N) (n : ℝ) : ℝ) : ℂ))‖
      ≤ ‖(∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ)
            * ((GaloisForLFunctions.HTGeometry.smoothWeight N (smoothWidthTwo N) (n : ℝ) : ℝ) : ℂ))
          - ∑ n ∈ Finset.range (⌊N⌋₊ + 1), (ArithmeticFunction.moebius n : ℂ)‖ := by
    rw [norm_sub_rev]
    exact norm_sub_norm_le _ _
  linarith [hsmooth, hcmp, hHle, hone, hsplit]

end RHTower.Sieve
