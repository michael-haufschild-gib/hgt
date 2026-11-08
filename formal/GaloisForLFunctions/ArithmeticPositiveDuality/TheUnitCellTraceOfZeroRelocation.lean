import GaloisForLFunctions.RHTower.ZetaEulerMaclaurinArbitraryOrder
import Mathlib.Analysis.Analytic.Binomial

/-!
# The unit-cell trace of a finite spectral correction

The inverse Mellin density of a simple rational pole is an ordinary power
sum. At a zeta zero its nondecaying spectral term disappears. The remaining
Euler–Maclaurin terms retain the integer lattice: after removing the constant
and first endpoint terms, the quadratic trace is a Bernoulli polynomial.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Finset RHTower

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- The power-sum kernel with its zeta value removed. At a zero this is the
literal density obtained by convolving a power with the integer measure. -/
def zeroPowerSumKernel (s : ℂ) (N : ℕ) : ℂ :=
  (N : ℂ) ^ (s - 1) * ((∑ n ∈ Icc 1 N, (n : ℂ) ^ (-s)) - riemannZeta s)

private theorem emBoundary_one (s : ℂ) (N : ℕ) :
    zetaEMBoundary 1 s N = (N : ℂ) ^ (-s) / 2 -
      s / 12 * (N : ℂ) ^ (-s - 1) +
      s * (s + 1) * (s + 2) / 720 * (N : ℂ) ^ (-s - 3) := by
  have h4 : bernoulli 4 = -1 / 30 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num : (4 : ℕ) ≠ 1)]
    exact bernoulli'_four
  norm_num [zetaEMBoundary, Finset.sum_range_succ, complexPowerTower,
    complexRisingFactor, Finset.prod_range_succ, bernoulli_two, h4]
  ring

private def emErrorConstant (s : ℂ) : ℝ :=
  |((bernoulli 4 : ℚ) : ℝ)| / 24 *
    ‖complexRisingFactor s 4‖ / (s.re + 3)

private theorem norm_scaled_em_error_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖(N : ℂ) ^ (s + 1) * (riemannZeta s - zetaEulerMaclaurinMain 1 N s)‖ ≤
      emErrorConstant s * (N : ℝ) ^ (-(2 : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hb := norm_riemannZeta_sub_zetaEulerMaclaurinMain_le hs hs1 hN 1
  norm_num only [Nat.reduceAdd, Nat.reduceMul, Nat.factorial, Nat.cast_ofNat] at hb
  have hb' : ‖riemannZeta s - zetaEulerMaclaurinMain 1 N s‖ ≤
      emErrorConstant s * (N : ℝ) ^ (-s.re - 3) := by
    convert hb using 1
    dsimp only [emErrorConstant]
    rw [show 1 - s.re - 4 = -s.re - 3 by ring]
    ring
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega),
    Complex.add_re, Complex.one_re]
  calc
    _ ≤ (N : ℝ) ^ (s.re + 1) * (emErrorConstant s * (N : ℝ) ^ (-s.re - 3)) :=
      mul_le_mul_of_nonneg_left hb' (Real.rpow_nonneg hNpos.le _)
    _ = emErrorConstant s * (N : ℝ) ^ (-(2 : ℝ)) := by
      rw [mul_left_comm, ← Real.rpow_add hNpos]
      congr 2
      ring

private theorem tendsto_scaled_em_error {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ (s + 1) *
      (riemannZeta s - zetaEulerMaclaurinMain 1 N s)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => emErrorConstant s * (N : ℝ) ^ (-(2 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (emErrorConstant s)
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact norm_scaled_em_error_le hs hs1 hN

private theorem tendsto_complex_nat_inv :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹) atTop (𝓝 0) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  change Tendsto (fun N : ℕ => (((N : ℝ)⁻¹ : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) at h
  simpa only [Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.ofReal_zero] using h

private theorem scaled_kernel_eq_em_error (s : ℂ) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℂ) ^ 2 * zeroPowerSumKernel s N - (N : ℂ) ^ 2 / (1 - s) - N / 2 =
      -s / 12 + (s * (s + 1) * (s + 2) / 720) / (N : ℂ) ^ 2 -
        (N : ℂ) ^ (s + 1) * (riemannZeta s - zetaEulerMaclaurinMain 1 N s) := by
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have h0 : (N : ℂ) ^ (s + 1) * (N : ℂ) ^ (1 - s) = (N : ℂ) ^ 2 := by
    rw [← Complex.cpow_add _ _ hn, show s + 1 + (1 - s) = (2 : ℂ) by ring]
    norm_cast
  have h1 : (N : ℂ) ^ (s + 1) * (N : ℂ) ^ (-s) = N := by
    rw [← Complex.cpow_add _ _ hn, show s + 1 + -s = (1 : ℂ) by ring]
    simp only [Complex.cpow_one]
  have h2 : (N : ℂ) ^ (s + 1) * (N : ℂ) ^ (-s - 1) = 1 := by
    rw [← Complex.cpow_add _ _ hn, show s + 1 + (-s - 1) = (0 : ℂ) by ring]
    simp only [Complex.cpow_zero]
  have h4 : (N : ℂ) ^ (s + 1) * (N : ℂ) ^ (-s - 3) = 1 / (N : ℂ) ^ 2 := by
    rw [← Complex.cpow_add _ _ hn, show s + 1 + (-s - 3) = -(2 : ℂ) by ring,
      Complex.cpow_neg]
    rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast, one_div]
  have hk : (N : ℂ) ^ 2 * zeroPowerSumKernel s N =
      (N : ℂ) ^ (s + 1) *
        ((∑ n ∈ Icc 1 N, (n : ℂ) ^ (-s)) - riemannZeta s) := by
    rw [zeroPowerSumKernel, ← mul_assoc]
    congr 1
    calc
      (N : ℂ) ^ 2 * (N : ℂ) ^ (s - 1) =
          (N : ℂ) ^ (2 : ℂ) * (N : ℂ) ^ (s - 1) := by norm_cast
      _ = (N : ℂ) ^ (s + 1) := by
        rw [← Complex.cpow_add _ _ hn]
        congr 1
        ring
  rw [hk, zetaEulerMaclaurinMain, emBoundary_one]
  linear_combination h0 / (1 - s) + h1 / 2 - (s / 12) * h2 +
    (s * (s + 1) * (s + 2) / 720) * h4

/-- The first nonconstant lattice trace at integer cutoffs is `-s/12`. -/
theorem tendsto_zeroPowerSumKernel_integer_trace {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ 2 * zeroPowerSumKernel s N -
      (N : ℂ) ^ 2 / (1 - s) - N / 2) atTop (𝓝 (-s / 12)) := by
  have ht : Tendsto (fun N : ℕ => (s * (s + 1) * (s + 2) / 720) /
      (N : ℂ) ^ 2) atTop (𝓝 0) := by
    simpa only [inv_pow, div_eq_mul_inv, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero] using (tendsto_complex_nat_inv.pow 2).const_mul
        (s * (s + 1) * (s + 2) / 720)
  have h := (ht.const_add (-s / 12)).sub (tendsto_scaled_em_error hs hs1)
  simp only [add_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (scaled_kernel_eq_em_error s hN).symm

/-- The integer quadratic trace has a fourth-order density remainder. -/
theorem exists_integer_trace_error_bound {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      ‖(N : ℂ) ^ 2 * zeroPowerSumKernel s N - (N : ℂ) ^ 2 / (1 - s) - N / 2 + s / 12‖ ≤
        C / (N : ℝ) ^ 2 := by
  let q : ℂ := s * (s + 1) * (s + 2) / 720
  refine ⟨‖q‖ + emErrorConstant s, ?_, ?_⟩
  · dsimp only [emErrorConstant]
    positivity
  intro N hN
  have hn : ‖(N : ℂ)‖ = (N : ℝ) := by simp
  have he : ‖(N : ℂ) ^ (s + 1) * (riemannZeta s - zetaEulerMaclaurinMain 1 N s)‖ ≤
      emErrorConstant s / (N : ℝ) ^ 2 := by
    simpa only [Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_two, div_eq_mul_inv] using
      norm_scaled_em_error_le hs hs1 hN
  have hid : (N : ℂ) ^ 2 * zeroPowerSumKernel s N - (N : ℂ) ^ 2 / (1 - s) - N / 2 + s / 12 =
      q / (N : ℂ) ^ 2 - (N : ℂ) ^ (s + 1) *
        (riemannZeta s - zetaEulerMaclaurinMain 1 N s) := by
    rw [scaled_kernel_eq_em_error s hN]
    dsimp only [q]
    ring
  rw [hid]
  calc
    _ ≤ ‖q / (N : ℂ) ^ 2‖ +
        ‖(N : ℂ) ^ (s + 1) * (riemannZeta s - zetaEulerMaclaurinMain 1 N s)‖ := norm_sub_le _ _
    _ ≤ ‖q / (N : ℂ) ^ 2‖ + emErrorConstant s / (N : ℝ) ^ 2 := add_le_add le_rfl he
    _ = (‖q‖ + emErrorConstant s) / (N : ℝ) ^ 2 := by
      rw [norm_div, norm_pow, hn, add_div]

private theorem binomial_partial_three (a z : ℂ) :
    (binomialSeries ℂ a).partialSum 3 z = 1 + a * z + a * (a - 1) / 2 * z ^ 2 := by
  have hc := Ring.descPochhammer_eq_factorial_smul_choose a 2
  norm_num [descPochhammer_succ_right, Polynomial.smeval_mul,
    Polynomial.smeval_natCast, nsmul_eq_mul] at hc
  norm_num [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, binomialSeries]
  linear_combination -(z ^ 2 / 2) * hc

/-- The cubic Taylor remainder is uniform over a bounded unit-cell parameter. -/
theorem exists_uniform_cpow_quadratic_remainder (a : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ‖(1 + (θ : ℂ) / (N : ℂ)) ^ a -
        (1 + a * ((θ : ℂ) / (N : ℂ)) +
          a * (a - 1) / 2 * ((θ : ℂ) / (N : ℂ)) ^ 2)‖ ≤ C / (N : ℝ) ^ 3 := by
  obtain ⟨C, hC⟩ :=
    (Complex.one_add_cpow_hasFPowerSeriesAt_zero (a := a)).isBigO_sub_partialSum_pow 3 |>.bound
  have hb : ∀ᶠ z : ℂ in 𝓝 0,
      ‖(1 + z) ^ a - (1 + a * z + a * (a - 1) / 2 * z ^ 2)‖ ≤
        max C 0 * ‖z‖ ^ 3 := by
    filter_upwards [hC] with z hz
    have hz' : ‖(1 + z) ^ a - (1 + a * z + a * (a - 1) / 2 * z ^ 2)‖ ≤
        C * ‖z‖ ^ 3 := by
      simpa only [zero_add, binomial_partial_three, norm_pow, norm_norm] using hz
    exact hz'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  obtain ⟨δ, hδ, hbδ⟩ := Metric.eventually_nhds_iff.mp hb
  have hlim : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  filter_upwards [eventually_ge_atTop 1, hlim.eventually (Iio_mem_nhds hδ)] with N hN hNδ
  intro θ hθ
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hnorm : ‖(θ : ℂ) / (N : ℂ)‖ = θ / (N : ℝ) := by
    simp [abs_of_nonneg hθ.1]
  have hsmall : ‖(θ : ℂ) / (N : ℂ)‖ ≤ (N : ℝ)⁻¹ := by
    rw [hnorm, ← one_div]
    exact div_le_div_of_nonneg_right hθ.2 hn.le
  have hbound := hbδ (y := (θ : ℂ) / (N : ℂ))
    (by simpa only [dist_zero_right] using hsmall.trans_lt hNδ)
  calc
    _ ≤ max C 0 * ‖(θ : ℂ) / (N : ℂ)‖ ^ 3 := hbound
    _ ≤ max C 0 * ((N : ℝ)⁻¹) ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsmall 3) (le_max_right _ _)
    _ = max C 0 / (N : ℝ) ^ 3 := by rw [inv_pow, div_eq_mul_inv]

private theorem cpow_trace_estimates (a : ℂ) {C : ℝ} (hC : 0 ≤ C)
    {N : ℕ} (hN : 1 ≤ N) {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hT : ‖(1 + (θ : ℂ) / (N : ℂ)) ^ a -
      (1 + a * ((θ : ℂ) / (N : ℂ)) + a * (a - 1) / 2 * ((θ : ℂ) / (N : ℂ)) ^ 2)‖ ≤
        C / (N : ℝ) ^ 3) :
    let A := (1 + (θ : ℂ) / (N : ℂ)) ^ a
    let B := ‖a * (a - 1) / 2‖ + C
    ‖A‖ ≤ 1 + (‖a‖ + B) ∧
      ‖A - 1‖ ≤ (‖a‖ + B) / (N : ℝ) ∧
      ‖(N : ℂ) * (A - 1) - a * (θ : ℂ)‖ ≤ B / (N : ℝ) ∧
      ‖(N : ℂ) ^ 2 * (A - 1 - a * (θ : ℂ) / (N : ℂ)) -
        a * (a - 1) / 2 * (θ : ℂ) ^ 2‖ ≤ C / (N : ℝ) := by
  let A := (1 + (θ : ℂ) / (N : ℂ)) ^ a
  let b := a * (a - 1) / 2
  let B := ‖b‖ + C
  let Q := (N : ℂ) ^ 2 * (A - 1 - a * (θ : ℂ) / (N : ℂ))
  change ‖A‖ ≤ 1 + (‖a‖ + B) ∧ ‖A - 1‖ ≤ (‖a‖ + B) / (N : ℝ) ∧
    ‖(N : ℂ) * (A - 1) - a * (θ : ℂ)‖ ≤ B / (N : ℝ) ∧
      ‖Q - b * (θ : ℂ) ^ 2‖ ≤ C / (N : ℝ)
  have hnR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hnR
  have hnC : (N : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hn : ‖(N : ℂ)‖ = (N : ℝ) := by simp
  have hθnorm : ‖(θ : ℂ)‖ ≤ 1 := by simpa [abs_of_nonneg hθ.1] using hθ.2
  have hB : 0 ≤ B := add_nonneg (norm_nonneg _) hC
  have hdiv (x : ℝ) (hx : 0 ≤ x) : x / (N : ℝ) ≤ x := by
    apply (div_le_iff₀ hnpos).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hnR hx
  have hQerror : ‖Q - b * (θ : ℂ) ^ 2‖ ≤ C / (N : ℝ) := by
    have he : Q - b * (θ : ℂ) ^ 2 = (N : ℂ) ^ 2 *
        (A - (1 + a * ((θ : ℂ) / (N : ℂ)) + b * ((θ : ℂ) / (N : ℂ)) ^ 2)) := by
      dsimp only [Q]
      field_simp [hnC]
      ring
    rw [he, norm_mul, norm_pow, hn]
    calc
      _ ≤ (N : ℝ) ^ 2 * (C / (N : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hT (sq_nonneg _)
      _ = C / (N : ℝ) := by field_simp [hnpos.ne']
  have hbθ : ‖b * (θ : ℂ) ^ 2‖ ≤ ‖b‖ := by
    rw [norm_mul, norm_pow]
    have hp := pow_le_pow_left₀ (norm_nonneg (θ : ℂ)) hθnorm 2
    simpa only [one_pow, mul_one] using mul_le_mul_of_nonneg_left hp (norm_nonneg b)
  have hQ : ‖Q‖ ≤ B := by
    calc
      ‖Q‖ = ‖(Q - b * (θ : ℂ) ^ 2) + b * (θ : ℂ) ^ 2‖ := by congr 1; ring
      _ ≤ ‖Q - b * (θ : ℂ) ^ 2‖ + ‖b * (θ : ℂ) ^ 2‖ := norm_add_le _ _
      _ ≤ C / (N : ℝ) + ‖b‖ := add_le_add hQerror hbθ
      _ ≤ C + ‖b‖ := add_le_add (hdiv C hC) le_rfl
      _ = B := by dsimp only [B]; ring
  have hL : ‖(N : ℂ) * (A - 1) - a * (θ : ℂ)‖ ≤ B / (N : ℝ) := by
    have he : (N : ℂ) * (A - 1) - a * (θ : ℂ) = Q / (N : ℂ) := by
      dsimp only [Q]
      field_simp [hnC]
    rw [he, norm_div, hn]
    exact div_le_div_of_nonneg_right hQ hnpos.le
  have haθ : ‖a * (θ : ℂ)‖ ≤ ‖a‖ := by
    rw [norm_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hθnorm (norm_nonneg a)
  have hLnorm : ‖(N : ℂ) * (A - 1)‖ ≤ ‖a‖ + B := by
    calc
      _ = ‖((N : ℂ) * (A - 1) - a * (θ : ℂ)) + a * (θ : ℂ)‖ := by congr 1; ring
      _ ≤ ‖(N : ℂ) * (A - 1) - a * (θ : ℂ)‖ + ‖a * (θ : ℂ)‖ := norm_add_le _ _
      _ ≤ B / (N : ℝ) + ‖a‖ := add_le_add hL haθ
      _ ≤ B + ‖a‖ := add_le_add (hdiv B hB) le_rfl
      _ = ‖a‖ + B := add_comm _ _
  have hAone : ‖A - 1‖ ≤ (‖a‖ + B) / (N : ℝ) := by
    apply (le_div_iff₀ hnpos).mpr
    simpa only [norm_mul, hn, mul_comm] using hLnorm
  refine ⟨?_, hAone, hL, hQerror⟩
  calc
    ‖A‖ = ‖1 + (A - 1)‖ := by congr 1; ring
    _ ≤ ‖(1 : ℂ)‖ + ‖A - 1‖ := norm_add_le _ _
    _ ≤ 1 + (‖a‖ + B) / (N : ℝ) := by simpa only [norm_one] using add_le_add (le_refl (1 : ℝ)) hAone
    _ ≤ 1 + (‖a‖ + B) := add_le_add le_rfl (hdiv _ (add_nonneg (norm_nonneg _) hB))

private theorem tendsto_cpow_quadratic_trace (a θ : ℂ) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ 2 *
      ((1 + θ / (N : ℂ)) ^ a - 1 - a * θ / (N : ℂ)))
      atTop (𝓝 (a * (a - 1) / 2 * θ ^ 2)) := by
  have hw : Tendsto (fun N : ℕ => θ / (N : ℂ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_complex_nat_inv.const_mul θ
  obtain ⟨C, hC⟩ :=
    (Complex.one_add_cpow_hasFPowerSeriesAt_zero (a := a)).isBigO_sub_partialSum_pow 3 |>.bound
  have hb : ∀ᶠ z : ℂ in 𝓝 0,
      ‖(1 + z) ^ a - (1 + a * z + a * (a - 1) / 2 * z ^ 2)‖ ≤ C * ‖z‖ ^ 3 := by
    filter_upwards [hC] with z hz
    simpa only [zero_add, binomial_partial_three, norm_pow, norm_norm] using hz
  have hlim : Tendsto (fun N : ℕ => C * ‖θ‖ ^ 3 / (N : ℝ)) atTop (𝓝 0) := by
    have h := ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (C * ‖θ‖ ^ 3)
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using h
  have hr : Tendsto (fun N : ℕ => (N : ℂ) ^ 2 *
      ((1 + θ / (N : ℂ)) ^ a - (1 + a * (θ / (N : ℂ)) +
        a * (a - 1) / 2 * (θ / (N : ℂ)) ^ 2))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hlim
    filter_upwards [hw.eventually hb, eventually_ge_atTop 1] with N hN hNpos
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    have hnorm : ‖(N : ℂ)‖ = (N : ℝ) := by simp
    rw [norm_mul, norm_pow, hnorm]
    calc
      _ ≤ (N : ℝ) ^ 2 * (C * ‖θ / (N : ℂ)‖ ^ 3) :=
        mul_le_mul_of_nonneg_left hN (sq_nonneg _)
      _ = C * ‖θ‖ ^ 3 / (N : ℝ) := by
        rw [norm_div, hnorm]
        field_simp [hn]
  have h := hr.const_add (a * (a - 1) / 2 * θ ^ 2)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  field_simp [hn]
  ring

private theorem tendsto_cpow_linear_trace (a θ : ℂ) :
    Tendsto (fun N : ℕ => (N : ℂ) * ((1 + θ / (N : ℂ)) ^ a - 1))
      atTop (𝓝 (a * θ)) := by
  have h := ((tendsto_cpow_quadratic_trace a θ).mul tendsto_complex_nat_inv).add_const (a * θ)
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  field_simp [hn]
  ring

/-- The same ordinary power sum evaluated inside the next unit cell. -/
def zeroPowerSumCellKernel (s : ℂ) (N : ℕ) (θ : ℝ) : ℂ :=
  ((N : ℂ) + (θ : ℂ)) ^ (s - 1) *
    ((∑ n ∈ Icc 1 N, (n : ℂ) ^ (-s)) - riemannZeta s)

private theorem cell_kernel_factor (s : ℂ) {N : ℕ} (hN : 1 ≤ N)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    zeroPowerSumCellKernel s N θ =
      (1 + (θ : ℂ) / (N : ℂ)) ^ (s - 1) * zeroPowerSumKernel s N := by
  have hnR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hnC : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hbase : (N : ℂ) + (θ : ℂ) =
      (((1 + θ / (N : ℝ) : ℝ) : ℂ) * ((N : ℝ) : ℂ)) := by
    push_cast
    field_simp [hnC]
  rw [zeroPowerSumCellKernel, hbase,
    Complex.mul_cpow_ofReal_nonneg (by positivity : 0 ≤ 1 + θ / (N : ℝ)) hnR.le]
  push_cast
  rw [zeroPowerSumKernel]
  ring

/-- The quadratic endpoint trace at every fixed position of a unit cell. -/
theorem tendsto_zeroPowerSumCellKernel_trace {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) {θ : ℝ} (hθ : 0 ≤ θ) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ 2 * zeroPowerSumCellKernel s N θ -
      (N : ℂ) ^ 2 / (1 - s) - (1 / 2 - (θ : ℂ)) * (N : ℂ)) atTop
      (𝓝 (-s / 12 + (s - 1) * (θ : ℂ) / 2 - (s - 2) * (θ : ℂ) ^ 2 / 2)) := by
  have hw : Tendsto (fun N : ℕ => (θ : ℂ) / (N : ℂ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_complex_nat_inv.const_mul (θ : ℂ)
  have hA : Tendsto (fun N : ℕ => (1 + (θ : ℂ) / (N : ℂ)) ^ (s - 1)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using
      (Complex.one_add_cpow_hasFPowerSeriesAt_zero (a := s - 1)).continuousAt.tendsto.comp hw
  have h := ((hA.mul (tendsto_zeroPowerSumKernel_integer_trace hs hs1)).add
    ((tendsto_cpow_quadratic_trace (s - 1) (θ : ℂ)).const_mul (1 / (1 - s)))).add
      ((tendsto_cpow_linear_trace (s - 1) (θ : ℂ)).const_mul (1 / 2))
  have hden : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hvalue : 1 * (-s / 12) + 1 / (1 - s) *
      ((s - 1) * (s - 1 - 1) / 2 * (θ : ℂ) ^ 2) + 1 / 2 * ((s - 1) * (θ : ℂ)) =
      -s / 12 + (s - 1) * (θ : ℂ) / 2 - (s - 2) * (θ : ℂ) ^ 2 / 2 := by
    field_simp [hden]
    ring
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [cell_kernel_factor s hN hθ]
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  field_simp [hn, hden]
  ring

/-- The residual after the constant, linear and quadratic cell terms are removed. -/
def zeroPowerSumCellRemainder (s : ℂ) (N : ℕ) (θ : ℝ) : ℂ :=
  (N : ℂ) ^ 2 * zeroPowerSumCellKernel s N θ - (N : ℂ) ^ 2 / (1 - s) -
    (1 / 2 - (θ : ℂ)) * (N : ℂ) -
      (-s / 12 + (s - 1) * (θ : ℂ) / 2 - (s - 2) * (θ : ℂ) ^ 2 / 2)

/-- The quadratic cell trace is uniform, with an explicit extra inverse power. -/
theorem exists_uniform_zeroPowerSumCell_remainder {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ‖zeroPowerSumCellRemainder s N θ‖ ≤ C / (N : ℝ) := by
  obtain ⟨Ce, hCe, he⟩ := exists_integer_trace_error_bound hs hs1
  obtain ⟨Ct, hCt, ht⟩ := exists_uniform_cpow_quadratic_remainder (s - 1)
  let B : ℝ := ‖(s - 1) * (s - 1 - 1) / 2‖ + Ct
  let D : ℝ := ‖s - 1‖ + B
  have hB : 0 ≤ B := add_nonneg (norm_nonneg _) hCt
  have hD : 0 ≤ D := add_nonneg (norm_nonneg _) hB
  refine ⟨(1 + D) * Ce + ‖-s / 12‖ * D + ‖1 / (1 - s)‖ * Ct + ‖(1 / 2 : ℂ)‖ * B,
    by positivity, ?_⟩
  filter_upwards [ht, eventually_ge_atTop 1] with N hT hN
  intro θ hθ
  obtain ⟨hA, hAone, hL, hQ⟩ := cpow_trace_estimates (s - 1) hCt hN hθ (hT θ hθ)
  let A : ℂ := (1 + (θ : ℂ) / (N : ℂ)) ^ (s - 1)
  let E : ℂ := (N : ℂ) ^ 2 * zeroPowerSumKernel s N - (N : ℂ) ^ 2 / (1 - s) - N / 2 + s / 12
  let Q : ℂ := (N : ℂ) ^ 2 * (A - 1 - (s - 1) * (θ : ℂ) / (N : ℂ)) -
    (s - 1) * (s - 1 - 1) / 2 * (θ : ℂ) ^ 2
  let L : ℂ := (N : ℂ) * (A - 1) - (s - 1) * (θ : ℂ)
  change ‖A‖ ≤ 1 + D at hA
  change ‖A - 1‖ ≤ D / (N : ℝ) at hAone
  change ‖L‖ ≤ B / (N : ℝ) at hL
  change ‖Q‖ ≤ Ct / (N : ℝ) at hQ
  have hnR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hnR
  have hnC : (N : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hden : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hn2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hnR, sq_nonneg ((N : ℝ) - 1)]
  have he' : ‖E‖ ≤ Ce / (N : ℝ) :=
    (he N hN).trans (div_le_div_of_nonneg_left hCe hnpos hn2)
  have hAE : ‖A * E‖ ≤ (1 + D) * (Ce / (N : ℝ)) := by
    rw [norm_mul]
    exact mul_le_mul hA he' (norm_nonneg E) (by positivity)
  have hA₁ : ‖(-s / 12) * (A - 1)‖ ≤ ‖-s / 12‖ * (D / (N : ℝ)) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hAone (norm_nonneg _)
  have hQ₁ : ‖(1 / (1 - s)) * Q‖ ≤ ‖1 / (1 - s)‖ * (Ct / (N : ℝ)) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hQ (norm_nonneg _)
  have hL₁ : ‖(1 / 2 : ℂ) * L‖ ≤ ‖(1 / 2 : ℂ)‖ * (B / (N : ℝ)) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hL (norm_nonneg _)
  have hid : zeroPowerSumCellRemainder s N θ =
      A * E + (-s / 12) * (A - 1) + (1 / (1 - s)) * Q + (1 / 2 : ℂ) * L := by
    rw [zeroPowerSumCellRemainder, cell_kernel_factor s hN hθ.1]
    dsimp only [A, E, Q, L]
    field_simp [hnC, hden]
    ring
  rw [hid]
  calc
    _ ≤ ‖A * E + (-s / 12) * (A - 1) + (1 / (1 - s)) * Q‖ + ‖(1 / 2 : ℂ) * L‖ :=
      norm_add_le _ _
    _ ≤ (‖A * E + (-s / 12) * (A - 1)‖ + ‖(1 / (1 - s)) * Q‖) + ‖(1 / 2 : ℂ) * L‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ((‖A * E‖ + ‖(-s / 12) * (A - 1)‖) + ‖(1 / (1 - s)) * Q‖) + ‖(1 / 2 : ℂ) * L‖ :=
      add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ ≤ ((1 + D) * (Ce / (N : ℝ)) + ‖-s / 12‖ * (D / (N : ℝ))) +
        ‖1 / (1 - s)‖ * (Ct / (N : ℝ)) + ‖(1 / 2 : ℂ)‖ * (B / (N : ℝ)) :=
      add_le_add (add_le_add (add_le_add hAE hA₁) hQ₁) hL₁
    _ = _ := by ring

/-- The second Bernoulli polynomial on a unit cell. -/
def unitCellBernoulli (θ : ℝ) : ℝ := θ ^ 2 - θ + 1 / 6

/-- The real density kernel for a conjugate pair of critical-line poles. -/
def criticalPairCellKernel (γ : ℝ) (N : ℕ) (θ : ℝ) : ℝ :=
  (zeroPowerSumCellKernel (1 / 2 + (γ : ℂ) * I) N θ).im / γ

/-- The quadratic cell trace of a conjugate pair is independent of its ordinate. -/
theorem tendsto_criticalPairCellKernel_trace {γ : ℝ} (hγ : γ ≠ 0)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * criticalPairCellKernel γ N θ -
      (N : ℝ) ^ 2 / (1 / 4 + γ ^ 2)) atTop (𝓝 (-unitCellBernoulli θ / 2)) := by
  let s : ℂ := 1 / 2 + (γ : ℂ) * I
  have hs : 0 < s.re := by norm_num [s]
  have hs1 : s ≠ 1 := by
    intro he
    have := congrArg Complex.re he
    norm_num [s] at this
  have h := ((Complex.continuous_im.tendsto _).comp
    (tendsto_zeroPowerSumCellKernel_trace hs hs1 hθ)).div_const γ
  have him : ((1 - s)⁻¹).im = γ / (1 / 4 + γ ^ 2) := by
    dsimp only [s]
    simp [Complex.normSq_apply]
    ring
  have hv : (-s / 12 + (s - 1) * (θ : ℂ) / 2 - (s - 2) * (θ : ℂ) ^ 2 / 2).im / γ =
      -unitCellBernoulli θ / 2 := by
    dsimp only [s, unitCellBernoulli]
    simp [pow_two]
    field_simp [hγ]
    ring
  rw [hv] at h
  apply h.congr
  intro N
  dsimp only [Function.comp_apply, criticalPairCellKernel]
  simp [pow_two, Complex.mul_im, Complex.mul_re, div_eq_mul_inv, him]
  dsimp only [s]
  field_simp [hγ]

private theorem criticalPairCell_remainder_eq {γ : ℝ} (hγ : γ ≠ 0) (N : ℕ) (θ : ℝ) :
    (zeroPowerSumCellRemainder (1 / 2 + (γ : ℂ) * I) N θ).im / γ =
      (N : ℝ) ^ 2 * criticalPairCellKernel γ N θ - (N : ℝ) ^ 2 / (1 / 4 + γ ^ 2) +
        unitCellBernoulli θ / 2 := by
  let s : ℂ := 1 / 2 + (γ : ℂ) * I
  have him : ((1 - s)⁻¹).im = γ / (1 / 4 + γ ^ 2) := by
    dsimp only [s]
    simp [Complex.normSq_apply]
    ring
  have hsim : s.im = γ := by simp [s]
  change (zeroPowerSumCellRemainder s N θ).im / γ = _
  dsimp only [zeroPowerSumCellRemainder, criticalPairCellKernel, unitCellBernoulli]
  simp [pow_two, Complex.mul_im, Complex.mul_re, div_eq_mul_inv, him, hsim]
  dsimp only [s]
  field_simp [hγ]
  ring

/-- The Bernoulli trace of a conjugate pair has a uniform remainder on the whole cell. -/
theorem exists_uniform_criticalPairCell_remainder {γ : ℝ} (hγ : γ ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      |(N : ℝ) ^ 2 * criticalPairCellKernel γ N θ - (N : ℝ) ^ 2 / (1 / 4 + γ ^ 2) +
        unitCellBernoulli θ / 2| ≤ C / (N : ℝ) := by
  let s : ℂ := 1 / 2 + (γ : ℂ) * I
  have hs : 0 < s.re := by norm_num [s]
  have hs1 : s ≠ 1 := by
    intro he
    have he' := congrArg Complex.re he
    norm_num [s] at he'
  obtain ⟨C, hC, hb⟩ := exists_uniform_zeroPowerSumCell_remainder hs hs1
  refine ⟨C / |γ|, div_nonneg hC (abs_nonneg _), ?_⟩
  filter_upwards [hb] with N hN
  intro θ hθ
  rw [← criticalPairCell_remainder_eq hγ, abs_div]
  calc
    _ ≤ ‖zeroPowerSumCellRemainder s N θ‖ / |γ| :=
      div_le_div_of_nonneg_right (Complex.abs_im_le_norm _) (abs_nonneg _)
    _ ≤ (C / (N : ℝ)) / |γ| := div_le_div_of_nonneg_right (hN θ hθ) (abs_nonneg _)
    _ = (C / |γ|) / (N : ℝ) := by ring

/-- The normalized difference of two conjugate-pair density kernels. -/
def quartetCellDefect (γ₁ γ₂ c : ℝ) (N : ℕ) (θ : ℝ) : ℝ :=
  c / (γ₂ ^ 2 - γ₁ ^ 2) *
    ((γ₂ ^ 2 + 1 / 4) * criticalPairCellKernel γ₂ N θ -
      (γ₁ ^ 2 + 1 / 4) * criticalPairCellKernel γ₁ N θ)

/-- Normalization removes the constant terms and leaves precisely the quadratic
trace times the Bernoulli polynomial. -/
theorem tendsto_quartetCellDefect_trace {γ₁ γ₂ : ℝ}
    (hγ₁ : 0 < γ₁) (hγ₂ : γ₁ < γ₂) (c : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * quartetCellDefect γ₁ γ₂ c N θ)
      atTop (𝓝 (-c * unitCellBernoulli θ / 2)) := by
  have h₂ : 0 < γ₂ := hγ₁.trans hγ₂
  have hd : γ₂ ^ 2 - γ₁ ^ 2 ≠ 0 := by
    have hp := mul_pos (sub_pos.mpr hγ₂) (add_pos h₂ hγ₁)
    nlinarith only [hp]
  have h := (((tendsto_criticalPairCellKernel_trace h₂.ne' hθ).const_mul (γ₂ ^ 2 + 1 / 4)).sub
    ((tendsto_criticalPairCellKernel_trace hγ₁.ne' hθ).const_mul (γ₁ ^ 2 + 1 / 4))).const_mul
      (c / (γ₂ ^ 2 - γ₁ ^ 2))
  have hv : c / (γ₂ ^ 2 - γ₁ ^ 2) *
      ((γ₂ ^ 2 + 1 / 4) * (-unitCellBernoulli θ / 2) -
        (γ₁ ^ 2 + 1 / 4) * (-unitCellBernoulli θ / 2)) =
      -c * unitCellBernoulli θ / 2 := by
    field_simp [hd]
    ring
  rw [hv] at h
  apply h.congr
  intro N
  dsimp only [quartetCellDefect]
  have h₁d : 1 / 4 + γ₁ ^ 2 ≠ 0 := by positivity
  have h₂d : 1 / 4 + γ₂ ^ 2 ≠ 0 := by positivity
  field_simp [hd, h₁d, h₂d]
  ring

/-- The signed quartet density has a uniform Bernoulli profile, with cubic density error. -/
theorem exists_uniform_quartetCellDefect_remainder {γ₁ γ₂ : ℝ}
    (hγ₁ : 0 < γ₁) (hγ₂ : γ₁ < γ₂) (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      |(N : ℝ) ^ 2 * quartetCellDefect γ₁ γ₂ c N θ + c * unitCellBernoulli θ / 2| ≤
        C / (N : ℝ) := by
  have h₂ : 0 < γ₂ := hγ₁.trans hγ₂
  obtain ⟨C₁, hC₁, h₁⟩ := exists_uniform_criticalPairCell_remainder hγ₁.ne'
  obtain ⟨C₂, hC₂, h₂b⟩ := exists_uniform_criticalPairCell_remainder h₂.ne'
  let w₁ : ℝ := γ₁ ^ 2 + 1 / 4
  let w₂ : ℝ := γ₂ ^ 2 + 1 / 4
  have hw₁ : 0 ≤ w₁ := by dsimp only [w₁]; positivity
  have hw₂ : 0 ≤ w₂ := by dsimp only [w₂]; positivity
  let q : ℝ := c / (γ₂ ^ 2 - γ₁ ^ 2)
  have hd : γ₂ ^ 2 - γ₁ ^ 2 ≠ 0 := by
    have hp := mul_pos (sub_pos.mpr hγ₂) (add_pos h₂ hγ₁)
    nlinarith only [hp]
  refine ⟨|q| * (w₂ * C₂ + w₁ * C₁), by positivity, ?_⟩
  filter_upwards [h₁, h₂b] with N hN₁ hN₂
  intro θ hθ
  let E₁ := (N : ℝ) ^ 2 * criticalPairCellKernel γ₁ N θ -
    (N : ℝ) ^ 2 / (1 / 4 + γ₁ ^ 2) + unitCellBernoulli θ / 2
  let E₂ := (N : ℝ) ^ 2 * criticalPairCellKernel γ₂ N θ -
    (N : ℝ) ^ 2 / (1 / 4 + γ₂ ^ 2) + unitCellBernoulli θ / 2
  have hid : (N : ℝ) ^ 2 * quartetCellDefect γ₁ γ₂ c N θ + c * unitCellBernoulli θ / 2 =
      q * (w₂ * E₂ - w₁ * E₁) := by
    have hd₁ : 1 / 4 + γ₁ ^ 2 ≠ 0 := by positivity
    have hd₂ : 1 / 4 + γ₂ ^ 2 ≠ 0 := by positivity
    dsimp only [quartetCellDefect, q, w₁, w₂, E₁, E₂]
    field_simp [hd, hd₁, hd₂]
    ring
  rw [hid, abs_mul]
  have he : |w₂ * E₂ - w₁ * E₁| ≤ w₂ * |E₂| + w₁ * |E₁| := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw₁, abs_of_nonneg hw₂] using
      norm_sub_le (w₂ * E₂) (w₁ * E₁)
  calc
    _ ≤ |q| * (w₂ * |E₂| + w₁ * |E₁|) := mul_le_mul_of_nonneg_left he (abs_nonneg _)
    _ ≤ |q| * (w₂ * (C₂ / (N : ℝ)) + w₁ * (C₁ / (N : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact add_le_add (mul_le_mul_of_nonneg_left (hN₂ θ hθ) hw₂)
        (mul_le_mul_of_nonneg_left (hN₁ θ hθ) hw₁)
    _ = _ := by ring

/-- The normalized density has opposite limiting traces at integers and midpoints. -/
theorem quartetCellDefect_endpoint_traces {γ₁ γ₂ : ℝ}
    (hγ₁ : 0 < γ₁) (hγ₂ : γ₁ < γ₂) (c : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * quartetCellDefect γ₁ γ₂ c N 0)
      atTop (𝓝 (-c / 12)) ∧
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * quartetCellDefect γ₁ γ₂ c N (1 / 2))
      atTop (𝓝 (c / 24)) := by
  constructor
  · convert tendsto_quartetCellDefect_trace hγ₁ hγ₂ c (θ := 0) le_rfl using 1
    norm_num [unitCellBernoulli]
    ring
  · convert tendsto_quartetCellDefect_trace hγ₁ hγ₂ c
      (θ := 1 / 2) (by norm_num) using 1
    norm_num [unitCellBernoulli]
    ring

/-- A negative quadratic trace forces a sign change in every sufficiently large cell. -/
theorem eventually_quartetCellDefect_opposite_signs {γ₁ γ₂ c : ℝ}
    (hγ₁ : 0 < γ₁) (hγ₂ : γ₁ < γ₂) (hc : c < 0) :
    ∀ᶠ N : ℕ in atTop, 0 < quartetCellDefect γ₁ γ₂ c N 0 ∧
      quartetCellDefect γ₁ γ₂ c N (1 / 2) < 0 := by
  obtain ⟨h₀, hhalf⟩ := quartetCellDefect_endpoint_traces hγ₁ hγ₂ c
  have hp : 0 < -c / 12 := by linarith only [hc]
  have hn : c / 24 < 0 := by linarith only [hc]
  filter_upwards [h₀.eventually (Ioi_mem_nhds hp), hhalf.eventually (Iio_mem_nhds hn)]
    with N hN₀ hNhalf
  constructor
  · by_contra h
    have hprod := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (N : ℝ)) (le_of_not_gt h)
    exact not_lt_of_ge hprod hN₀
  · by_contra h
    have hprod := mul_nonneg (sq_nonneg (N : ℝ)) (le_of_not_gt h)
    exact not_lt_of_ge hprod hNhalf

#print axioms tendsto_zeroPowerSumCellKernel_trace
#print axioms tendsto_quartetCellDefect_trace
#print axioms exists_uniform_quartetCellDefect_remainder
#print axioms eventually_quartetCellDefect_opposite_signs

end GaloisForLFunctions.ArithmeticPositiveDuality
