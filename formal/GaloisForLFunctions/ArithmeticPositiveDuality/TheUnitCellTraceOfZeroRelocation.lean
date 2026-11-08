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

private theorem tendsto_scaled_em_error {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ (s + 1) *
      (riemannZeta s - zetaEulerMaclaurinMain 1 N s)) atTop (𝓝 0) := by
  let C : ℝ := |((bernoulli 4 : ℚ) : ℝ)| / 24 *
    ‖complexRisingFactor s 4‖ / (s.re + 3)
  have hlim : Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-(2 : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul C
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hb := norm_riemannZeta_sub_zetaEulerMaclaurinMain_le hs hs1 hN 1
  norm_num only [Nat.reduceAdd, Nat.reduceMul, Nat.factorial, Nat.cast_ofNat] at hb
  have hb' : ‖riemannZeta s - zetaEulerMaclaurinMain 1 N s‖ ≤
      C * (N : ℝ) ^ (-s.re - 3) := by
    convert hb using 1
    dsimp only [C]
    rw [show 1 - s.re - 4 = -s.re - 3 by ring]
    ring
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega),
    Complex.add_re, Complex.one_re]
  calc
    _ ≤ (N : ℝ) ^ (s.re + 1) * (C * (N : ℝ) ^ (-s.re - 3)) :=
      mul_le_mul_of_nonneg_left hb' (Real.rpow_nonneg hNpos.le _)
    _ = C * (N : ℝ) ^ (-(2 : ℝ)) := by
      rw [mul_left_comm, ← Real.rpow_add hNpos]
      congr 2
      ring

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

private theorem binomial_partial_three (a z : ℂ) :
    (binomialSeries ℂ a).partialSum 3 z = 1 + a * z + a * (a - 1) / 2 * z ^ 2 := by
  have hc := Ring.descPochhammer_eq_factorial_smul_choose a 2
  norm_num [descPochhammer_succ_right, Polynomial.smeval_mul,
    Polynomial.smeval_natCast, nsmul_eq_mul] at hc
  norm_num [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, binomialSeries]
  linear_combination -(z ^ 2 / 2) * hc

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
  ring

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

end GaloisForLFunctions.ArithmeticPositiveDuality
