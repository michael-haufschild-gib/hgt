import GaloisForLFunctions.RHTower.ComplexEulerMaclaurin
import GaloisForLFunctions.RHTower.ZetaPartialSumStrip

/-!
# Arbitrary-order Euler–Maclaurin estimates for the zeta series

The derivative factor is retained explicitly. Increasing the order makes the
remainder small when the truncation length is a power of the vertical height
strictly larger than one. This is needed for mean-square limits arbitrarily
close to the critical line.
-/

open Complex Filter Topology MeasureTheory Set

noncomputable section

namespace RHTower

def complexRisingFactor (s : ℂ) (j : ℕ) : ℂ :=
  ∏ i ∈ Finset.range j, (s + i)

def complexPowerTower (s : ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  (-1 : ℂ) ^ j * complexRisingFactor s j * (x : ℂ) ^ (-s - j)

@[simp] theorem complexPowerTower_zero (s : ℂ) (x : ℝ) :
    complexPowerTower s 0 x = (x : ℂ) ^ (-s) := by
  simp [complexPowerTower, complexRisingFactor]

theorem complexPowerTower_isTower {s : ℂ} (hs : 0 < s.re) :
    ComplexDerivTower (complexPowerTower s) (Ioi 0) := by
  intro j x hx
  have hexp : -s - (j : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re, Complex.zero_re] at hre
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have h := (hasDerivAt_ofReal_cpow_const (ne_of_gt hx) hexp).const_mul
    ((-1 : ℂ) ^ j * complexRisingFactor s j)
  refine h.congr_deriv ?_
  simp only [complexPowerTower, complexRisingFactor, Finset.prod_range_succ, pow_succ,
    Nat.cast_add, Nat.cast_one]
  rw [show -s - ((j : ℂ) + 1) = -s - j - 1 by ring]
  ring

theorem norm_complexPowerTower (s : ℂ) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖complexPowerTower s j x‖ = ‖complexRisingFactor s j‖ * x ^ (-s.re - j) := by
  rw [complexPowerTower, norm_mul, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]

/-- A uniform remainder bound over any number of cells. The bound depends only
on the lower endpoint, the exponent, and the chosen even order. -/
theorem norm_sum_complexPowerTower_EMCell_le {s : ℂ} (hs : 0 < s.re)
    {a : ℝ} (ha : 0 < a) (N : ℕ) {k : ℕ} (hk : k ≠ 0) :
    ‖∑ n ∈ Finset.range N, complexEMCell (complexPowerTower s) (2 * k) (a + n)‖ ≤
      |((bernoulli (2 * k) : ℚ) : ℝ)| / (((2 * k).factorial : ℕ) : ℝ) *
        ‖complexRisingFactor s (2 * k)‖ *
          (a ^ (1 - s.re - (2 * k : ℕ)) / (s.re + (2 * k : ℕ) - 1)) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hk2 : (2 : ℝ) ≤ (2 * k : ℕ) := by exact_mod_cast (by omega : 2 ≤ 2 * k)
  have hden : 0 < s.re + (2 * k : ℕ) - 1 := by linarith
  have hF : ComplexDerivTower (complexPowerTower s) (Icc a (a + N)) :=
    (complexPowerTower_isTower hs).mono fun x hx => lt_of_lt_of_le ha hx.1
  have hbound := norm_sum_complexEMCell_le N hF hk
  have hint : (∫ x in a..(a + N), ‖complexPowerTower s (2 * k) x‖) =
      ‖complexRisingFactor s (2 * k)‖ *
        ((a + N) ^ (1 - s.re - (2 * k : ℕ)) - a ^ (1 - s.re - (2 * k : ℕ))) /
          (1 - s.re - (2 * k : ℕ)) := by
    have hfun : (∫ x in a..(a + N), ‖complexPowerTower s (2 * k) x‖) =
        ∫ x in a..(a + N), ‖complexRisingFactor s (2 * k)‖ *
          x ^ (-s.re - (2 * k : ℕ)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by linarith : a ≤ a + N)] at hx
      exact norm_complexPowerTower s (2 * k) (lt_of_lt_of_le ha hx.1)
    rw [hfun, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inr ⟨by linarith, by
        rw [uIcc_of_le (by linarith)]
        intro h
        linarith [h.1]⟩)]
    rw [show -s.re - ((2 * k : ℕ) : ℝ) + 1 = 1 - s.re - (2 * k : ℕ) by ring]
    ring
  rw [hint] at hbound
  have hquot :
      ((a + N) ^ (1 - s.re - (2 * k : ℕ)) - a ^ (1 - s.re - (2 * k : ℕ))) /
          (1 - s.re - (2 * k : ℕ)) ≤
        a ^ (1 - s.re - (2 * k : ℕ)) / (s.re + (2 * k : ℕ) - 1) := by
    rw [show 1 - s.re - ((2 * k : ℕ) : ℝ) = -(s.re + (2 * k : ℕ) - 1) by ring,
      div_neg, neg_div', neg_sub]
    apply div_le_div_of_nonneg_right _ hden.le
    have : 0 ≤ (a + N) ^ (-(s.re + (2 * k : ℕ) - 1)) := by positivity
    linarith
  refine hbound.trans ?_
  have hscale := mul_le_mul_of_nonneg_left hquot
    (mul_nonneg (by positivity : 0 ≤
      |((bernoulli (2 * k) : ℚ) : ℝ)| / (((2 * k).factorial : ℕ) : ℝ))
      (norm_nonneg (complexRisingFactor s (2 * k))))
  convert hscale using 1
  ring

theorem tendsto_complexPowerTower_atTop {s : ℂ} (hs : 0 < s.re) (j : ℕ) :
    Tendsto (complexPowerTower s j) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hj : 0 < s.re + j := by positivity
  have h := (tendsto_rpow_neg_atTop hj).const_mul ‖complexRisingFactor s j‖
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [norm_complexPowerTower s j hx]
  congr 2
  ring

/-- The finite collection of endpoint corrections at the chosen order. -/
def zetaEMBoundary (m : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-s) / 2 +
    ∑ r ∈ Finset.range (m + 1),
      (((bernoulli (2 * r + 2) : ℚ) : ℝ) / ((2 * r + 2).factorial : ℝ) : ℝ) *
        complexPowerTower s (2 * r + 1) x

/-- The zeta head, pole correction, and all endpoint corrections. -/
def zetaEulerMaclaurinMain (m N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) -
    (N : ℂ) ^ (1 - s) / (1 - s) - zetaEMBoundary m s N

theorem tendsto_zetaEMBoundary_atTop {s : ℂ} (hs : 0 < s.re) (m : ℕ) :
    Tendsto (zetaEMBoundary m s) atTop (𝓝 0) := by
  have h0 := (tendsto_complexPowerTower_atTop hs 0).div_const (2 : ℂ)
  simp only [complexPowerTower_zero, zero_div] at h0
  have hsum := tendsto_finsetSum (Finset.range (m + 1)) fun r _ =>
    (tendsto_complexPowerTower_atTop hs (2 * r + 1)).const_mul
      ((((bernoulli (2 * r + 2) : ℚ) : ℝ) / ((2 * r + 2).factorial : ℝ) : ℝ) : ℂ)
  change Tendsto (fun x => zetaEMBoundary m s x) atTop (𝓝 0)
  simpa only [mul_zero, Finset.sum_const_zero, add_zero, zetaEMBoundary] using h0.add hsum

private theorem sum_Icc_one_add_tail (f : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 (N + M), f n) =
      (∑ n ∈ Finset.Icc 1 N, f n) +
        (∑ n ∈ Finset.range (M + 1), f (N + n)) - f N := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [show N + (M + 1) = (N + M) + 1 by omega,
        Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
      ring

theorem zetaEulerMaclaurin_finite_tail {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) (m M : ℕ) :
    (∑ n ∈ Finset.Icc 1 (N + M), (n : ℂ) ^ (-s)) -
        ((N + M : ℕ) : ℂ) ^ (1 - s) / (1 - s) -
        zetaEulerMaclaurinMain m N s - zetaEMBoundary m s (N + M : ℕ) =
      -(∑ n ∈ Finset.range M,
        complexEMCell (complexPowerTower s) (2 * m + 2) ((N : ℝ) + n)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hF : ComplexDerivTower (complexPowerTower s) (Icc (N : ℝ) (N + M)) :=
    (complexPowerTower_isTower hs).mono fun x hx => lt_of_lt_of_le hN0 hx.1
  have h := complex_euler_maclaurin m M hF
  simp only [complexPowerTower_zero] at h
  rw [integral_cpow (Or.inr ⟨by intro h; apply hs1; linear_combination -h, by
    rw [uIcc_of_le (by linarith : (N : ℝ) ≤ N + M)]
    intro hx
    linarith [hx.1]⟩)] at h
  rw [show -s + 1 = 1 - s by ring, sub_div] at h
  simp_rw [mul_sub] at h
  rw [Finset.sum_sub_distrib] at h
  rw [zetaEulerMaclaurinMain, sum_Icc_one_add_tail (fun n => (n : ℂ) ^ (-s)) hN M]
  simp only [zetaEMBoundary]
  push_cast at h ⊢
  linear_combination h

/-- Zeta's arbitrary-order Euler–Maclaurin estimate. All hypotheses only specify
the natural domain, the positive cutoff, and the freely chosen order. -/
theorem norm_riemannZeta_sub_zetaEulerMaclaurinMain_le
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) (m : ℕ) :
    ‖riemannZeta s - zetaEulerMaclaurinMain m N s‖ ≤
      |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / ((2 * m + 2).factorial : ℝ) *
        ‖complexRisingFactor s (2 * m + 2)‖ *
          ((N : ℝ) ^ (1 - s.re - (2 * m + 2 : ℕ)) /
            (s.re + (2 * m + 2 : ℕ) - 1)) := by
  have hNat : Tendsto (fun M : ℕ => N + M) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat N
  have hReal : Tendsto (fun M : ℕ => ((N + M : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hNat
  have hsum := (tendsto_sum_cpow_sub_pow hs hs1).comp hNat
  have hb := (tendsto_zetaEMBoundary_atTop hs m).comp hReal
  have hlim := (((hsum.sub hb).sub_const (zetaEulerMaclaurinMain m N s)).norm)
  simp only [sub_zero] at hlim
  apply le_of_tendsto hlim
  filter_upwards with M
  have hid := zetaEulerMaclaurin_finite_tail hs hs1 hN m M
  have hswap :
      (∑ n ∈ Finset.Icc 1 (N + M), ((n : ℝ) : ℂ) ^ (-s)) -
          (((N + M : ℕ) : ℝ) : ℂ) ^ (1 - s) / (1 - s) -
          zetaEMBoundary m s (N + M : ℕ) - zetaEulerMaclaurinMain m N s =
        -(∑ n ∈ Finset.range M,
          complexEMCell (complexPowerTower s) (2 * m + 2) ((N : ℝ) + n)) := by
    simpa only [Complex.ofReal_natCast, sub_right_comm] using hid
  dsimp only [Function.comp_apply]
  rw [hswap, norm_neg]
  simpa only [show 2 * (m + 1) = 2 * m + 2 by omega] using
    norm_sum_complexPowerTower_EMCell_le hs (by exact_mod_cast hN : (0 : ℝ) < N)
      M (k := m + 1) (by omega)

end RHTower
