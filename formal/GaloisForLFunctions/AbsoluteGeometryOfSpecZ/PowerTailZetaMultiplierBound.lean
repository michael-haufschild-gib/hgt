import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailPrefixQuantitativeFinitePart

/-!
# Uniform zeta growth up to the line of absolute convergence

Truncate the Euler formula at the integer part of the ordinate. The
power prefix and the uniform Bernoulli remainder have the same growth
bound. Keeping a fixed left edge below one avoids a singular constant
as the real part approaches one.
-/

noncomputable section

open Complex Finset

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open _root_.RHTower.DeletionMixedRefinement

private theorem rawPrefix_eq_powerSum (s : ℂ) (N : ℕ) :
    rawPrefix s N = ∑ n ∈ Icc 1 N, (n : ℂ) ^ (-s) := by
  induction N with
  | zero => simp [rawPrefix]
  | succ N ih =>
      simp only [rawPrefix, Finset.sum_range_succ] at ih ⊢
      rw [Finset.sum_Icc_succ_top (by omega), ← ih]
      rfl

private theorem norm_le_coordinate_mass (s : ℂ) : ‖s‖ ≤ |s.re| + |s.im| := by
  have hsq : ‖s‖ ^ 2 ≤ (|s.re| + |s.im|) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith only [sq_abs s.re, sq_abs s.im,
      mul_nonneg (abs_nonneg s.re) (abs_nonneg s.im)]
  nlinarith only [hsq, norm_nonneg s, abs_nonneg s.re, abs_nonneg s.im]

/-- A fixed left edge below one gives a uniform polynomial bound across
the entire strip up to one, away from the real pole. -/
theorem norm_zeta_le_ordinate_power_in_closed_strip
    {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hσ₀1 : σ₀ < 1)
    {s : ℂ} (hs₀ : σ₀ ≤ s.re) (hs1 : s.re ≤ 1) (ht : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ (22 + 1 / (1 - σ₀)) * |s.im| ^ (1 - σ₀) := by
  have hgap : 0 < 1 - σ₀ := sub_pos.mpr hσ₀1
  let N := ⌊|s.im|⌋₊
  have hN : 1 ≤ N := Nat.le_floor (by simpa only [Nat.cast_one] using ht)
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNt : (N : ℝ) ≤ |s.im| := Nat.floor_le (abs_nonneg _)
  have htN : |s.im| ≤ 2 * (N : ℝ) := by
    have hh := Nat.lt_floor_add_one |s.im|
    change |s.im| < (N : ℝ) + 1 at hh
    linarith only [hh, hN1]
  have hspos : 0 < s.re := hσ₀.trans_le hs₀
  have hsne : s ≠ 1 := by
    intro he
    rw [he, Complex.one_im, abs_zero] at ht
    norm_num at ht
  have hsnorm : ‖s‖ ≤ 4 * (N : ℝ) := by
    have hh := norm_le_coordinate_mass s
    rw [abs_of_pos hspos] at hh
    linarith only [hh, hs1, htN, hN1]
  have hsadd : ‖s + 1‖ ≤ 5 * (N : ℝ) := by
    have hh := norm_add_le s 1
    rw [norm_one] at hh
    linarith only [hh, hsnorm, hN1]
  have hprod : ‖s * (s + 1)‖ ≤ 20 * (N : ℝ) ^ 2 := by
    rw [norm_mul]
    calc
      _ ≤ (4 * (N : ℝ)) * (5 * (N : ℝ)) :=
        mul_le_mul hsnorm hsadd (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hcoef : ‖s * (s + 1)‖ / (s.re + 1) ≤ 20 * (N : ℝ) ^ 2 :=
    (div_le_self (norm_nonneg _) (by linarith only [hspos])).trans hprod
  let U := (N : ℝ) ^ (1 - σ₀)
  have hU : 1 ≤ U := Real.one_le_rpow hN1 (by linarith only [hσ₀1])
  have hpow : (N : ℝ) ^ (1 - s.re) ≤ U :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hs₀])
  have hprefix : powerTailPrefix σ₀ N ≤ U / (1 - σ₀) := by
    have hh := (powerTailPrefix_sub_integral_bounds hσ₀ hσ₀1 hNp.le).2
    change powerTailPrefix σ₀ N ≤ (N : ℝ) ^ (1 - σ₀) / (1 - σ₀)
    linarith only [hh]
  have hraw : ‖rawPrefix s N‖ ≤ U / (1 - σ₀) := by
    rw [rawPrefix_eq_powerSum]
    calc
      _ ≤ ∑ n ∈ Icc 1 N, ‖(n : ℂ) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-σ₀) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn1 := (Finset.mem_Icc.mp hn).1
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
        exact Real.rpow_le_rpow_of_exponent_le hnR (neg_le_neg hs₀)
      _ = powerTailPrefix σ₀ N := by
        simp only [powerTailPrefix, powerTailWeight, Nat.floor_natCast]
      _ ≤ _ := hprefix
  have hden : 1 ≤ ‖1 - s‖ := by
    have hh := Complex.abs_im_le_norm (1 - s)
    simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at hh
    exact ht.trans hh
  have hmain : ‖(N : ℂ) ^ (1 - s) / (1 - s)‖ ≤ U := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (by omega),
      Complex.sub_re, Complex.one_re]
    exact (div_le_self (by positivity) hden).trans hpow
  have hend : ‖kernel s N / 2‖ ≤ U := by
    rw [norm_div, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num, kernel,
      Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    exact (div_le_self (by positivity) (by norm_num)).trans
      ((Real.rpow_le_one_of_one_le_of_nonpos hN1 (neg_nonpos.mpr hspos.le)).trans hU)
  have hrem : ‖powerSumRemainder s N‖ ≤ 20 * U := by
    calc
      _ ≤ (‖s * (s + 1)‖ / (s.re + 1)) * (N : ℝ) ^ (-s.re - 1) :=
        norm_powerSumRemainder_le (by linarith only [hspos]) hsne hN
      _ ≤ (20 * (N : ℝ) ^ 2) * (N : ℝ) ^ (-s.re - 1) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = 20 * (N : ℝ) ^ (1 - s.re) := by
        rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hNp]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by norm_num)
  have he : riemannZeta s = rawPrefix s N -
      (N : ℂ) ^ (1 - s) / (1 - s) - kernel s N / 2 - powerSumRemainder s N := by
    dsimp only [powerSumRemainder]
    ring
  have htriangle : ‖riemannZeta s‖ ≤ ‖rawPrefix s N‖ +
      ‖(N : ℂ) ^ (1 - s) / (1 - s)‖ + ‖kernel s N / 2‖ +
      ‖powerSumRemainder s N‖ := by
    rw [he]
    apply (norm_sub_le _ _).trans
    apply add_le_add _ le_rfl
    apply (norm_sub_le _ _).trans
    exact add_le_add (norm_sub_le _ _) le_rfl
  calc
    _ ≤ U / (1 - σ₀) + U + U + 20 * U :=
      htriangle.trans (add_le_add (add_le_add (add_le_add hraw hmain) hend) hrem)
    _ = (22 + 1 / (1 - σ₀)) * U := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hNp.le hNt (by linarith only [hσ₀1])) (by positivity)

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
