import GaloisForLFunctions.RHTower.FiniteEulerLocalRatio
import GaloisForLFunctions.RHTower.PrimeClockContinuousNoGo
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.Core

/-!
# Absolute divergence of the all-prime local-ratio product

For every complex point off the critical line, the prime-indexed deviations of the reflected Euler
local ratios from one are not summable.  Inside the critical strip this follows from a uniform
reverse-triangle lower bound by `p^{-sigma}` or `p^{-(1-sigma)}`.  Outside the strip the deviations
have a fixed positive lower bound.  Since the complement of the critical line is dense, no nonempty
open set can be a domain of absolute convergence for the ordinary all-place product.
-/

open Filter Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Absolute convergence at one point for the ordinary finite-place local-ratio product. -/
def FiniteEulerLocalRatioAbsolutelySummableAt (s : ℂ) : Prop :=
  Summable (fun p : Nat.Primes => ‖finiteEulerLocalRatio p s - 1‖)

private theorem half_norm_sub_le_norm_ratio_sub_one
    {a b : ℂ} (ha : ‖a‖ < 1) (hba : ‖b‖ ≤ ‖a‖) :
    (‖a‖ - ‖b‖) / 2 ≤ ‖(1 - b) / (1 - a) - 1‖ := by
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, norm_one] at ha
    exact (lt_irrefl 1) ha
  have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  have heq : (1 - b) / (1 - a) - 1 = (a - b) / (1 - a) := by
    field_simp [hden]
    ring
  rw [heq, norm_div]
  have hdenpos : 0 < ‖1 - a‖ := norm_pos_iff.mpr hden
  apply (le_div_iff₀ hdenpos).2
  have hdenle : ‖1 - a‖ ≤ 2 := by
    calc
      ‖1 - a‖ ≤ ‖(1 : ℂ)‖ + ‖a‖ := norm_sub_le _ _
      _ ≤ 2 := by simp only [norm_one]; linarith
  have hdiff : 0 ≤ (‖a‖ - ‖b‖) / 2 := by linarith
  calc
    ((‖a‖ - ‖b‖) / 2) * ‖1 - a‖ ≤
        ((‖a‖ - ‖b‖) / 2) * 2 := mul_le_mul_of_nonneg_left hdenle hdiff
    _ = ‖a‖ - ‖b‖ := by ring
    _ ≤ ‖a - b‖ := norm_sub_norm_le _ _

private theorem half_norm_rev_sub_le_norm_ratio_sub_one
    {a b : ℂ} (ha : ‖a‖ < 1) (hab : ‖a‖ ≤ ‖b‖) :
    (‖b‖ - ‖a‖) / 2 ≤ ‖(1 - b) / (1 - a) - 1‖ := by
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, norm_one] at ha
    exact (lt_irrefl 1) ha
  have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  have heq : (1 - b) / (1 - a) - 1 = (a - b) / (1 - a) := by
    field_simp [hden]
    ring
  rw [heq, norm_div]
  have hdenpos : 0 < ‖1 - a‖ := norm_pos_iff.mpr hden
  apply (le_div_iff₀ hdenpos).2
  have hdenle : ‖1 - a‖ ≤ 2 := by
    calc
      ‖1 - a‖ ≤ ‖(1 : ℂ)‖ + ‖a‖ := norm_sub_le _ _
      _ ≤ 2 := by simp only [norm_one]; linarith
  have hdiff : 0 ≤ (‖b‖ - ‖a‖) / 2 := by linarith
  have hrev : ‖b‖ - ‖a‖ ≤ ‖a - b‖ := by
    calc
      ‖b‖ - ‖a‖ ≤ ‖b - a‖ := norm_sub_norm_le _ _
      _ = ‖-(a - b)‖ := by congr 1; ring
      _ = ‖a - b‖ := norm_neg _
  calc
    ((‖b‖ - ‖a‖) / 2) * ‖1 - a‖ ≤
        ((‖b‖ - ‖a‖) / 2) * 2 := mul_le_mul_of_nonneg_left hdenle hdiff
    _ = ‖b‖ - ‖a‖ := by ring
    _ ≤ ‖a - b‖ := hrev

private theorem quarter_le_norm_ratio_sub_one_of_left_large
    {a b : ℂ} (ha : 1 ≤ ‖a‖) (hb : ‖b‖ ≤ 1 / 2) :
    (1 / 4 : ℝ) ≤ ‖(1 - b) / (1 - a) - 1‖ := by
  by_cases hden : 1 - a = 0
  · rw [hden]
    norm_num
  · have heq : (1 - b) / (1 - a) - 1 = (a - b) / (1 - a) := by
      field_simp [hden]
      ring
    rw [heq, norm_div]
    have hdenpos : 0 < ‖1 - a‖ := norm_pos_iff.mpr hden
    apply (le_div_iff₀ hdenpos).2
    have hdenle : ‖1 - a‖ ≤ 2 * ‖a‖ := by
      calc
        ‖1 - a‖ ≤ ‖(1 : ℂ)‖ + ‖a‖ := norm_sub_le _ _
        _ ≤ 2 * ‖a‖ := by simp only [norm_one]; linarith
    have hnum : ‖a‖ - ‖b‖ ≤ ‖a - b‖ := norm_sub_norm_le _ _
    nlinarith

private theorem quarter_le_norm_ratio_sub_one_of_right_large
    {a b : ℂ} (ha : ‖a‖ ≤ 1 / 2) (hb : 1 ≤ ‖b‖) :
    (1 / 4 : ℝ) ≤ ‖(1 - b) / (1 - a) - 1‖ := by
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, norm_one] at ha
    norm_num at ha
  have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  have heq : (1 - b) / (1 - a) - 1 = (a - b) / (1 - a) := by
    field_simp [hden]
    ring
  rw [heq, norm_div]
  have hdenpos : 0 < ‖1 - a‖ := norm_pos_iff.mpr hden
  apply (le_div_iff₀ hdenpos).2
  have hdenle : ‖1 - a‖ ≤ 3 / 2 := by
    calc
      ‖1 - a‖ ≤ ‖(1 : ℂ)‖ + ‖a‖ := norm_sub_le _ _
      _ ≤ 3 / 2 := by simp only [norm_one]; linarith
  have hnum : ‖b‖ - ‖a‖ ≤ ‖a - b‖ := by
    calc
      ‖b‖ - ‖a‖ ≤ ‖b - a‖ := norm_sub_norm_le _ _
      _ = ‖-(a - b)‖ := by congr 1; ring
      _ = ‖a - b‖ := norm_neg _
  nlinarith

private theorem norm_prime_cpow_neg (p : Nat.Primes) (s : ℂ) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  rw [Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re]

private theorem norm_prime_cpow_sub_one (p : Nat.Primes) (s : ℂ) :
    ‖((p : ℕ) : ℂ) ^ (s - 1)‖ = (p : ℝ) ^ (s.re - 1) := by
  rw [Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.sub_re]
  norm_num

private theorem finiteEulerLocalRatio_leftInterior_lower
    {s : ℂ} (hs0 : 0 < s.re) (hshalf : s.re < 1 / 2) (p : Nat.Primes) :
    ((1 - (2 : ℝ) ^ (2 * s.re - 1)) / 2) * (p : ℝ) ^ (-s.re) ≤
      ‖finiteEulerLocalRatio p s - 1‖ := by
  let P : ℝ := p
  let A : ℝ := P ^ (-s.re)
  let B : ℝ := P ^ (s.re - 1)
  let q : ℝ := P ^ (2 * s.re - 1)
  have hPpos : 0 < P := by dsimp [P]; exact_mod_cast p.property.pos
  have hPone : 1 < P := by dsimp [P]; exact_mod_cast p.property.one_lt
  have hPtwo : (2 : ℝ) ≤ P := by dsimp [P]; exact_mod_cast p.property.two_le
  have hApos : 0 < A := Real.rpow_pos_of_pos hPpos _
  have hAlt : A < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg hPone (by linarith)
  have hqnonneg : 0 ≤ q := (Real.rpow_pos_of_pos hPpos _).le
  have hqle : q ≤ (2 : ℝ) ^ (2 * s.re - 1) := by
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) hPtwo (by linarith)
  have hq2lt : (2 : ℝ) ^ (2 * s.re - 1) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hBle : B ≤ A := by
    have hB : B = A * q := by
      dsimp [A, B, q]
      rw [← Real.rpow_add hPpos]
      congr 1
      ring
    rw [hB]
    have hqone : q ≤ 1 := hqle.trans hq2lt.le
    simpa using mul_le_mul_of_nonneg_left hqone hApos.le
  have hbase : (A - B) / 2 ≤ ‖finiteEulerLocalRatio p s - 1‖ := by
    rw [finiteEulerLocalRatio_eq_cpow]
    have h := half_norm_sub_le_norm_ratio_sub_one
      (a := ((p : ℕ) : ℂ) ^ (-s)) (b := ((p : ℕ) : ℂ) ^ (s - 1))
      (by simpa [A, norm_prime_cpow_neg] using hAlt)
      (by simpa [A, B, norm_prime_cpow_neg, norm_prime_cpow_sub_one] using hBle)
    simpa [A, B, norm_prime_cpow_neg, norm_prime_cpow_sub_one] using h
  have hB : B = A * q := by
    dsimp [A, B, q]
    rw [← Real.rpow_add hPpos]
    congr 1
    ring
  have hscaled : A * q ≤ A * (2 : ℝ) ^ (2 * s.re - 1) :=
    mul_le_mul_of_nonneg_left hqle hApos.le
  dsimp [A] at hbase ⊢
  rw [hB] at hbase
  nlinarith

private theorem finiteEulerLocalRatio_rightInterior_lower
    {s : ℂ} (hshalf : 1 / 2 < s.re) (hs1 : s.re < 1) (p : Nat.Primes) :
    ((1 - (2 : ℝ) ^ (1 - 2 * s.re)) / 2) * (p : ℝ) ^ (s.re - 1) ≤
      ‖finiteEulerLocalRatio p s - 1‖ := by
  let P : ℝ := p
  let A : ℝ := P ^ (-s.re)
  let B : ℝ := P ^ (s.re - 1)
  let q : ℝ := P ^ (1 - 2 * s.re)
  have hPpos : 0 < P := by dsimp [P]; exact_mod_cast p.property.pos
  have hPone : 1 < P := by dsimp [P]; exact_mod_cast p.property.one_lt
  have hPtwo : (2 : ℝ) ≤ P := by dsimp [P]; exact_mod_cast p.property.two_le
  have hApos : 0 < A := Real.rpow_pos_of_pos hPpos _
  have hBpos : 0 < B := Real.rpow_pos_of_pos hPpos _
  have hAlt : A < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hPone (by linarith)
  have hqle : q ≤ (2 : ℝ) ^ (1 - 2 * s.re) := by
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) hPtwo (by linarith)
  have hq2lt : (2 : ℝ) ^ (1 - 2 * s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hAle : A ≤ B := by
    have hA : A = B * q := by
      dsimp [A, B, q]
      rw [← Real.rpow_add hPpos]
      congr 1
      ring
    rw [hA]
    have hqone : q ≤ 1 := hqle.trans hq2lt.le
    simpa using mul_le_mul_of_nonneg_left hqone hBpos.le
  have hbase : (B - A) / 2 ≤ ‖finiteEulerLocalRatio p s - 1‖ := by
    rw [finiteEulerLocalRatio_eq_cpow]
    have h := half_norm_rev_sub_le_norm_ratio_sub_one
      (a := ((p : ℕ) : ℂ) ^ (-s)) (b := ((p : ℕ) : ℂ) ^ (s - 1))
      (by simpa [A, norm_prime_cpow_neg] using hAlt)
      (by simpa [A, B, norm_prime_cpow_neg, norm_prime_cpow_sub_one] using hAle)
    simpa [A, B, norm_prime_cpow_neg, norm_prime_cpow_sub_one] using h
  have hA : A = B * q := by
    dsimp [A, B, q]
    rw [← Real.rpow_add hPpos]
    congr 1
    ring
  have hscaled : B * q ≤ B * (2 : ℝ) ^ (1 - 2 * s.re) :=
    mul_le_mul_of_nonneg_left hqle hBpos.le
  dsimp [B] at hbase ⊢
  rw [hA] at hbase
  nlinarith

theorem not_finiteEulerLocalRatioAbsolutelySummableAt_of_re_pos_lt_half
    {s : ℂ} (hs0 : 0 < s.re) (hshalf : s.re < 1 / 2) :
    ¬ FiniteEulerLocalRatioAbsolutelySummableAt s := by
  intro hsum
  let c : ℝ := (1 - (2 : ℝ) ^ (2 * s.re - 1)) / 2
  have hc : 0 < c := by
    dsimp [c]
    have hpow : (2 : ℝ) ^ (2 * s.re - 1) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  change Summable (fun p : Nat.Primes => ‖finiteEulerLocalRatio p s - 1‖) at hsum
  have hscaled : Summable (fun p : Nat.Primes => c * (p : ℝ) ^ (-s.re)) :=
    Summable.of_nonneg_of_le (fun p => mul_nonneg hc.le (by positivity))
      (fun p => by simpa [c] using finiteEulerLocalRatio_leftInterior_lower hs0 hshalf p) hsum
  have hpow : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-s.re)) := by
    rw [← summable_mul_left_iff hc.ne']
    exact hscaled
  exact (HTGeometry.not_summable_prime_rpow_of_exponent_le_one hs0 (by linarith)) hpow

theorem not_finiteEulerLocalRatioAbsolutelySummableAt_of_half_lt_re_lt_one
    {s : ℂ} (hshalf : 1 / 2 < s.re) (hs1 : s.re < 1) :
    ¬ FiniteEulerLocalRatioAbsolutelySummableAt s := by
  intro hsum
  let c : ℝ := (1 - (2 : ℝ) ^ (1 - 2 * s.re)) / 2
  have hc : 0 < c := by
    dsimp [c]
    have hpow : (2 : ℝ) ^ (1 - 2 * s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  change Summable (fun p : Nat.Primes => ‖finiteEulerLocalRatio p s - 1‖) at hsum
  have hscaled : Summable (fun p : Nat.Primes => c * (p : ℝ) ^ (s.re - 1)) :=
    Summable.of_nonneg_of_le (fun p => mul_nonneg hc.le (by positivity))
      (fun p => by simpa [c] using finiteEulerLocalRatio_rightInterior_lower hshalf hs1 p) hsum
  have hpow : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(1 - s.re))) := by
    have hunscaled : Summable (fun p : Nat.Primes => (p : ℝ) ^ (s.re - 1)) := by
      rw [← summable_mul_left_iff hc.ne']
      exact hscaled
    simpa only [neg_sub] using hunscaled
  exact (HTGeometry.not_summable_prime_rpow_of_exponent_le_one
    (by linarith) (by linarith)) hpow

private theorem finiteEulerLocalRatio_leftExterior_lower
    {s : ℂ} (hs : s.re ≤ 0) (p : Nat.Primes) :
    (1 / 4 : ℝ) ≤ ‖finiteEulerLocalRatio p s - 1‖ := by
  rw [finiteEulerLocalRatio_eq_cpow]
  apply quarter_le_norm_ratio_sub_one_of_left_large
  · rw [norm_prime_cpow_neg]
    exact Real.one_le_rpow (by exact_mod_cast p.property.one_lt.le) (by linarith)
  · rw [norm_prime_cpow_sub_one]
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
    calc
      (p : ℝ) ^ (s.re - 1) ≤ (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.property.one_lt.le) (by linarith)
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
      _ = 1 / 2 := by norm_num

private theorem finiteEulerLocalRatio_rightExterior_lower
    {s : ℂ} (hs : 1 ≤ s.re) (p : Nat.Primes) :
    (1 / 4 : ℝ) ≤ ‖finiteEulerLocalRatio p s - 1‖ := by
  rw [finiteEulerLocalRatio_eq_cpow]
  apply quarter_le_norm_ratio_sub_one_of_right_large
  · rw [norm_prime_cpow_neg]
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
    calc
      (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.property.one_lt.le) (by linarith)
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
      _ = 1 / 2 := by norm_num
  · rw [norm_prime_cpow_sub_one]
    exact Real.one_le_rpow (by exact_mod_cast p.property.one_lt.le) (by linarith)

theorem not_finiteEulerLocalRatioAbsolutelySummableAt_of_re_nonpos
    {s : ℂ} (hs : s.re ≤ 0) :
    ¬ FiniteEulerLocalRatioAbsolutelySummableAt s := by
  intro hsum
  have hquarter : Summable (fun _ : Nat.Primes => (1 / 4 : ℝ)) :=
    Summable.of_nonneg_of_le (fun _ => by norm_num)
      (finiteEulerLocalRatio_leftExterior_lower hs) hsum
  have hone : Summable (fun _ : Nat.Primes => (1 : ℝ)) := by
    rw [← summable_mul_left_iff (by norm_num : (1 / 4 : ℝ) ≠ 0)]
    simpa using hquarter
  exact not_summable_constant_one_on_primes hone

theorem not_finiteEulerLocalRatioAbsolutelySummableAt_of_one_le_re
    {s : ℂ} (hs : 1 ≤ s.re) :
    ¬ FiniteEulerLocalRatioAbsolutelySummableAt s := by
  intro hsum
  have hquarter : Summable (fun _ : Nat.Primes => (1 / 4 : ℝ)) :=
    Summable.of_nonneg_of_le (fun _ => by norm_num)
      (finiteEulerLocalRatio_rightExterior_lower hs) hsum
  have hone : Summable (fun _ : Nat.Primes => (1 : ℝ)) := by
    rw [← summable_mul_left_iff (by norm_num : (1 / 4 : ℝ) ≠ 0)]
    simpa using hquarter
  exact not_summable_constant_one_on_primes hone

/-- **Pointwise all-place obstruction.** Absolute convergence fails at every point off the
critical line. -/
theorem not_finiteEulerLocalRatioAbsolutelySummableAt_of_re_ne_half
    {s : ℂ} (hs : s.re ≠ 1 / 2) :
    ¬ FiniteEulerLocalRatioAbsolutelySummableAt s := by
  by_cases hs0 : s.re ≤ 0
  · exact not_finiteEulerLocalRatioAbsolutelySummableAt_of_re_nonpos hs0
  by_cases hs1 : 1 ≤ s.re
  · exact not_finiteEulerLocalRatioAbsolutelySummableAt_of_one_le_re hs1
  have hs0' : 0 < s.re := lt_of_not_ge hs0
  have hs1' : s.re < 1 := lt_of_not_ge hs1
  rcases lt_or_gt_of_ne hs with hleft | hright
  · exact not_finiteEulerLocalRatioAbsolutelySummableAt_of_re_pos_lt_half hs0' hleft
  · exact not_finiteEulerLocalRatioAbsolutelySummableAt_of_half_lt_re_lt_one hright hs1'

/-- **No open absolute-convergence domain.** The ordinary product of all finite-place local ratios
has no nonempty open domain on which its deviations from one are absolutely summable. -/
theorem not_exists_nonempty_open_finiteEulerLocalRatio_absoluteConvergenceDomain :
    ¬ ∃ U : Set ℂ, U.Nonempty ∧ IsOpen U ∧
      ∀ s ∈ U, FiniteEulerLocalRatioAbsolutelySummableAt s := by
  rintro ⟨U, hUne, hUopen, hU⟩
  obtain ⟨s, hsoff, hsU⟩ :=
    _root_.RHTower.dense_offCriticalLine.exists_mem_open hUopen hUne
  exact not_finiteEulerLocalRatioAbsolutelySummableAt_of_re_ne_half hsoff (hU s hsU)

end GaloisForLFunctions.RHTower

end
