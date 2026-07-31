import GaloisForLFunctions.RHTower.CCMSharpPrimeWindow
import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowNoncensorship
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Dyadic sharp-window quadrature

For a prime-power index `k`, reversing the dyadic moving-window sum produces the finite kernel

`sum_{k ≤ n < 2k} n^{-s}`.

This file isolates its exact integral main term and the cellwise discretization error.  The latter
is the analytic remainder whose locally uniform `O(k^{-Re s})` estimate makes the sharp-window
source continuation holomorphic past the shifted critical boundary.
-/

open Complex Finset intervalIntegral MeasureTheory Set

noncomputable section

namespace RHTower

/-- Finite dyadic kernel obtained after reversing the sharp moving-window double sum. -/
def dyadicSharpPrimeWindowKernel (k : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ range k, (((k + j : ℕ) : ℂ) ^ (-s))

/-- Continuous Mellin main term on the matching interval `[k,2k]`. -/
def dyadicSharpPrimeWindowIntegralMain (k : ℕ) (s : ℂ) : ℂ :=
  ∫ x in (k : ℝ)..(2 * k : ℝ), (x : ℂ) ^ (-s)

/-- Discrete-to-continuous error of one dyadic sharp kernel. -/
def dyadicSharpPrimeWindowError (k : ℕ) (s : ℂ) : ℂ :=
  dyadicSharpPrimeWindowKernel k s - dyadicSharpPrimeWindowIntegralMain k s

/-- The continuous dyadic main term factors into scale times the sharp-window Mellin amplitude. -/
theorem dyadicSharpPrimeWindowIntegralMain_eq_scaledMellin
    {k : ℕ} (hk : 1 ≤ k) (s : ℂ) :
    dyadicSharpPrimeWindowIntegralMain k s =
      (k : ℂ) ^ (1 - s) * sharpPrimeWindowMellin (Real.log 2) s := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have h2kreal : (0 : ℝ) < 2 * k := by positivity
  have hkTwo : (k : ℝ) ≤ (2 * k : ℝ) := by
    exact_mod_cast (show k ≤ 2 * k by omega)
  have hzero : (0 : ℝ) ∉ Set.uIcc (k : ℝ) (2 * k : ℝ) := by
    rw [Set.uIcc_of_le hkTwo]
    intro h
    linarith [h.1]
  by_cases hs : s = 1
  · subst s
    rw [dyadicSharpPrimeWindowIntegralMain]
    have hfun : (fun x : ℝ => (x : ℂ) ^ (-(1 : ℂ))) =
        fun x : ℝ => ((1 / x : ℝ) : ℂ) := by
      funext x
      rw [Complex.cpow_neg_one]
      norm_num [div_eq_mul_inv]
    rw [hfun, intervalIntegral.integral_ofReal, integral_one_div hzero]
    have hratio : (2 * (k : ℝ)) / k = 2 := by field_simp
    rw [hratio]
    simp [sharpPrimeWindowMellin]
  · have hneg : -s ≠ (-1 : ℂ) := by
      intro h
      exact hs (neg_inj.mp h)
    rw [dyadicSharpPrimeWindowIntegralMain,
      integral_cpow (Or.inr ⟨hneg, hzero⟩)]
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have h2C : (2 : ℂ) ≠ 0 := by norm_num
    have h2kC : (((2 * (k : ℝ) : ℝ) : ℂ)) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt h2kreal)
    have hlogTwo : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
      exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
    have hlogK : Complex.log (k : ℂ) = (Real.log k : ℂ) := by
      simpa only [Complex.ofReal_natCast] using
        (Complex.ofReal_log hkreal.le).symm
    have hlogTwoK : Complex.log (((2 * (k : ℝ) : ℝ) : ℂ)) =
        Complex.log (2 : ℂ) + Complex.log (k : ℂ) := by
      rw [← Complex.ofReal_log h2kreal.le, hlogTwo, hlogK, ← Complex.ofReal_add,
        ← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hkreal)]
    have hmul : (((2 * (k : ℝ) : ℝ) : ℂ)) ^ (1 - s) =
        (k : ℂ) ^ (1 - s) * (2 : ℂ) ^ (1 - s) := by
      rw [Complex.cpow_def_of_ne_zero h2kC,
        Complex.cpow_def_of_ne_zero hkC,
        Complex.cpow_def_of_ne_zero h2C, hlogTwoK]
      rw [show (Complex.log (2 : ℂ) + Complex.log (k : ℂ)) * (1 - s) =
          Complex.log (k : ℂ) * (1 - s) +
            Complex.log (2 : ℂ) * (1 - s) by ring,
        Complex.exp_add]
    have hexpTwo : Complex.exp (-(Real.log 2 : ℂ) * (s - 1)) =
        (2 : ℂ) ^ (1 - s) := by
      rw [Complex.cpow_def_of_ne_zero h2C, hlogTwo]
      congr 1
      ring
    rw [show -s + 1 = 1 - s by ring, hmul,
      sharpPrimeWindowMellin, rectangularWindowAmplitude_eq_div
        (sub_ne_zero.mpr hs), hexpTwo]
    rw [div_eq_mul_inv, show 1 - s = -(s - 1) by ring, inv_neg]
    simp only [Complex.ofReal_natCast]
    ring

private theorem intervalIntegrable_ofReal_cpow_neg_on_natCell
    {k j : ℕ} (hk : 1 ≤ k) (s : ℂ) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) volume
      ((k + j : ℕ) : ℝ) (((k + j : ℕ) : ℝ) + 1) := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.cpow_const (by fun_prop)
  intro x hx
  left
  rw [Set.uIcc_of_le (by linarith)] at hx
  have hkj : (1 : ℝ) ≤ (k + j : ℕ) := by exact_mod_cast (show 1 ≤ k + j by omega)
  have hxpos : 0 < x := lt_of_lt_of_le (by linarith : (0 : ℝ) < (k + j : ℕ)) hx.1
  simpa using hxpos

/-- The dyadic integral is exactly the sum of its `k` unit-cell integrals. -/
theorem dyadicSharpPrimeWindowIntegralMain_eq_sum_cells
    {k : ℕ} (hk : 1 ≤ k) (s : ℂ) :
    dyadicSharpPrimeWindowIntegralMain k s =
      ∑ j ∈ range k,
        ∫ x in ((k + j : ℕ) : ℝ)..(((k + j : ℕ) : ℝ) + 1),
          (x : ℂ) ^ (-s) := by
  let a : ℕ → ℝ := fun j => (k + j : ℕ)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x : ℝ => (x : ℂ) ^ (-s)) (a := a) (n := k)
    (fun j _ => by
      convert intervalIntegrable_ofReal_cpow_neg_on_natCell (j := j) hk s using 1 ;
        simp only [a, Nat.cast_add, Nat.cast_one] ; ring)
  have ha0 : a 0 = (k : ℝ) := by simp [a]
  have hak : a k = (2 * k : ℝ) := by
    simp only [a]
    push_cast
    ring
  rw [ha0, hak] at hsum
  rw [dyadicSharpPrimeWindowIntegralMain]
  convert hsum.symm using 1 ; simp only [a, Nat.cast_add, Nat.cast_one] ; ring

/-- Exact cell-error expansion. -/
theorem dyadicSharpPrimeWindowError_eq_sum_cellErrors
    {k : ℕ} (hk : 1 ≤ k) (s : ℂ) :
    dyadicSharpPrimeWindowError k s =
      ∑ j ∈ range k,
        ((((k + j : ℕ) : ℂ) ^ (-s)) -
          ∫ x in ((k + j : ℕ) : ℝ)..(((k + j : ℕ) : ℝ) + 1),
            (x : ℂ) ^ (-s)) := by
  rw [dyadicSharpPrimeWindowError, dyadicSharpPrimeWindowKernel,
    dyadicSharpPrimeWindowIntegralMain_eq_sum_cells hk]
  rw [← Finset.sum_sub_distrib]

/-- One unit cell contributes at most the derivative scale at the left edge of the whole dyadic
block. -/
theorem norm_dyadicSharpPrimeWindow_cellError_le
    {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hsre : 0 < s.re)
    (j : ℕ) :
    ‖(((k + j : ℕ) : ℂ) ^ (-s)) -
        ∫ x in ((k + j : ℕ) : ℝ)..(((k + j : ℕ) : ℝ) + 1),
          (x : ℂ) ^ (-s)‖ ≤
      ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs, Complex.zero_re] at hsre
    exact (lt_irrefl 0 hsre).elim
  let a : ℝ := (k + j : ℕ)
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ (-s)
  let C : ℝ := ‖s‖ * (k : ℝ) ^ (-s.re - 1)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hapos : 0 < a := by
    dsimp only [a]
    exact_mod_cast (show 0 < k + j by omega)
  have hderiv : ∀ x ∈ Set.Icc a (a + 1),
      HasDerivWithinAt f ((-s) * (x : ℂ) ^ (-s - 1)) (Set.Icc a (a + 1)) x := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hapos hx.1
    exact (hasDerivAt_ofReal_cpow_const (ne_of_gt hxpos)
      (neg_ne_zero.mpr hs0)).hasDerivWithinAt
  have hderivBound : ∀ x ∈ Set.Ico a (a + 1),
      ‖(-s) * (x : ℂ) ^ (-s - 1)‖ ≤ C := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hapos hx.1
    have hkx : (k : ℝ) ≤ x := by
      have hka : (k : ℝ) ≤ a := by
        dsimp only [a]
        exact_mod_cast (show k ≤ k + j by omega)
      exact hka.trans hx.1
    have hexp : 0 ≤ s.re + 1 := by linarith
    have hpows : (k : ℝ) ^ (s.re + 1) ≤ x ^ (s.re + 1) :=
      Real.rpow_le_rpow hkpos.le hkx hexp
    have hkpowpos : 0 < (k : ℝ) ^ (s.re + 1) :=
      Real.rpow_pos_of_pos hkpos _
    have hrpow : x ^ (-s.re - 1) ≤ (k : ℝ) ^ (-s.re - 1) := by
      rw [show -s.re - 1 = -(s.re + 1) by ring,
        Real.rpow_neg hxpos.le, Real.rpow_neg hkpos.le]
      simpa only [one_div] using one_div_le_one_div_of_le hkpowpos hpows
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_left hrpow (norm_nonneg s)
  have hmv : ∀ x ∈ Set.Icc a (a + 1), ‖f x - f a‖ ≤ C * (x - a) :=
    fun x hx => norm_image_sub_le_of_norm_deriv_le_segment' hderiv hderivBound x hx
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg s) (Real.rpow_nonneg hkpos.le _)
  have hpoint : ∀ x ∈ Set.uIoc a (a + 1), ‖f a - f x‖ ≤ C := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hxa : x - a ≤ 1 := by linarith [hx.2]
    calc
      ‖f a - f x‖ = ‖f x - f a‖ := by rw [norm_sub_rev]
      _ ≤ C * (x - a) := hmv x ⟨hx.1.le, hx.2⟩
      _ ≤ C := by nlinarith
  have hfint := intervalIntegrable_ofReal_cpow_neg_on_natCell (j := j) hk s
  have hconst : IntervalIntegrable (fun _ : ℝ => f a) volume a (a + 1) :=
    intervalIntegrable_const
  calc
    ‖(((k + j : ℕ) : ℂ) ^ (-s)) -
        ∫ x in ((k + j : ℕ) : ℝ)..(((k + j : ℕ) : ℝ) + 1),
          (x : ℂ) ^ (-s)‖ =
      ‖∫ x in a..(a + 1), f a - f x‖ := by
        change ‖f a - ∫ x in a..(a + 1), f x‖ = _
        rw [intervalIntegral.integral_sub hconst hfint,
          intervalIntegral.integral_const]
        have haone : a + 1 - a = 1 := by ring
        rw [haone, one_smul]
    _ ≤ C * |a + 1 - a| := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by
      have haone : a + 1 - a = 1 := by ring
      rw [haone, abs_one, mul_one]

/-- **Dyadic quadrature estimate.**  The complete discretization error is bounded by
`norm s * k^{-Re s}`.  This is the summable error scale needed after multiplication by the
critical von-Mangoldt weight. -/
theorem norm_dyadicSharpPrimeWindowError_le
    {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hsre : 0 < s.re) :
    ‖dyadicSharpPrimeWindowError k s‖ ≤
      ‖s‖ * (k : ℝ) ^ (-s.re) := by
  rw [dyadicSharpPrimeWindowError_eq_sum_cellErrors hk]
  calc
    ‖∑ j ∈ range k,
        ((((k + j : ℕ) : ℂ) ^ (-s)) -
          ∫ x in ((k + j : ℕ) : ℝ)..(((k + j : ℕ) : ℝ) + 1),
            (x : ℂ) ^ (-s))‖ ≤
        ∑ j ∈ range k,
          ‖(((k + j : ℕ) : ℂ) ^ (-s)) -
            ∫ x in ((k + j : ℕ) : ℝ)..(((k + j : ℕ) : ℝ) + 1),
              (x : ℂ) ^ (-s)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range k, ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by
      exact Finset.sum_le_sum fun j _ =>
        norm_dyadicSharpPrimeWindow_cellError_le hk hsre j
    _ = (k : ℝ) * (‖s‖ * (k : ℝ) ^ (-s.re - 1)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ‖s‖ * (k : ℝ) ^ (-s.re) := by
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      calc
        (k : ℝ) * (‖s‖ * (k : ℝ) ^ (-s.re - 1)) =
            ‖s‖ * ((k : ℝ) * (k : ℝ) ^ (-s.re - 1)) := by ring
        _ = ‖s‖ * ((k : ℝ) ^ (1 : ℝ) *
            (k : ℝ) ^ (-s.re - 1)) := by rw [Real.rpow_one]
        _ = ‖s‖ * (k : ℝ) ^ ((1 : ℝ) + (-s.re - 1)) := by
          rw [Real.rpow_add hkpos]
        _ = ‖s‖ * (k : ℝ) ^ (-s.re) := by congr 2 ; ring

/-- One von-Mangoldt-weighted dyadic quadrature remainder. -/
def dyadicSharpPrimeWindowErrorSummand (s : ℂ) (k : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt k / Real.sqrt k : ℝ) : ℂ) *
    dyadicSharpPrimeWindowError k s

/-- The weighted dyadic quadrature errors are absolutely summable throughout `Re s > 1/2`.
This is the analytic threshold required for the source-side continuation. -/
theorem summable_dyadicSharpPrimeWindowErrorSummand
    {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (dyadicSharpPrimeWindowErrorSummand s) := by
  let z : ℂ := ((s.re + 1 / 2 : ℝ) : ℂ)
  have hz : 1 < z.re := by
    dsimp only [z]
    simp only [ofReal_re]
    linarith
  have hvm : LSeriesSummable
      (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) z :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hz
  have hdom : Summable (fun k => ‖s‖ *
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) z k‖) :=
    hvm.norm.mul_left ‖s‖
  apply Summable.of_norm_bounded hdom
  intro k
  rcases k.eq_zero_or_pos with rfl | hk
  · simp [dyadicSharpPrimeWindowErrorSummand,
      dyadicSharpPrimeWindowError, dyadicSharpPrimeWindowKernel,
      dyadicSharpPrimeWindowIntegralMain]
  · have hk1 : 1 ≤ k := hk
    have hk0 : k ≠ 0 := Nat.ne_of_gt hk
    have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
    have herr := norm_dyadicSharpPrimeWindowError_le hk1 (by linarith : 0 < s.re)
    rw [dyadicSharpPrimeWindowErrorSummand, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.sqrt_nonneg k))]
    calc
      ArithmeticFunction.vonMangoldt k / Real.sqrt k *
          ‖dyadicSharpPrimeWindowError k s‖ ≤
        ArithmeticFunction.vonMangoldt k / Real.sqrt k *
          (‖s‖ * (k : ℝ) ^ (-s.re)) := by
            exact mul_le_mul_of_nonneg_left herr
              (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg k))
      _ = ‖s‖ * ‖LSeries.term
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) z k‖ := by
        rw [LSeries.term_of_ne_zero hk0, norm_div, norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Complex.norm_natCast_cpow_of_pos hk]
        simp only [z, ofReal_re]
        rw [Real.sqrt_eq_rpow]
        rw [show ArithmeticFunction.vonMangoldt k / (k : ℝ) ^ (1 / 2 : ℝ) *
            (‖s‖ * (k : ℝ) ^ (-s.re)) =
          ‖s‖ * ArithmeticFunction.vonMangoldt k *
            ((k : ℝ) ^ (-(1 / 2 : ℝ)) * (k : ℝ) ^ (-s.re)) by
              rw [div_eq_mul_inv, ← Real.rpow_neg hkreal.le]
              ring]
        rw [← Real.rpow_add hkreal]
        rw [show -(1 / 2 : ℝ) + -s.re = -(s.re + 1 / 2) by ring]
        rw [Real.rpow_neg hkreal.le]
        field_simp

/-- Holomorphic-remainder candidate supplied by the absolutely convergent weighted error series. -/
def dyadicSharpPrimeWindowErrorSeries (s : ℂ) : ℂ :=
  ∑' k : ℕ, dyadicSharpPrimeWindowErrorSummand s k

end RHTower
