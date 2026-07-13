import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCoreCancellation
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Trunc

open scoped BigOperators
open Polynomial Complex

namespace RHTower

noncomputable section

/-- Twice the formal cosine series with source variable `x` and spectral indeterminate `X`. -/
def spectralEvenExponentialPowerSeries (x : ℝ) : PowerSeries ℂ :=
  PowerSeries.rescale ((x : ℂ) * I) (PowerSeries.exp ℂ) +
    PowerSeries.rescale (-((x : ℂ) * I)) (PowerSeries.exp ℂ)

/-- Twice `i` times the formal sine series with source variable `x`. -/
def spectralOddExponentialPowerSeries (x : ℝ) : PowerSeries ℂ :=
  PowerSeries.rescale ((x : ℂ) * I) (PowerSeries.exp ℂ) -
    PowerSeries.rescale (-((x : ℂ) * I)) (PowerSeries.exp ℂ)

/-- The formal exponential addition law, already arranged in even--odd form. -/
theorem spectralEvenExponentialPowerSeries_add (x a : ℝ) :
    (2 : PowerSeries ℂ) * spectralEvenExponentialPowerSeries (x + a) =
      spectralEvenExponentialPowerSeries x * spectralEvenExponentialPowerSeries a +
        spectralOddExponentialPowerSeries x * spectralOddExponentialPowerSeries a := by
  unfold spectralEvenExponentialPowerSeries spectralOddExponentialPowerSeries
  simp only [mul_add, add_mul, mul_sub, sub_mul]
  rw [PowerSeries.exp_mul_exp_eq_exp_add,
    PowerSeries.exp_mul_exp_eq_exp_add,
    PowerSeries.exp_mul_exp_eq_exp_add,
    PowerSeries.exp_mul_exp_eq_exp_add]
  ring_nf
  congr 1 <;> congr 2 <;> push_cast <;> ring

theorem coeff_spectralEvenExponentialPowerSeries_two_mul (x : ℝ) (k : ℕ) :
    PowerSeries.coeff (2 * k) (spectralEvenExponentialPowerSeries x) =
      2 * ((-1 : ℂ) ^ k * (x : ℂ) ^ (2 * k) / (2 * k).factorial) := by
  have hI : I ^ (2 * k) = (-1 : ℂ) ^ k := by
    rw [pow_mul, Complex.I_sq]
  unfold spectralEvenExponentialPowerSeries
  simp only [map_add, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  rw [mul_pow, neg_pow, (even_two_mul k).neg_one_pow]
  push_cast
  rw [mul_pow, hI]
  ring

theorem coeff_spectralEvenExponentialPowerSeries_two_mul_add_one (x : ℝ) (k : ℕ) :
    PowerSeries.coeff (2 * k + 1) (spectralEvenExponentialPowerSeries x) = 0 := by
  unfold spectralEvenExponentialPowerSeries
  simp only [map_add, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  rw [mul_pow, neg_pow, (odd_two_mul_add_one k).neg_one_pow]
  ring

theorem coeff_spectralOddExponentialPowerSeries_two_mul (x : ℝ) (k : ℕ) :
    PowerSeries.coeff (2 * k) (spectralOddExponentialPowerSeries x) = 0 := by
  unfold spectralOddExponentialPowerSeries
  simp only [map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  rw [mul_pow, neg_pow, (even_two_mul k).neg_one_pow]
  ring

theorem coeff_spectralOddExponentialPowerSeries_two_mul_add_one (x : ℝ) (k : ℕ) :
    PowerSeries.coeff (2 * k + 1) (spectralOddExponentialPowerSeries x) =
      2 * I * ((-1 : ℂ) ^ k * (x : ℂ) ^ (2 * k + 1) /
        (2 * k + 1).factorial) := by
  have hI : I ^ (2 * k) = (-1 : ℂ) ^ k := by
    rw [pow_mul, Complex.I_sq]
  have hIodd : I ^ (2 * k + 1) = (-1 : ℂ) ^ k * I := by
    rw [pow_add, hI, pow_one]
  unfold spectralOddExponentialPowerSeries
  simp only [map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  rw [mul_pow, neg_pow, (odd_two_mul_add_one k).neg_one_pow]
  push_cast
  rw [mul_pow, hIodd]
  ring

/-- The canonical finite cosine section as a polynomial in the spectral variable. -/
def finiteCosinePolynomial (d : ℕ) (x : ℝ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (d + 1),
    Polynomial.C (((-1 : ℂ) ^ k * (x : ℂ) ^ (2 * k)) / (2 * k).factorial) *
      Polynomial.X ^ (2 * k)

/-- The odd companion required by translation of a finite cosine section. -/
def finiteSinePolynomial (d : ℕ) (x : ℝ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range d,
    Polynomial.C (((-1 : ℂ) ^ k * (x : ℂ) ^ (2 * k + 1)) /
      (2 * k + 1).factorial) * Polynomial.X ^ (2 * k + 1)

theorem trunc_spectralEvenExponentialPowerSeries
    (d : ℕ) (x : ℝ) :
    PowerSeries.trunc (2 * d + 1) (spectralEvenExponentialPowerSeries x) =
      (2 : ℂ) • finiteCosinePolynomial d x := by
  induction d with
  | zero =>
      have h0 := coeff_spectralEvenExponentialPowerSeries_two_mul x 0
      norm_num at h0
      rw [show 2 * 0 + 1 = 0 + 1 by omega,
        PowerSeries.trunc_succ, PowerSeries.trunc_zero',
        PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
      simp [finiteCosinePolynomial, Algebra.smul_def,
        Polynomial.C_eq_algebraMap, map_ofNat]
  | succ d ih =>
      rw [show 2 * (d + 1) + 1 = (2 * d + 1 + 1) + 1 by omega,
        PowerSeries.trunc_succ, PowerSeries.trunc_succ,
        coeff_spectralEvenExponentialPowerSeries_two_mul_add_one,
        show 2 * d + 2 = 2 * (d + 1) by omega,
        coeff_spectralEvenExponentialPowerSeries_two_mul, ih]
      simp only [Polynomial.monomial_zero_right, add_zero,
        finiteCosinePolynomial, Finset.sum_range_succ]
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [map_mul, map_ofNat]
      simp only [Algebra.smul_def, map_ofNat]
      ring

theorem trunc_spectralOddExponentialPowerSeries
    (d : ℕ) (x : ℝ) :
    PowerSeries.trunc (2 * d + 1) (spectralOddExponentialPowerSeries x) =
      (2 * I) • finiteSinePolynomial d x := by
  induction d with
  | zero =>
      have h0 := coeff_spectralOddExponentialPowerSeries_two_mul x 0
      norm_num at h0
      rw [show 2 * 0 + 1 = 0 + 1 by omega,
        PowerSeries.trunc_succ, PowerSeries.trunc_zero',
        PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
      simp [finiteSinePolynomial]
  | succ d ih =>
      rw [show 2 * (d + 1) + 1 = (2 * d + 1 + 1) + 1 by omega,
        PowerSeries.trunc_succ, PowerSeries.trunc_succ,
        coeff_spectralOddExponentialPowerSeries_two_mul_add_one,
        show 2 * d + 2 = 2 * (d + 1) by omega,
        coeff_spectralOddExponentialPowerSeries_two_mul, ih]
      simp only [Polynomial.monomial_zero_right, add_zero,
        finiteSinePolynomial, Finset.sum_range_succ]
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      rw [smul_add]
      congr 1
      simp only [Algebra.smul_def, map_mul, map_ofNat]
      rw [← Polynomial.C_eq_algebraMap]
      ring

/-- Translation of the finite cosine section is the low-degree part of the cosine--sine
product.  This is the exact triangular coefficient relation; no analytic limit is used. -/
theorem finiteCosinePolynomial_add_eq_trunc_product
    (d : ℕ) (x a : ℝ) :
    finiteCosinePolynomial d (x + a) =
      PowerSeries.trunc (2 * d + 1)
        (((finiteCosinePolynomial d x * finiteCosinePolynomial d a -
          finiteSinePolynomial d x * finiteSinePolynomial d a : Polynomial ℂ) :
            PowerSeries ℂ)) := by
  let n := 2 * d + 1
  have h := congrArg (PowerSeries.trunc n)
    (spectralEvenExponentialPowerSeries_add x a)
  dsimp only [n] at h ⊢
  have htwo (f : PowerSeries ℂ) :
      PowerSeries.trunc (2 * d + 1) ((2 : PowerSeries ℂ) * f) =
        (2 : Polynomial ℂ) * PowerSeries.trunc (2 * d + 1) f := by
    change PowerSeries.trunc (2 * d + 1) (PowerSeries.C 2 * f) = _
    rw [PowerSeries.trunc_C_mul]
    have hc : Polynomial.C (2 : ℂ) = (2 : Polynomial ℂ) := by
      simpa only [map_ofNat] using Polynomial.C_eq_algebraMap (2 : ℂ)
    rw [hc]
  have hprod (f g : PowerSeries ℂ) :
      PowerSeries.trunc (2 * d + 1) (f * g) =
        PowerSeries.trunc (2 * d + 1)
          (((PowerSeries.trunc (2 * d + 1) f : Polynomial ℂ) : PowerSeries ℂ) *
            ((PowerSeries.trunc (2 * d + 1) g : Polynomial ℂ) : PowerSeries ℂ)) :=
    (PowerSeries.trunc_trunc_mul_trunc f g).symm
  rw [htwo, map_add,
    hprod (spectralEvenExponentialPowerSeries x)
      (spectralEvenExponentialPowerSeries a),
    hprod (spectralOddExponentialPowerSeries x)
      (spectralOddExponentialPowerSeries a),
    trunc_spectralEvenExponentialPowerSeries,
    trunc_spectralEvenExponentialPowerSeries,
    trunc_spectralEvenExponentialPowerSeries,
    trunc_spectralOddExponentialPowerSeries,
    trunc_spectralOddExponentialPowerSeries] at h
  have hscale (c : ℂ) (P Q : Polynomial ℂ) :
      PowerSeries.trunc (2 * d + 1)
          (((c • P : Polynomial ℂ) : PowerSeries ℂ) *
            ((c • Q : Polynomial ℂ) : PowerSeries ℂ)) =
        c ^ 2 • PowerSeries.trunc (2 * d + 1) ((P * Q : Polynomial ℂ) : PowerSeries ℂ) := by
    rw [Polynomial.coe_smul, Polynomial.coe_smul,
      smul_mul_smul_comm, map_smul, ← Polynomial.coe_mul]
    rw [pow_two]
  rw [hscale, hscale] at h
  have htwoSq : (2 : ℂ) ^ 2 = 4 := by norm_num
  have htwoISq : (2 * I : ℂ) ^ 2 = -4 := by
    calc
      (2 * I : ℂ) ^ 2 = 4 * I ^ 2 := by ring
      _ = -4 := by rw [Complex.I_sq]; ring
  rw [htwoSq, htwoISq] at h
  have hleft : (2 : Polynomial ℂ) * ((2 : ℂ) • finiteCosinePolynomial d (x + a)) =
      (4 : ℂ) • finiteCosinePolynomial d (x + a) := by
    ext m
    simp
    ring
  rw [hleft] at h
  rw [show ((finiteCosinePolynomial d x * finiteCosinePolynomial d a -
      finiteSinePolynomial d x * finiteSinePolynomial d a : Polynomial ℂ) :
        PowerSeries ℂ) =
      ((finiteCosinePolynomial d x * finiteCosinePolynomial d a : Polynomial ℂ) :
        PowerSeries ℂ) -
      ((finiteSinePolynomial d x * finiteSinePolynomial d a : Polynomial ℂ) :
        PowerSeries ℂ) by norm_num,
    map_sub]
  apply smul_right_injective (Polynomial ℂ) (by norm_num : (4 : ℂ) ≠ 0)
  have h' : (4 : ℂ) • finiteCosinePolynomial d (x + a) =
      (4 : ℂ) • PowerSeries.trunc (2 * d + 1)
        ((finiteCosinePolynomial d x * finiteCosinePolynomial d a : Polynomial ℂ) :
          PowerSeries ℂ) -
      (4 : ℂ) • PowerSeries.trunc (2 * d + 1)
        ((finiteSinePolynomial d x * finiteSinePolynomial d a : Polynomial ℂ) :
          PowerSeries ℂ) := by
    simpa only [neg_smul] using h
  simpa [smul_sub] using h'

/-- The exact top edge discarded by the finite cosine--sine translation law. -/
def finiteCosineTranslationTopEdge (d : ℕ) (x a : ℝ) : Polynomial ℂ :=
  let P := finiteCosinePolynomial d x * finiteCosinePolynomial d a -
    finiteSinePolynomial d x * finiteSinePolynomial d a
  P - PowerSeries.trunc (2 * d + 1) (P : PowerSeries ℂ)

/-- Exact two-component finite translation, with the entire truncation defect isolated in one
top-edge polynomial. -/
theorem finiteCosinePolynomial_add_eq_product_sub_topEdge
    (d : ℕ) (x a : ℝ) :
    finiteCosinePolynomial d (x + a) =
      finiteCosinePolynomial d x * finiteCosinePolynomial d a -
        finiteSinePolynomial d x * finiteSinePolynomial d a -
          finiteCosineTranslationTopEdge d x a := by
  rw [finiteCosinePolynomial_add_eq_trunc_product]
  unfold finiteCosineTranslationTopEdge
  dsimp only
  ring

theorem trunc_finiteCosineTranslationTopEdge
    (d : ℕ) (x a : ℝ) :
    PowerSeries.trunc (2 * d + 1)
      ((finiteCosineTranslationTopEdge d x a : Polynomial ℂ) : PowerSeries ℂ) = 0 := by
  let P := finiteCosinePolynomial d x * finiteCosinePolynomial d a -
    finiteSinePolynomial d x * finiteSinePolynomial d a
  change PowerSeries.trunc (2 * d + 1)
    (((P - PowerSeries.trunc (2 * d + 1) (P : PowerSeries ℂ) : Polynomial ℂ) :
      PowerSeries ℂ)) = 0
  rw [show (((P - PowerSeries.trunc (2 * d + 1) (P : PowerSeries ℂ) : Polynomial ℂ) :
      PowerSeries ℂ)) = (P : PowerSeries ℂ) -
        ((PowerSeries.trunc (2 * d + 1) (P : PowerSeries ℂ) : Polynomial ℂ) :
          PowerSeries ℂ) by norm_num,
    map_sub, PowerSeries.trunc_trunc, sub_self]

/-- The translation defect has no coefficient below the finite-section cutoff. -/
theorem finiteCosineTranslationTopEdge_coeff_eq_zero_of_lt
    (d : ℕ) (x a : ℝ) {m : ℕ} (hm : m < 2 * d + 1) :
    (finiteCosineTranslationTopEdge d x a).coeff m = 0 := by
  have h := congrArg (Polynomial.coeff · m)
    (trunc_finiteCosineTranslationTopEdge d x a)
  change (PowerSeries.trunc (2 * d + 1)
    ((finiteCosineTranslationTopEdge d x a : Polynomial ℂ) : PowerSeries ℂ)).coeff m = 0 at h
  rw [PowerSeries.coeff_trunc, if_pos hm] at h
  simpa using h

/-- Differentiation moves the translation defect boundary down by exactly one degree. -/
theorem finiteCosineTranslationTopEdge_derivative_coeff_eq_zero_of_lt
    (d : ℕ) (x a : ℝ) {m : ℕ} (hm : m < 2 * d) :
    (finiteCosineTranslationTopEdge d x a).derivative.coeff m = 0 := by
  rw [Polynomial.coeff_derivative,
    finiteCosineTranslationTopEdge_coeff_eq_zero_of_lt d x a (by omega), zero_mul]

/-- Evaluation of the finite odd companion. -/
def truncatedSineCompanion (d : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range d,
    ((-1 : ℂ) ^ k * (z * (x : ℂ)) ^ (2 * k + 1)) /
      (2 * k + 1).factorial

theorem eval_finiteCosinePolynomial (d : ℕ) (z : ℂ) (x : ℝ) :
    (finiteCosinePolynomial d x).eval z = truncatedCosineSection d z x := by
  unfold finiteCosinePolynomial truncatedCosineSection
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  ring

theorem eval_finiteSinePolynomial (d : ℕ) (z : ℂ) (x : ℝ) :
    (finiteSinePolynomial d x).eval z = truncatedSineCompanion d z x := by
  unfold finiteSinePolynomial truncatedSineCompanion
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  ring

def finiteCosineTranslationTopEdgeSection
    (d : ℕ) (z : ℂ) (x a : ℝ) : ℂ :=
  (finiteCosineTranslationTopEdge d x a).eval z

/-- Exact cosine--sine translation identity for the canonical finite section. -/
theorem truncatedCosineSection_add
    (d : ℕ) (z : ℂ) (x a : ℝ) :
    truncatedCosineSection d z (x + a) =
      truncatedCosineSection d z x * truncatedCosineSection d z a -
        truncatedSineCompanion d z x * truncatedSineCompanion d z a -
          finiteCosineTranslationTopEdgeSection d z x a := by
  rw [← eval_finiteCosinePolynomial, finiteCosinePolynomial_add_eq_product_sub_topEdge,
    eval_sub, eval_sub, eval_mul, eval_mul, eval_finiteCosinePolynomial,
    eval_finiteCosinePolynomial, eval_finiteSinePolynomial, eval_finiteSinePolynomial]
  rfl

/-- The requested finite translation identity for the completion-compensated core `H_d`.  The
constant seam is untouched; all translation loss is confined to the explicit top edge. -/
theorem sq_mul_thetaCuspTailSecondCoreAtom_add_eq_cosine_sine_sub_topEdge
    (d : ℕ) (z : ℂ) (x a : ℝ) :
    z ^ 2 * thetaCuspTailSecondCoreAtom d z (x + a) =
      (z ^ 2 + 1 / 4) *
          (truncatedCosineSection (d + 1) z x * truncatedCosineSection (d + 1) z a -
            truncatedSineCompanion (d + 1) z x * truncatedSineCompanion (d + 1) z a -
              finiteCosineTranslationTopEdgeSection (d + 1) z x a) -
        1 / 4 := by
  rw [sq_mul_thetaCuspTailSecondCoreAtom_eq_completion_mul_cosine_sub,
    truncatedCosineSection_add]

end

end RHTower
