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

/-- The untruncated two-component packet appearing in finite cosine translation. -/
def finiteCosineTranslationPacket
    (d : ℕ) (x a : ℝ) : Polynomial ℂ :=
  finiteCosinePolynomial d x * finiteCosinePolynomial d a -
    finiteSinePolynomial d x * finiteSinePolynomial d a

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

/-- Coefficients under the spectral reflection `X ↦ -X`. -/
theorem coeff_comp_neg_X_complex (P : Polynomial ℂ) (m : ℕ) :
    (P.comp (-X)).coeff m = (-1 : ℂ) ^ m * P.coeff m := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [add_comp, coeff_add, hP, hQ]
      ring
  | monomial n c =>
      rw [monomial_comp, neg_pow]
      rw [show (-1 : Polynomial ℂ) = C (-1 : ℂ) by simp, ← map_pow]
      rw [← mul_assoc, ← C_mul, C_mul_X_pow_eq_monomial]
      simp only [coeff_monomial]
      split_ifs with h
      · subst m
        ring
      · simp only [mul_zero]

/-- Every canonical finite cosine section is even in the spectral variable. -/
theorem finiteCosinePolynomial_comp_neg_X (d : ℕ) (x : ℝ) :
    (finiteCosinePolynomial d x).comp (-X) = finiteCosinePolynomial d x := by
  unfold finiteCosinePolynomial
  rw [Polynomial.sum_comp]
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [mul_comp, C_comp, X_pow_comp]
  rw [show (-X : Polynomial ℂ) ^ (2 * k) = X ^ (2 * k) by
    rw [neg_pow, (even_two_mul k).neg_one_pow, one_mul]]

/-- Every finite sine companion is odd in the spectral variable. -/
theorem finiteSinePolynomial_comp_neg_X (d : ℕ) (x : ℝ) :
    (finiteSinePolynomial d x).comp (-X) = -finiteSinePolynomial d x := by
  unfold finiteSinePolynomial
  rw [Polynomial.sum_comp, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [mul_comp, C_comp, X_pow_comp]
  rw [show (-X : Polynomial ℂ) ^ (2 * k + 1) = -(X ^ (2 * k + 1)) by
    rw [neg_pow, (odd_two_mul_add_one k).neg_one_pow, neg_one_mul]]
  ring

theorem finiteCosineTranslationPacket_comp_neg_X
    (d : ℕ) (x a : ℝ) :
    (finiteCosineTranslationPacket d x a).comp (-X) =
      finiteCosineTranslationPacket d x a := by
  unfold finiteCosineTranslationPacket
  rw [sub_comp, mul_comp, mul_comp, finiteCosinePolynomial_comp_neg_X,
    finiteCosinePolynomial_comp_neg_X, finiteSinePolynomial_comp_neg_X,
    finiteSinePolynomial_comp_neg_X]
  ring

/-- The entire translation edge is even; all odd top coefficients vanish exactly. -/
theorem finiteCosineTranslationTopEdge_comp_neg_X
    (d : ℕ) (x a : ℝ) :
    (finiteCosineTranslationTopEdge d x a).comp (-X) =
      finiteCosineTranslationTopEdge d x a := by
  have hEdge : finiteCosineTranslationTopEdge d x a =
      finiteCosineTranslationPacket d x a - finiteCosinePolynomial d (x + a) := by
    rw [finiteCosinePolynomial_add_eq_product_sub_topEdge]
    unfold finiteCosineTranslationPacket
    ring
  rw [hEdge, sub_comp, finiteCosineTranslationPacket_comp_neg_X,
    finiteCosinePolynomial_comp_neg_X]

theorem finiteCosineTranslationTopEdge_coeff_eq_zero_of_odd
    (d : ℕ) (x a : ℝ) {m : ℕ} (hm : Odd m) :
    (finiteCosineTranslationTopEdge d x a).coeff m = 0 := by
  have h := congrArg (Polynomial.coeff · m)
    (finiteCosineTranslationTopEdge_comp_neg_X d x a)
  change ((finiteCosineTranslationTopEdge d x a).comp (-X)).coeff m =
    (finiteCosineTranslationTopEdge d x a).coeff m at h
  rw [coeff_comp_neg_X_complex, hm.neg_one_pow] at h
  linear_combination (-1 / 2 : ℂ) * h

/-- The edge vanishes through degree `2*d+1`; its first possible term has degree `2*d+2`. -/
theorem finiteCosineTranslationTopEdge_coeff_eq_zero_of_le
    (d : ℕ) (x a : ℝ) {m : ℕ} (hm : m ≤ 2 * d + 1) :
    (finiteCosineTranslationTopEdge d x a).coeff m = 0 := by
  rcases hm.lt_or_eq with hm | rfl
  · exact finiteCosineTranslationTopEdge_coeff_eq_zero_of_lt d x a hm
  · exact finiteCosineTranslationTopEdge_coeff_eq_zero_of_odd d x a
      (odd_two_mul_add_one d)

/-- Differentiation of the edge first permits degree `2*d+1`. -/
theorem finiteCosineTranslationTopEdge_derivative_coeff_eq_zero_of_lt_succ
    (d : ℕ) (x a : ℝ) {m : ℕ} (hm : m < 2 * d + 1) :
    (finiteCosineTranslationTopEdge d x a).derivative.coeff m = 0 := by
  rw [Polynomial.coeff_derivative,
    finiteCosineTranslationTopEdge_coeff_eq_zero_of_le d x a (by omega), zero_mul]

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


theorem spectralOddExponentialPowerSeries_add (x a : ℝ) :
    (2 : PowerSeries ℂ) * spectralOddExponentialPowerSeries (x + a) =
      spectralOddExponentialPowerSeries x * spectralEvenExponentialPowerSeries a +
        spectralEvenExponentialPowerSeries x * spectralOddExponentialPowerSeries a := by
  unfold spectralEvenExponentialPowerSeries spectralOddExponentialPowerSeries
  simp only [mul_add, add_mul, mul_sub, sub_mul]
  rw [PowerSeries.exp_mul_exp_eq_exp_add,
    PowerSeries.exp_mul_exp_eq_exp_add,
    PowerSeries.exp_mul_exp_eq_exp_add,
    PowerSeries.exp_mul_exp_eq_exp_add]
  ring_nf
  congr 1 <;> congr 2 <;> push_cast <;> ring

theorem finiteSinePolynomial_add_eq_trunc_product
    (d : ℕ) (x a : ℝ) :
    finiteSinePolynomial d (x + a) =
      PowerSeries.trunc (2 * d + 1)
        (((finiteSinePolynomial d x * finiteCosinePolynomial d a +
          finiteCosinePolynomial d x * finiteSinePolynomial d a : Polynomial ℂ) :
            PowerSeries ℂ)) := by
  let n := 2 * d + 1
  have h := congrArg (PowerSeries.trunc n)
    (spectralOddExponentialPowerSeries_add x a)
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
    hprod (spectralOddExponentialPowerSeries x)
      (spectralEvenExponentialPowerSeries a),
    hprod (spectralEvenExponentialPowerSeries x)
      (spectralOddExponentialPowerSeries a),
    trunc_spectralOddExponentialPowerSeries,
    trunc_spectralOddExponentialPowerSeries,
    trunc_spectralOddExponentialPowerSeries,
    trunc_spectralEvenExponentialPowerSeries,
    trunc_spectralEvenExponentialPowerSeries] at h
  have hscale (c e : ℂ) (P Q : Polynomial ℂ) :
      PowerSeries.trunc (2 * d + 1)
          (((c • P : Polynomial ℂ) : PowerSeries ℂ) *
            ((e • Q : Polynomial ℂ) : PowerSeries ℂ)) =
        (c * e) • PowerSeries.trunc (2 * d + 1)
          ((P * Q : Polynomial ℂ) : PowerSeries ℂ) := by
    rw [Polynomial.coe_smul, Polynomial.coe_smul,
      smul_mul_smul_comm, map_smul, ← Polynomial.coe_mul]
  rw [hscale, hscale] at h
  have hfourI : (2 : ℂ) * (2 * I) = 4 * I := by ring
  have hfourI' : (2 * I : ℂ) * 2 = 4 * I := by ring
  rw [hfourI, hfourI'] at h
  have hleft : (2 : Polynomial ℂ) * ((2 * I : ℂ) • finiteSinePolynomial d (x + a)) =
      (4 * I : ℂ) • finiteSinePolynomial d (x + a) := by
    ext m
    simp
    ring
  rw [hleft] at h
  rw [show ((finiteSinePolynomial d x * finiteCosinePolynomial d a +
      finiteCosinePolynomial d x * finiteSinePolynomial d a : Polynomial ℂ) :
        PowerSeries ℂ) =
      ((finiteSinePolynomial d x * finiteCosinePolynomial d a : Polynomial ℂ) :
        PowerSeries ℂ) +
      ((finiteCosinePolynomial d x * finiteSinePolynomial d a : Polynomial ℂ) :
        PowerSeries ℂ) by norm_num,
    map_add]
  apply smul_right_injective (Polynomial ℂ) (by simp : (4 * I : ℂ) ≠ 0)
  simpa only [smul_add] using h

def finiteSineTranslationPacket
    (d : ℕ) (x a : ℝ) : Polynomial ℂ :=
  finiteSinePolynomial d x * finiteCosinePolynomial d a +
    finiteCosinePolynomial d x * finiteSinePolynomial d a

def finiteSineTranslationTopEdge
    (d : ℕ) (x a : ℝ) : Polynomial ℂ :=
  let P := finiteSineTranslationPacket d x a
  P - PowerSeries.trunc (2 * d + 1) (P : PowerSeries ℂ)

theorem finiteSinePolynomial_add_eq_product_sub_topEdge
    (d : ℕ) (x a : ℝ) :
    finiteSinePolynomial d (x + a) =
      finiteSinePolynomial d x * finiteCosinePolynomial d a +
        finiteCosinePolynomial d x * finiteSinePolynomial d a -
          finiteSineTranslationTopEdge d x a := by
  rw [finiteSinePolynomial_add_eq_trunc_product]
  unfold finiteSineTranslationTopEdge finiteSineTranslationPacket
  dsimp only
  ring

theorem trunc_finiteSineTranslationTopEdge
    (d : ℕ) (x a : ℝ) :
    PowerSeries.trunc (2 * d + 1)
      ((finiteSineTranslationTopEdge d x a : Polynomial ℂ) : PowerSeries ℂ) = 0 := by
  let P := finiteSineTranslationPacket d x a
  change PowerSeries.trunc (2 * d + 1)
    (((P - PowerSeries.trunc (2 * d + 1) (P : PowerSeries ℂ) : Polynomial ℂ) :
      PowerSeries ℂ)) = 0
  rw [show (((P - PowerSeries.trunc (2 * d + 1) (P : PowerSeries ℂ) : Polynomial ℂ) :
      PowerSeries ℂ)) = (P : PowerSeries ℂ) -
        ((PowerSeries.trunc (2 * d + 1) (P : PowerSeries ℂ) : Polynomial ℂ) :
          PowerSeries ℂ) by norm_num,
    map_sub, PowerSeries.trunc_trunc, sub_self]

theorem finiteSineTranslationTopEdge_coeff_eq_zero_of_lt
    (d : ℕ) (x a : ℝ) {m : ℕ} (hm : m < 2 * d + 1) :
    (finiteSineTranslationTopEdge d x a).coeff m = 0 := by
  have h := congrArg (Polynomial.coeff · m)
    (trunc_finiteSineTranslationTopEdge d x a)
  change (PowerSeries.trunc (2 * d + 1)
    ((finiteSineTranslationTopEdge d x a : Polynomial ℂ) : PowerSeries ℂ)).coeff m = 0 at h
  rw [PowerSeries.coeff_trunc, if_pos hm] at h
  simpa using h

theorem finiteSineTranslationPacket_comp_neg_X
    (d : ℕ) (x a : ℝ) :
    (finiteSineTranslationPacket d x a).comp (-X) =
      -finiteSineTranslationPacket d x a := by
  unfold finiteSineTranslationPacket
  rw [add_comp, mul_comp, mul_comp, finiteCosinePolynomial_comp_neg_X,
    finiteCosinePolynomial_comp_neg_X, finiteSinePolynomial_comp_neg_X,
    finiteSinePolynomial_comp_neg_X]
  ring

theorem finiteSineTranslationTopEdge_comp_neg_X
    (d : ℕ) (x a : ℝ) :
    (finiteSineTranslationTopEdge d x a).comp (-X) =
      -finiteSineTranslationTopEdge d x a := by
  have hEdge : finiteSineTranslationTopEdge d x a =
      finiteSineTranslationPacket d x a - finiteSinePolynomial d (x + a) := by
    rw [finiteSinePolynomial_add_eq_product_sub_topEdge]
    unfold finiteSineTranslationPacket
    ring
  rw [hEdge, sub_comp, finiteSineTranslationPacket_comp_neg_X,
    finiteSinePolynomial_comp_neg_X]
  ring

theorem finiteSineTranslationTopEdge_coeff_eq_zero_of_even
    (d : ℕ) (x a : ℝ) {m : ℕ} (hm : Even m) :
    (finiteSineTranslationTopEdge d x a).coeff m = 0 := by
  have h := congrArg (Polynomial.coeff · m)
    (finiteSineTranslationTopEdge_comp_neg_X d x a)
  change ((finiteSineTranslationTopEdge d x a).comp (-X)).coeff m =
    (-finiteSineTranslationTopEdge d x a).coeff m at h
  rw [coeff_comp_neg_X_complex, hm.neg_one_pow, one_mul, coeff_neg] at h
  linear_combination (1 / 2 : ℂ) * h

def finiteSineTranslationTopEdgeSection
    (d : ℕ) (z : ℂ) (x a : ℝ) : ℂ :=
  (finiteSineTranslationTopEdge d x a).eval z

theorem truncatedSineCompanion_add
    (d : ℕ) (z : ℂ) (x a : ℝ) :
    truncatedSineCompanion d z (x + a) =
      truncatedSineCompanion d z x * truncatedCosineSection d z a +
        truncatedCosineSection d z x * truncatedSineCompanion d z a -
          finiteSineTranslationTopEdgeSection d z x a := by
  rw [← eval_finiteSinePolynomial,
    finiteSinePolynomial_add_eq_product_sub_topEdge,
    eval_sub, eval_add, eval_mul, eval_mul, eval_finiteCosinePolynomial,
    eval_finiteCosinePolynomial, eval_finiteSinePolynomial, eval_finiteSinePolynomial]
  rfl

theorem truncatedCosineSine_add
    (d : ℕ) (z : ℂ) (x a : ℝ) :
    (truncatedCosineSection d z (x + a),
      truncatedSineCompanion d z (x + a)) =
    (truncatedCosineSection d z x * truncatedCosineSection d z a -
        truncatedSineCompanion d z x * truncatedSineCompanion d z a -
          finiteCosineTranslationTopEdgeSection d z x a,
      truncatedSineCompanion d z x * truncatedCosineSection d z a +
        truncatedCosineSection d z x * truncatedSineCompanion d z a -
          finiteSineTranslationTopEdgeSection d z x a) := by
  rw [truncatedCosineSection_add, truncatedSineCompanion_add]

/-- The contracting exponential eigenchannel of the finite cosine--sine translation matrix. -/
def finitePositivePhasePolynomial (d : ℕ) (x : ℝ) : Polynomial ℂ :=
  finiteCosinePolynomial d x + C I * finiteSinePolynomial d x

/-- The expanding exponential eigenchannel of the finite cosine--sine translation matrix. -/
def finiteNegativePhasePolynomial (d : ℕ) (x : ℝ) : Polynomial ℂ :=
  finiteCosinePolynomial d x - C I * finiteSinePolynomial d x

def finitePositivePhaseTranslationTopEdge
    (d : ℕ) (x a : ℝ) : Polynomial ℂ :=
  finiteCosineTranslationTopEdge d x a +
    C I * finiteSineTranslationTopEdge d x a

def finiteNegativePhaseTranslationTopEdge
    (d : ℕ) (x a : ℝ) : Polynomial ℂ :=
  finiteCosineTranslationTopEdge d x a -
    C I * finiteSineTranslationTopEdge d x a

/-- Exact diagonal form of the two-component finite translation law in the contracting channel. -/
theorem finitePositivePhasePolynomial_add_eq_mul_sub_topEdge
    (d : ℕ) (x a : ℝ) :
    finitePositivePhasePolynomial d (x + a) =
      finitePositivePhasePolynomial d x * finitePositivePhasePolynomial d a -
        finitePositivePhaseTranslationTopEdge d x a := by
  unfold finitePositivePhasePolynomial finitePositivePhaseTranslationTopEdge
  rw [finiteCosinePolynomial_add_eq_product_sub_topEdge,
    finiteSinePolynomial_add_eq_product_sub_topEdge]
  ring

/-- Exact diagonal form of the two-component finite translation law in the expanding channel. -/
theorem finiteNegativePhasePolynomial_add_eq_mul_sub_topEdge
    (d : ℕ) (x a : ℝ) :
    finiteNegativePhasePolynomial d (x + a) =
      finiteNegativePhasePolynomial d x * finiteNegativePhasePolynomial d a -
        finiteNegativePhaseTranslationTopEdge d x a := by
  unfold finiteNegativePhasePolynomial finiteNegativePhaseTranslationTopEdge
  rw [finiteCosinePolynomial_add_eq_product_sub_topEdge,
    finiteSinePolynomial_add_eq_product_sub_topEdge]
  ring

theorem eval_finitePositivePhasePolynomial (d : ℕ) (z : ℂ) (x : ℝ) :
    (finitePositivePhasePolynomial d x).eval z =
      truncatedCosineSection d z x + I * truncatedSineCompanion d z x := by
  simp [finitePositivePhasePolynomial, eval_finiteCosinePolynomial,
    eval_finiteSinePolynomial]

theorem eval_finiteNegativePhasePolynomial (d : ℕ) (z : ℂ) (x : ℝ) :
    (finiteNegativePhasePolynomial d x).eval z =
      truncatedCosineSection d z x - I * truncatedSineCompanion d z x := by
  simp [finiteNegativePhasePolynomial, eval_finiteCosinePolynomial,
    eval_finiteSinePolynomial]

/-- The diagonal-channel edge has no coefficient below the common finite cutoff. -/
theorem finitePositivePhaseTranslationTopEdge_coeff_eq_zero_of_lt
    (d : ℕ) (x a : ℝ) {m : ℕ} (hm : m < 2 * d + 1) :
    (finitePositivePhaseTranslationTopEdge d x a).coeff m = 0 := by
  unfold finitePositivePhaseTranslationTopEdge
  rw [coeff_add, coeff_C_mul,
    finiteCosineTranslationTopEdge_coeff_eq_zero_of_lt d x a hm,
    finiteSineTranslationTopEdge_coeff_eq_zero_of_lt d x a hm]
  ring

/-- The conjugate diagonal-channel edge has the same high-degree support. -/
theorem finiteNegativePhaseTranslationTopEdge_coeff_eq_zero_of_lt
    (d : ℕ) (x a : ℝ) {m : ℕ} (hm : m < 2 * d + 1) :
    (finiteNegativePhaseTranslationTopEdge d x a).coeff m = 0 := by
  unfold finiteNegativePhaseTranslationTopEdge
  rw [coeff_sub, coeff_C_mul,
    finiteCosineTranslationTopEdge_coeff_eq_zero_of_lt d x a hm,
    finiteSineTranslationTopEdge_coeff_eq_zero_of_lt d x a hm]
  ring

end

end RHTower
