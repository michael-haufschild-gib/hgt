import GaloisForLFunctions.HTGeometry.RiemannGaussian.GramWeilOnePair
import GaloisForLFunctions.HTGeometry.PoissonKernelIntegrals
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Integral

/-!
# Exact analytic realization for one conjugate pair

This file proves the improper rational integrals used by the quadratic
polynomial `A(z) = z^(2 : ℕ) + a^(2 : ℕ)`.  The eventual endpoint is the exact `L²` Gram
matrix of its two normalized zero functions.  No model-space or
Krein--Langer theorem is assumed here.
-/

open MeasureTheory
open scoped ComplexConjugate

namespace RiemannGaussian

noncomputable section

private theorem integrable_cauchyKernel {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => (x ^ (2 : ℕ) + a ^ (2 : ℕ))⁻¹) := by
  simpa [add_comm] using
    GaloisForLFunctions.HTGeometry.integrable_inv_sq_add_sq ha

private theorem integral_cauchyKernel {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, (x ^ (2 : ℕ) + a ^ (2 : ℕ))⁻¹) = Real.pi / a := by
  simpa [add_comm] using
    GaloisForLFunctions.HTGeometry.integral_inv_sq_add_sq ha

/-- Integrability of the product of two distinct positive Cauchy kernels. -/
theorem integrable_inv_two_sq_add_sq {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    Integrable
      (fun x : ℝ => ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))⁻¹) := by
  have hv : 0 < v := hu.trans huv
  have hgap : v ^ (2 : ℕ) - u ^ (2 : ℕ) ≠ 0 := by nlinarith
  have hparts : Integrable
      (fun x : ℝ => (x ^ (2 : ℕ) + u ^ (2 : ℕ))⁻¹ - (x ^ (2 : ℕ) + v ^ (2 : ℕ))⁻¹) :=
    (integrable_cauchyKernel hu).sub (integrable_cauchyKernel hv)
  have hscaled := hparts.const_mul (v ^ (2 : ℕ) - u ^ (2 : ℕ))⁻¹
  convert hscaled using 1
  ext x
  have hxu : x ^ (2 : ℕ) + u ^ (2 : ℕ) ≠ 0 := by positivity
  have hxv : x ^ (2 : ℕ) + v ^ (2 : ℕ) ≠ 0 := by positivity
  field_simp [hgap, hxu, hxv]; ring

/-- The first rational integral in the finite one-pair calculation. -/
theorem integral_inv_two_sq_add_sq {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    (∫ x : ℝ, ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))⁻¹) =
      Real.pi / (u * v * (u + v)) := by
  have hv : 0 < v := hu.trans huv
  have hgap : v ^ (2 : ℕ) - u ^ (2 : ℕ) ≠ 0 := by nlinarith
  have huInt := integrable_cauchyKernel hu
  have hvInt := integrable_cauchyKernel hv
  calc
    (∫ x : ℝ, ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))⁻¹) =
        ∫ x : ℝ, (v ^ (2 : ℕ) - u ^ (2 : ℕ))⁻¹ *
          ((x ^ (2 : ℕ) + u ^ (2 : ℕ))⁻¹ - (x ^ (2 : ℕ) + v ^ (2 : ℕ))⁻¹) := by
      apply integral_congr_ae
      filter_upwards [] with x
      have hxu : x ^ (2 : ℕ) + u ^ (2 : ℕ) ≠ 0 := by positivity
      have hxv : x ^ (2 : ℕ) + v ^ (2 : ℕ) ≠ 0 := by positivity
      field_simp [hgap, hxu, hxv]; ring
    _ = (v ^ (2 : ℕ) - u ^ (2 : ℕ))⁻¹ *
        ((∫ x : ℝ, (x ^ (2 : ℕ) + u ^ (2 : ℕ))⁻¹) -
          ∫ x : ℝ, (x ^ (2 : ℕ) + v ^ (2 : ℕ))⁻¹) := by
      rw [integral_const_mul, integral_sub huInt hvInt]
    _ = Real.pi / (u * v * (u + v)) := by
      rw [integral_cauchyKernel hu, integral_cauchyKernel hv]
      field_simp [hu.ne', hv.ne', hgap]; ring

/-- Integrability of the quadratic-numerator two-pole kernel. -/
theorem integrable_sq_div_two_sq_add_sq {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    Integrable
      (fun x : ℝ =>
        x ^ (2 : ℕ) / ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))) := by
  have hv : 0 < v := hu.trans huv
  have hright := integrable_cauchyKernel hv
  have hproduct := integrable_inv_two_sq_add_sq hu huv
  have hdiff := hright.sub (hproduct.const_mul (u ^ (2 : ℕ)))
  convert hdiff using 1
  ext x
  change x ^ (2 : ℕ) / ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ))) =
    (x ^ (2 : ℕ) + v ^ (2 : ℕ))⁻¹ -
      u ^ (2 : ℕ) * ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))⁻¹
  have hxu : x ^ (2 : ℕ) + u ^ (2 : ℕ) ≠ 0 := by positivity
  have hxv : x ^ (2 : ℕ) + v ^ (2 : ℕ) ≠ 0 := by positivity
  field_simp [hxu, hxv]; ring

/-- The second rational integral in the finite one-pair calculation. -/
theorem integral_sq_div_two_sq_add_sq {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    (∫ x : ℝ,
      x ^ (2 : ℕ) / ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))) =
      Real.pi / (u + v) := by
  have hv : 0 < v := hu.trans huv
  have hright := integrable_cauchyKernel hv
  have hproduct := integrable_inv_two_sq_add_sq hu huv
  calc
    (∫ x : ℝ,
      x ^ (2 : ℕ) / ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))) =
        ∫ x : ℝ, (x ^ (2 : ℕ) + v ^ (2 : ℕ))⁻¹ -
          u ^ (2 : ℕ) * ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))⁻¹ := by
      apply integral_congr_ae
      filter_upwards [] with x
      have hxu : x ^ (2 : ℕ) + u ^ (2 : ℕ) ≠ 0 := by positivity
      have hxv : x ^ (2 : ℕ) + v ^ (2 : ℕ) ≠ 0 := by positivity
      field_simp [hxu, hxv]; ring
    _ = (∫ x : ℝ, (x ^ (2 : ℕ) + v ^ (2 : ℕ))⁻¹) -
        u ^ (2 : ℕ) * ∫ x : ℝ,
          ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))⁻¹ := by
      rw [integral_sub hright (hproduct.const_mul (u ^ (2 : ℕ))),
        integral_const_mul]
    _ = Real.pi / (u + v) := by
      rw [integral_cauchyKernel hv,
        integral_inv_two_sq_add_sq hu huv]
      field_simp [hu.ne', hv.ne']; ring

/-- The odd-numerator two-pole kernel is absolutely integrable. -/
theorem integrable_id_div_two_sq_add_sq {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    Integrable
      (fun x : ℝ =>
        x / ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))) := by
  have hv : 0 < v := hu.trans huv
  have hmajorant : Integrable
      (fun x : ℝ => (2 * u)⁻¹ * (x ^ (2 : ℕ) + v ^ (2 : ℕ))⁻¹) :=
    (integrable_cauchyKernel hv).const_mul (2 * u)⁻¹
  apply hmajorant.mono'
  · apply Continuous.aestronglyMeasurable
    apply continuous_id.div
    · fun_prop
    · intro x
      positivity
  · filter_upwards [] with x
    have hxu : 0 < x ^ (2 : ℕ) + u ^ (2 : ℕ) := by positivity
    have hxv : 0 < x ^ (2 : ℕ) + v ^ (2 : ℕ) := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hxu,
      abs_of_pos hxv]
    have hfirst : |x| / (x ^ (2 : ℕ) + u ^ (2 : ℕ)) ≤ (2 * u)⁻¹ := by
      rw [div_le_iff₀ hxu, inv_mul_eq_div, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (|x| - u), sq_abs x]
    calc
      |x| / ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ))) =
          (|x| / (x ^ (2 : ℕ) + u ^ (2 : ℕ))) * (x ^ (2 : ℕ) + v ^ (2 : ℕ))⁻¹ := by
            field_simp [hxu.ne', hxv.ne']
      _ ≤ (2 * u)⁻¹ * (x ^ (2 : ℕ) + v ^ (2 : ℕ))⁻¹ :=
        mul_le_mul_of_nonneg_right hfirst (by positivity)

/-- The odd part of the one-pair cross term integrates to zero. -/
theorem integral_id_div_two_sq_add_sq {u v : ℝ} :
    (∫ x : ℝ,
      x / ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))) = 0 := by
  let f : ℝ → ℝ := fun x =>
    x / ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))
  have hsub := MeasureTheory.integral_neg_eq_self f MeasureTheory.volume
  have hodd : (fun x => f (-x)) = fun x => -f x := by
    funext x
    dsimp [f]
    rw [neg_sq, neg_div]
  rw [hodd, MeasureTheory.integral_neg] at hsub
  change -(∫ x : ℝ,
      x / ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))) =
    ∫ x : ℝ,
      x / ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ))) at hsub
  linarith

/-- The positive square-root parameter used to factor the quadratic
denominator. -/
def finiteOnePairB (a : ℝ) : ℝ := Real.sqrt (1 + a ^ (2 : ℕ))

/-- The upper-half-plane pole height of `A + i A'` for
`A(z) = z^(2 : ℕ) + a^(2 : ℕ)`. -/
def finiteOnePairU (a : ℝ) : ℝ := finiteOnePairB a - 1

/-- The absolute lower-half-plane pole height of `A + i A'` for
`A(z) = z^(2 : ℕ) + a^(2 : ℕ)`. -/
def finiteOnePairV (a : ℝ) : ℝ := finiteOnePairB a + 1

theorem finiteOnePairB_sq (a : ℝ) :
    finiteOnePairB a ^ (2 : ℕ) = 1 + a ^ (2 : ℕ) := by
  exact Real.sq_sqrt (by positivity)

theorem finiteOnePairB_gt_one {a : ℝ} (ha : 0 < a) :
    1 < finiteOnePairB a := by
  rw [finiteOnePairB, Real.lt_sqrt (by positivity)]
  nlinarith [sq_pos_of_pos ha]

theorem finiteOnePairU_pos {a : ℝ} (ha : 0 < a) :
    0 < finiteOnePairU a := by
  rw [finiteOnePairU]
  exact sub_pos.mpr (finiteOnePairB_gt_one ha)

theorem finiteOnePairV_pos {a : ℝ} (ha : 0 < a) :
    0 < finiteOnePairV a := by
  rw [finiteOnePairV]
  nlinarith [finiteOnePairB_gt_one ha]

theorem finiteOnePairU_lt_V (a : ℝ) :
    finiteOnePairU a < finiteOnePairV a := by
  simp only [finiteOnePairU, finiteOnePairV]
  linarith

theorem finiteOnePairU_mul_V (a : ℝ) :
    finiteOnePairU a * finiteOnePairV a = a ^ (2 : ℕ) := by
  rw [finiteOnePairU, finiteOnePairV]
  nlinarith [finiteOnePairB_sq a]

theorem finiteOnePairU_add_V (a : ℝ) :
    finiteOnePairU a + finiteOnePairV a = 2 * finiteOnePairB a := by
  simp [finiteOnePairU, finiteOnePairV]
  ring

/-- The real squared modulus of `x^(2 : ℕ) + a^(2 : ℕ) + 2 i x`. -/
def finiteOnePairDenominator (a x : ℝ) : ℝ :=
  (x ^ (2 : ℕ) + a ^ (2 : ℕ)) ^ (2 : ℕ) + (2 * x) ^ (2 : ℕ)

/-- Exact factorization of the squared modulus into its two Cauchy factors. -/
theorem finiteOnePairDenominator_factor (a x : ℝ) :
    finiteOnePairDenominator a x =
      (x ^ (2 : ℕ) + finiteOnePairU a ^ (2 : ℕ)) *
        (x ^ (2 : ℕ) + finiteOnePairV a ^ (2 : ℕ)) := by
  have hsq := finiteOnePairB_sq a
  simp only [finiteOnePairDenominator, finiteOnePairU, finiteOnePairV]
  nlinarith [sq_nonneg (finiteOnePairB a - 1),
    sq_nonneg (finiteOnePairB a + 1)]

theorem finiteOnePair_normKernel_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ =>
      (x ^ (2 : ℕ) + a ^ (2 : ℕ)) / finiteOnePairDenominator a x) := by
  let u := finiteOnePairU a
  let v := finiteOnePairV a
  have hu : 0 < u := finiteOnePairU_pos ha
  have huv : u < v := finiteOnePairU_lt_V a
  have hsq := integrable_sq_div_two_sq_add_sq hu huv
  have hprod := integrable_inv_two_sq_add_sq hu huv
  have hsum := hsq.add (hprod.const_mul (a ^ (2 : ℕ)))
  have hfun :
      (fun x : ℝ =>
        (x ^ (2 : ℕ) + a ^ (2 : ℕ)) / finiteOnePairDenominator a x) =
      (fun x : ℝ =>
        x ^ (2 : ℕ) / ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ))) +
          a ^ (2 : ℕ) * ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))⁻¹) := by
    funext x
    rw [finiteOnePairDenominator_factor]
    change (x ^ (2 : ℕ) + a ^ (2 : ℕ)) /
        ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ))) =
      x ^ (2 : ℕ) / ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ))) +
        a ^ (2 : ℕ) * ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))⁻¹
    have hxu : x ^ (2 : ℕ) + u ^ (2 : ℕ) ≠ 0 := by positivity
    have hxv : x ^ (2 : ℕ) + v ^ (2 : ℕ) ≠ 0 := by
      have hv : 0 < v := hu.trans huv
      positivity
    field_simp [hxu, hxv]
  rw [hfun]
  exact hsum

/-- The exact diagonal integral before the `1 / pi` normalization. -/
theorem finiteOnePair_normKernel_integral {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ,
      (x ^ (2 : ℕ) + a ^ (2 : ℕ)) / finiteOnePairDenominator a x) =
      Real.pi / finiteOnePairB a := by
  let u := finiteOnePairU a
  let v := finiteOnePairV a
  have hu : 0 < u := finiteOnePairU_pos ha
  have huv : u < v := finiteOnePairU_lt_V a
  have hv : 0 < v := hu.trans huv
  have hsq := integrable_sq_div_two_sq_add_sq hu huv
  have hprod := integrable_inv_two_sq_add_sq hu huv
  calc
    (∫ x : ℝ,
      (x ^ (2 : ℕ) + a ^ (2 : ℕ)) / finiteOnePairDenominator a x) =
        ∫ x : ℝ,
          x ^ (2 : ℕ) / ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ))) +
            a ^ (2 : ℕ) * ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))⁻¹ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [finiteOnePairDenominator_factor]
      change (x ^ (2 : ℕ) + a ^ (2 : ℕ)) /
          ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ))) = _
      have hxu : x ^ (2 : ℕ) + u ^ (2 : ℕ) ≠ 0 := by positivity
      have hxv : x ^ (2 : ℕ) + v ^ (2 : ℕ) ≠ 0 := by positivity
      field_simp [hxu, hxv]
    _ = (∫ x : ℝ,
          x ^ (2 : ℕ) / ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))) +
        a ^ (2 : ℕ) * ∫ x : ℝ,
          ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))⁻¹ := by
      rw [integral_add hsq (hprod.const_mul (a ^ (2 : ℕ))), integral_const_mul]
    _ = Real.pi / finiteOnePairB a := by
      rw [integral_sq_div_two_sq_add_sq hu huv,
        integral_inv_two_sq_add_sq hu huv]
      have huvEq : u * v = a ^ (2 : ℕ) := finiteOnePairU_mul_V a
      have hsum : u + v = 2 * finiteOnePairB a :=
        finiteOnePairU_add_V a
      have hb : 0 < finiteOnePairB a := by
        nlinarith [finiteOnePairB_gt_one ha]
      rw [← huvEq, hsum]
      field_simp [hu.ne', hv.ne', hb.ne']; ring

theorem finiteOnePair_crossRealKernel_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ =>
      (x ^ (2 : ℕ) - a ^ (2 : ℕ)) / finiteOnePairDenominator a x) := by
  let u := finiteOnePairU a
  let v := finiteOnePairV a
  have hu : 0 < u := finiteOnePairU_pos ha
  have huv : u < v := finiteOnePairU_lt_V a
  have hsq := integrable_sq_div_two_sq_add_sq hu huv
  have hprod := integrable_inv_two_sq_add_sq hu huv
  have hdiff := hsq.sub (hprod.const_mul (a ^ (2 : ℕ)))
  convert hdiff using 1
  ext x
  rw [finiteOnePairDenominator_factor]
  change (x ^ (2 : ℕ) - a ^ (2 : ℕ)) /
      ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ))) =
    x ^ (2 : ℕ) / ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ))) -
      a ^ (2 : ℕ) * ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))⁻¹
  have hxu : x ^ (2 : ℕ) + u ^ (2 : ℕ) ≠ 0 := by positivity
  have hxv : x ^ (2 : ℕ) + v ^ (2 : ℕ) ≠ 0 := by
    have hv : 0 < v := hu.trans huv
    positivity
  field_simp [hxu, hxv]

/-- The real part of the off-diagonal Gram entry vanishes exactly. -/
theorem finiteOnePair_crossRealKernel_integral {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ,
      (x ^ (2 : ℕ) - a ^ (2 : ℕ)) / finiteOnePairDenominator a x) = 0 := by
  let u := finiteOnePairU a
  let v := finiteOnePairV a
  have hu : 0 < u := finiteOnePairU_pos ha
  have huv : u < v := finiteOnePairU_lt_V a
  have hv : 0 < v := hu.trans huv
  have hsq := integrable_sq_div_two_sq_add_sq hu huv
  have hprod := integrable_inv_two_sq_add_sq hu huv
  calc
    (∫ x : ℝ,
      (x ^ (2 : ℕ) - a ^ (2 : ℕ)) / finiteOnePairDenominator a x) =
        ∫ x : ℝ,
          x ^ (2 : ℕ) / ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ))) -
            a ^ (2 : ℕ) * ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))⁻¹ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [finiteOnePairDenominator_factor]
      change (x ^ (2 : ℕ) - a ^ (2 : ℕ)) /
          ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ))) = _
      have hxu : x ^ (2 : ℕ) + u ^ (2 : ℕ) ≠ 0 := by positivity
      have hxv : x ^ (2 : ℕ) + v ^ (2 : ℕ) ≠ 0 := by positivity
      field_simp [hxu, hxv]
    _ = (∫ x : ℝ,
          x ^ (2 : ℕ) / ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))) -
        a ^ (2 : ℕ) * ∫ x : ℝ,
          ((x ^ (2 : ℕ) + u ^ (2 : ℕ)) * (x ^ (2 : ℕ) + v ^ (2 : ℕ)))⁻¹ := by
      rw [integral_sub hsq (hprod.const_mul (a ^ (2 : ℕ))), integral_const_mul]
    _ = 0 := by
      rw [integral_sq_div_two_sq_add_sq hu huv,
        integral_inv_two_sq_add_sq hu huv]
      have huvEq : u * v = a ^ (2 : ℕ) := finiteOnePairU_mul_V a
      rw [← huvEq]
      field_simp [hu.ne', hv.ne']; ring

theorem finiteOnePair_crossImagKernel_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ =>
      x / finiteOnePairDenominator a x) := by
  simpa only [finiteOnePairDenominator_factor] using
    (integrable_id_div_two_sq_add_sq
      (finiteOnePairU_pos ha) (finiteOnePairU_lt_V a))

/-- The imaginary odd kernel vanishes exactly. -/
theorem finiteOnePair_crossImagKernel_integral (a : ℝ) :
    (∫ x : ℝ, x / finiteOnePairDenominator a x) = 0 := by
  simpa only [finiteOnePairDenominator_factor] using
    (integral_id_div_two_sq_add_sq
      (u := finiteOnePairU a) (v := finiteOnePairV a))

/-- `E(x) = A(x) + i A'(x)` for `A(z) = z^(2 : ℕ) + a^(2 : ℕ)`, restricted to
the real line. -/
def finiteOnePairE (a x : ℝ) : ℂ :=
  (x ^ (2 : ℕ) + a ^ (2 : ℕ) : ℝ) + (2 * x : ℝ) * Complex.I

theorem finiteOnePairE_normSq (a x : ℝ) :
    Complex.normSq (finiteOnePairE a x) =
      finiteOnePairDenominator a x := by
  simpa only [finiteOnePairE, finiteOnePairDenominator] using
    (Complex.normSq_add_mul_I (x ^ (2 : ℕ) + a ^ (2 : ℕ)) (2 * x))

theorem finiteOnePairDenominator_pos {a : ℝ} (ha : 0 < a) (x : ℝ) :
    0 < finiteOnePairDenominator a x := by
  rw [finiteOnePairDenominator]
  have hbase : 0 < x ^ (2 : ℕ) + a ^ (2 : ℕ) := by positivity
  positivity

theorem finiteOnePairE_ne_zero {a : ℝ} (ha : 0 < a) (x : ℝ) :
    finiteOnePairE a x ≠ 0 := by
  intro hzero
  have hnorm := congrArg Complex.normSq hzero
  rw [finiteOnePairE_normSq] at hnorm
  simp at hnorm
  exact (finiteOnePairDenominator_pos ha x).ne' hnorm

/-- The common normalization `i / sqrt pi`. -/
def finiteOnePairNormalization : ℂ :=
  Complex.I / (Real.sqrt Real.pi : ℂ)

theorem finiteOnePairNormalization_normSq :
    Complex.normSq finiteOnePairNormalization = Real.pi⁻¹ := by
  rw [finiteOnePairNormalization, Complex.normSq_div,
    Complex.normSq_I, Complex.normSq_ofReal]
  have hsqrt : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_nonneg
  rw [hsqrt]
  simp

theorem finiteOnePairNormalization_conj_mul :
    conj finiteOnePairNormalization * finiteOnePairNormalization =
      (Real.pi⁻¹ : ℂ) := by
  rw [← Complex.normSq_eq_conj_mul_self,
    finiteOnePairNormalization_normSq]
  norm_cast

/-- The normalized zero function belonging to the root `+ i a` of
`z^(2 : ℕ) + a^(2 : ℕ)`. -/
def finiteOnePairFPlus (a x : ℝ) : ℂ :=
  finiteOnePairNormalization *
    (((x : ℂ) + (a : ℂ) * Complex.I) / finiteOnePairE a x)

/-- The normalized zero function belonging to the root `- i a` of
`z^(2 : ℕ) + a^(2 : ℕ)`. -/
def finiteOnePairFMinus (a x : ℝ) : ℂ :=
  finiteOnePairNormalization *
    (((x : ℂ) - (a : ℂ) * Complex.I) / finiteOnePairE a x)

theorem finiteOnePairFPlus_normSq (a x : ℝ) :
    Complex.normSq (finiteOnePairFPlus a x) =
      Real.pi⁻¹ *
        ((x ^ (2 : ℕ) + a ^ (2 : ℕ)) / finiteOnePairDenominator a x) := by
  rw [finiteOnePairFPlus, Complex.normSq_mul,
    finiteOnePairNormalization_normSq, Complex.normSq_div,
    finiteOnePairE_normSq]
  simp [Complex.normSq_apply]
  ring

theorem finiteOnePairFMinus_normSq (a x : ℝ) :
    Complex.normSq (finiteOnePairFMinus a x) =
      Real.pi⁻¹ *
        ((x ^ (2 : ℕ) + a ^ (2 : ℕ)) / finiteOnePairDenominator a x) := by
  rw [finiteOnePairFMinus, Complex.normSq_mul,
    finiteOnePairNormalization_normSq, Complex.normSq_div,
    finiteOnePairE_normSq]
  simp [Complex.normSq_apply]
  ring

theorem finiteOnePairE_conj_mul (a x : ℝ) :
    conj (finiteOnePairE a x) * finiteOnePairE a x =
      (finiteOnePairDenominator a x : ℂ) := by
  rw [← Complex.normSq_eq_conj_mul_self, finiteOnePairE_normSq]

/-- Pointwise algebra behind the off-diagonal Gram entry. -/
theorem finiteOnePair_crossTerm_pointwise (a x : ℝ) :
    conj (finiteOnePairFPlus a x) * finiteOnePairFMinus a x =
      (Real.pi⁻¹ : ℂ) *
        ((((x : ℂ) - (a : ℂ) * Complex.I) ^ (2 : ℕ)) /
          (finiteOnePairDenominator a x : ℂ)) := by
  calc
    conj (finiteOnePairFPlus a x) * finiteOnePairFMinus a x =
        (conj finiteOnePairNormalization *
          finiteOnePairNormalization) *
          ((((x : ℂ) - (a : ℂ) * Complex.I) ^ (2 : ℕ)) /
            (conj (finiteOnePairE a x) *
              finiteOnePairE a x)) := by
      simp only [finiteOnePairFPlus, finiteOnePairFMinus,
        map_mul, map_div₀, map_add, Complex.conj_ofReal,
        Complex.conj_I, mul_neg]
      ring
    _ = (Real.pi⁻¹ : ℂ) *
        ((((x : ℂ) - (a : ℂ) * Complex.I) ^ (2 : ℕ)) /
          (finiteOnePairDenominator a x : ℂ)) := by
      rw [finiteOnePairNormalization_conj_mul,
        finiteOnePairE_conj_mul]

/-- The same cross term separated into its even real and odd imaginary
parts.  This is the form used for the improper integral. -/
theorem finiteOnePair_crossTerm_pointwise_re_im {a : ℝ} (ha : 0 < a)
    (x : ℝ) :
    conj (finiteOnePairFPlus a x) * finiteOnePairFMinus a x =
      ((Real.pi⁻¹ *
        ((x ^ (2 : ℕ) - a ^ (2 : ℕ)) / finiteOnePairDenominator a x) : ℝ) : ℂ) -
      ((Real.pi⁻¹ *
        ((2 * a * x) / finiteOnePairDenominator a x) : ℝ) : ℂ) *
        Complex.I := by
  rw [finiteOnePair_crossTerm_pointwise]
  apply Complex.ext
  · simp [Complex.div_re]
    have hden := (finiteOnePairDenominator_pos ha x).ne'
    field_simp [hden, Real.pi_ne_zero]; simp [pow_two, Complex.mul_re, Complex.mul_im]
  · simp [Complex.div_im]
    have hden := (finiteOnePairDenominator_pos ha x).ne'
    field_simp [hden, Real.pi_ne_zero]; simp [pow_two, Complex.mul_re, Complex.mul_im]; ring

theorem finiteOnePairFPlus_normSq_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Complex.normSq (finiteOnePairFPlus a x)) := by
  have hscaled :=
    (finiteOnePair_normKernel_integrable ha).const_mul Real.pi⁻¹
  simpa only [finiteOnePairFPlus_normSq] using hscaled

theorem finiteOnePairFMinus_normSq_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Complex.normSq (finiteOnePairFMinus a x)) := by
  have hscaled :=
    (finiteOnePair_normKernel_integrable ha).const_mul Real.pi⁻¹
  simpa only [finiteOnePairFMinus_normSq] using hscaled

/-- Exact squared `L²` norm of the upper-root zero function. -/
theorem finiteOnePairFPlus_normSq_integral {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, Complex.normSq (finiteOnePairFPlus a x)) =
      (finiteOnePairB a)⁻¹ := by
  calc
    (∫ x : ℝ, Complex.normSq (finiteOnePairFPlus a x)) =
        ∫ x : ℝ, Real.pi⁻¹ *
          ((x ^ (2 : ℕ) + a ^ (2 : ℕ)) / finiteOnePairDenominator a x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact finiteOnePairFPlus_normSq a x
    _ = Real.pi⁻¹ * ∫ x : ℝ,
        (x ^ (2 : ℕ) + a ^ (2 : ℕ)) / finiteOnePairDenominator a x := by
      rw [integral_const_mul]
    _ = (finiteOnePairB a)⁻¹ := by
      rw [finiteOnePair_normKernel_integral ha]
      field_simp [Real.pi_ne_zero]

/-- Exact squared `L²` norm of the lower-root zero function. -/
theorem finiteOnePairFMinus_normSq_integral {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, Complex.normSq (finiteOnePairFMinus a x)) =
      (finiteOnePairB a)⁻¹ := by
  calc
    (∫ x : ℝ, Complex.normSq (finiteOnePairFMinus a x)) =
        ∫ x : ℝ, Real.pi⁻¹ *
          ((x ^ (2 : ℕ) + a ^ (2 : ℕ)) / finiteOnePairDenominator a x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact finiteOnePairFMinus_normSq a x
    _ = Real.pi⁻¹ * ∫ x : ℝ,
        (x ^ (2 : ℕ) + a ^ (2 : ℕ)) / finiteOnePairDenominator a x := by
      rw [integral_const_mul]
    _ = (finiteOnePairB a)⁻¹ := by
      rw [finiteOnePair_normKernel_integral ha]
      field_simp [Real.pi_ne_zero]

theorem finiteOnePair_crossTerm_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ =>
      conj (finiteOnePairFPlus a x) * finiteOnePairFMinus a x) := by
  let realPart : ℝ → ℝ := fun x => Real.pi⁻¹ *
    ((x ^ (2 : ℕ) - a ^ (2 : ℕ)) / finiteOnePairDenominator a x)
  let imagPart : ℝ → ℝ := fun x => Real.pi⁻¹ *
    ((2 * a * x) / finiteOnePairDenominator a x)
  have hreal : Integrable realPart := by
    exact (finiteOnePair_crossRealKernel_integrable ha).const_mul Real.pi⁻¹
  have himagBase := finiteOnePair_crossImagKernel_integrable ha
  have himagScaled :=
    (himagBase.const_mul (2 * a)).const_mul Real.pi⁻¹
  have himag : Integrable imagPart := by
    have hfun : imagPart = fun x : ℝ =>
        Real.pi⁻¹ * ((2 * a) *
          (x / finiteOnePairDenominator a x)) := by
      funext x
      simp only [imagPart]
      ring
    rw [hfun]
    exact himagScaled
  have hcomplex : Integrable (fun x : ℝ =>
      (realPart x : ℂ) - (imagPart x : ℂ) * Complex.I) :=
    hreal.ofReal.sub (himag.ofReal.mul_const Complex.I)
  have hfun :
      (fun x : ℝ =>
        conj (finiteOnePairFPlus a x) * finiteOnePairFMinus a x) =
      (fun x : ℝ =>
        (realPart x : ℂ) - (imagPart x : ℂ) * Complex.I) := by
    funext x
    exact finiteOnePair_crossTerm_pointwise_re_im ha x
  rw [hfun]
  exact hcomplex

/-- Exact vanishing of the off-diagonal `L²` Gram entry. -/
theorem finiteOnePair_crossTerm_integral {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ,
      conj (finiteOnePairFPlus a x) * finiteOnePairFMinus a x) = 0 := by
  let realPart : ℝ → ℝ := fun x => Real.pi⁻¹ *
    ((x ^ (2 : ℕ) - a ^ (2 : ℕ)) / finiteOnePairDenominator a x)
  let imagPart : ℝ → ℝ := fun x => Real.pi⁻¹ *
    ((2 * a * x) / finiteOnePairDenominator a x)
  have hreal : Integrable realPart := by
    exact (finiteOnePair_crossRealKernel_integrable ha).const_mul Real.pi⁻¹
  have himagBase := finiteOnePair_crossImagKernel_integrable ha
  have himagScaled :=
    (himagBase.const_mul (2 * a)).const_mul Real.pi⁻¹
  have himag : Integrable imagPart := by
    have hfun : imagPart = fun x : ℝ =>
        Real.pi⁻¹ * ((2 * a) *
          (x / finiteOnePairDenominator a x)) := by
      funext x
      simp only [imagPart]
      ring
    rw [hfun]
    exact himagScaled
  calc
    (∫ x : ℝ,
      conj (finiteOnePairFPlus a x) * finiteOnePairFMinus a x) =
        ∫ x : ℝ,
          (realPart x : ℂ) - (imagPart x : ℂ) * Complex.I := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact finiteOnePair_crossTerm_pointwise_re_im ha x
    _ = (∫ x : ℝ, (realPart x : ℂ)) -
        (∫ x : ℝ, (imagPart x : ℂ)) * Complex.I := by
      calc
        (∫ x : ℝ, (realPart x : ℂ) -
            (imagPart x : ℂ) * Complex.I) =
            (∫ x : ℝ, (realPart x : ℂ)) -
              ∫ x : ℝ, (imagPart x : ℂ) * Complex.I := by
          exact integral_sub hreal.ofReal
            (himag.ofReal.mul_const Complex.I)
        _ = (∫ x : ℝ, (realPart x : ℂ)) -
            (∫ x : ℝ, (imagPart x : ℂ)) * Complex.I := by
          rw [integral_mul_const]
    _ = 0 := by
      rw [integral_complex_ofReal, integral_complex_ofReal]
      have hrealZero : (∫ x : ℝ, realPart x) = 0 := by
        rw [show realPart = fun x : ℝ => Real.pi⁻¹ *
          ((x ^ (2 : ℕ) - a ^ (2 : ℕ)) / finiteOnePairDenominator a x) from rfl,
          integral_const_mul, finiteOnePair_crossRealKernel_integral ha]
        ring
      have himagZero : (∫ x : ℝ, imagPart x) = 0 := by
        rw [show imagPart = fun x : ℝ => Real.pi⁻¹ *
          ((2 * a * x) / finiteOnePairDenominator a x) from rfl]
        have hfun :
            (fun x : ℝ => Real.pi⁻¹ *
              ((2 * a * x) / finiteOnePairDenominator a x)) =
            (fun x : ℝ => (Real.pi⁻¹ * (2 * a)) *
              (x / finiteOnePairDenominator a x)) := by
          funext x
          ring
        rw [hfun, integral_const_mul,
          finiteOnePair_crossImagKernel_integral]
        ring
      rw [hrealZero, himagZero]
      simp

theorem finiteOnePair_diagPlus_integral {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ,
      conj (finiteOnePairFPlus a x) * finiteOnePairFPlus a x) =
      ((finiteOnePairB a)⁻¹ : ℂ) := by
  calc
    (∫ x : ℝ,
      conj (finiteOnePairFPlus a x) * finiteOnePairFPlus a x) =
        ∫ x : ℝ, (Complex.normSq (finiteOnePairFPlus a x) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact Complex.normSq_eq_conj_mul_self.symm
    _ = Complex.ofReal
        (∫ x : ℝ, Complex.normSq (finiteOnePairFPlus a x)) :=
      integral_complex_ofReal
    _ = ((finiteOnePairB a)⁻¹ : ℂ) := by
      rw [finiteOnePairFPlus_normSq_integral ha]
      norm_cast

theorem finiteOnePair_diagMinus_integral {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ,
      conj (finiteOnePairFMinus a x) * finiteOnePairFMinus a x) =
      ((finiteOnePairB a)⁻¹ : ℂ) := by
  calc
    (∫ x : ℝ,
      conj (finiteOnePairFMinus a x) * finiteOnePairFMinus a x) =
        ∫ x : ℝ, (Complex.normSq (finiteOnePairFMinus a x) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact Complex.normSq_eq_conj_mul_self.symm
    _ = Complex.ofReal
        (∫ x : ℝ, Complex.normSq (finiteOnePairFMinus a x)) :=
      integral_complex_ofReal
    _ = ((finiteOnePairB a)⁻¹ : ℂ) := by
      rw [finiteOnePairFMinus_normSq_integral ha]
      norm_cast

theorem finiteOnePair_reverseCrossTerm_integral {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ,
      conj (finiteOnePairFMinus a x) * finiteOnePairFPlus a x) = 0 := by
  have hfun :
      (fun x : ℝ =>
        conj (finiteOnePairFMinus a x) * finiteOnePairFPlus a x) =
      (fun x : ℝ => conj
        (conj (finiteOnePairFPlus a x) * finiteOnePairFMinus a x)) := by
    funext x
    simp
    ring
  rw [hfun, integral_conj, finiteOnePair_crossTerm_integral ha]
  simp

/-- The ordered pair of normalized zero functions. -/
def finiteOnePairZeroFunction (a : ℝ) (i : Fin 2) (x : ℝ) : ℂ :=
  if i = 0 then finiteOnePairFPlus a x else finiteOnePairFMinus a x

/-- The literal `2 × 2` `L²` Gram matrix of the quadratic zero functions. -/
def finiteOnePairGram (a : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => ∫ x : ℝ,
    conj (finiteOnePairZeroFunction a i x) *
      finiteOnePairZeroFunction a j x

/-- Exact one-pair analytic realization:
`G = (1 / sqrt (1 + a^(2 : ℕ))) I₂`. -/
theorem finiteOnePairGram_eq_smul_one {a : ℝ} (ha : 0 < a) :
    finiteOnePairGram a =
      ((finiteOnePairB a)⁻¹ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [finiteOnePairGram, finiteOnePairZeroFunction] using
      finiteOnePair_diagPlus_integral ha
  · simpa [finiteOnePairGram, finiteOnePairZeroFunction] using
      finiteOnePair_crossTerm_integral ha
  · simpa [finiteOnePairGram, finiteOnePairZeroFunction] using
      finiteOnePair_reverseCrossTerm_integral ha
  · simpa [finiteOnePairGram, finiteOnePairZeroFunction] using
      finiteOnePair_diagMinus_integral ha

/-- The one-pair Weil signature matrix, which exchanges the two conjugate
roots. -/
def finiteOnePairSignatureMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- The analytic one-pair generalized metric pencil. -/
def finiteOnePairPencil (a : ℝ) (lambda : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  finiteOnePairGram a - lambda • finiteOnePairSignatureMatrix

theorem finiteOnePairPencil_det {a : ℝ} (ha : 0 < a) (lambda : ℂ) :
    (finiteOnePairPencil a lambda).det =
      ((finiteOnePairB a)⁻¹ : ℂ) ^ (2 : ℕ) - lambda ^ (2 : ℕ) := by
  rw [finiteOnePairPencil, finiteOnePairGram_eq_smul_one ha,
    Matrix.det_fin_two]
  simp [finiteOnePairSignatureMatrix]
  ring

/-- Exact singular values of the analytic one-pair pencil. -/
theorem finiteOnePairPencil_singular_iff {a : ℝ} (ha : 0 < a)
    (lambda : ℂ) :
    (finiteOnePairPencil a lambda).det = 0 ↔
      lambda = ((finiteOnePairB a)⁻¹ : ℂ) ∨
        lambda = -((finiteOnePairB a)⁻¹ : ℂ) := by
  rw [finiteOnePairPencil_det ha]
  constructor
  · intro hzero
    have hsquare : lambda ^ (2 : ℕ) = ((finiteOnePairB a)⁻¹ : ℂ) ^ (2 : ℕ) :=
      (sub_eq_zero.mp hzero).symm
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hsquare
  · rintro (rfl | rfl) <;> ring

end

end RiemannGaussian
