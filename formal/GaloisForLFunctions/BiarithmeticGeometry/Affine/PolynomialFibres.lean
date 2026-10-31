import GaloisForLFunctions.BiarithmeticGeometry.Affine.FiniteRankKernels
import GaloisForLFunctions.HTGeometry.PolynomialShiftDifference
import Mathlib.Algebra.Ring.Periodic

/-!
# Polynomial translation fibres of affine kernels

Finite column rank gives polynomial dependence on each translation fibre. Conjugate inversion
preserves this property. A polynomial with a nonzero rational period is constant, so zero
dilation values determine every right-periodic polynomial-fibre kernel.
-/

open Polynomial
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Every fixed-slope translation reading is polynomial. -/
def HasPolynomialTranslationFibres (k : AffineGroupQ → ℂ) : Prop :=
  ∀ u : ℚˣ, ∃ P : ℂ[X], ∀ b : ℚ, k (translation b * dilation u) = P.eval (b : ℂ)

theorem hasPolynomialTranslationFibres_of_finite_columns (k : AffineGroupQ → ℂ)
    [Module.Finite ℂ (kernelColumnSpan k)] : HasPolynomialTranslationFibres k := by
  intro u
  by_cases hk : k = 0
  · exact ⟨0, fun b => by simp only [hk, Pi.zero_apply, eval_zero]⟩
  · obtain ⟨P, _, hP⟩ := exists_polynomial_translation_fibre hk u
    exact ⟨P, hP⟩

theorem HasPolynomialTranslationFibres.sub {k l : AffineGroupQ → ℂ}
    (hk : HasPolynomialTranslationFibres k) (hl : HasPolynomialTranslationFibres l) :
    HasPolynomialTranslationFibres (fun g => k g - l g) := by
  intro u
  obtain ⟨P, hP⟩ := hk u
  obtain ⟨Q, hQ⟩ := hl u
  refine ⟨P - Q, fun b => ?_⟩
  change k (translation b * dilation u) - l (translation b * dilation u) = _
  rw [hP, hQ, eval_sub]

private theorem tdil_inverse (b : ℚ) (u : ℚˣ) :
    (translation b * dilation u)⁻¹ = translation (-b / u) * dilation u⁻¹ := by
  apply affine_ext
  · simp only [affSlope_inv, affSlope_mul, affSlope_translation,
      affSlope_dilation, one_mul, Units.val_inv_eq_inv_val]
  · simp only [affShift_inv, affShift_mul, affSlope_translation, affShift_dilation,
      affShift_translation, affSlope_mul, affSlope_dilation, one_mul, mul_zero,
      zero_add]

/-- Inversion and conjugation preserve polynomial translation fibres. -/
theorem HasPolynomialTranslationFibres.adjoint {k : AffineGroupQ → ℂ}
    (hk : HasPolynomialTranslationFibres k) :
    HasPolynomialTranslationFibres (fun g => starRingEnd ℂ (k g⁻¹)) := by
  intro u
  obtain ⟨P, hP⟩ := hk u⁻¹
  refine ⟨(P.map (starRingEnd ℂ)).comp (C (-((u : ℚ) : ℂ)⁻¹) * X), fun b => ?_⟩
  dsimp only
  rw [tdil_inverse, hP, eval_comp, eval_mul, eval_C, eval_X]
  have he : -((u : ℚ) : ℂ)⁻¹ * (b : ℂ) = ((-b / (u : ℚ) : ℚ) : ℂ) := by
    push_cast
    ring
  rw [he]
  have hm := Polynomial.eval_map_apply (f := starRingEnd ℂ) (p := P)
    (((-b / (u : ℚ) : ℚ) : ℂ))
  simpa only [map_ratCast] using hm.symm

/-- A polynomial constant under a nonzero rational shift is constant everywhere. -/
theorem eq_C_of_rational_period {a : ℚ} (ha : a ≠ 0) (P : ℂ[X])
    (h : Function.Periodic (fun b : ℚ => P.eval (b : ℂ)) a) : P = C (P.eval 0) := by
  apply HTGeometry.eq_C_of_shiftDiff_eq_zero (Rat.cast_ne_zero.mpr ha)
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective
    (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℂ)))).mono
  rintro x ⟨n, rfl⟩
  simpa only [Set.mem_setOf_eq, eval_comp, eval_add, eval_X, eval_C,
    Rat.cast_add, Rat.cast_natCast] using h (n : ℚ)

/-- A polynomial difference of commensurably periodic functions is constant. -/
theorem polynomial_difference_of_rational_periods (P : ℂ[X]) (f g : ℚ → ℂ)
    {a : ℚ} (ha : a ≠ 0) (hf : Function.Periodic f a) (hg : Function.Periodic g 1)
    (hP : ∀ b : ℚ, P.eval (b : ℂ) = f b - g b) (b : ℚ) :
    f b - g b = f 0 - g 0 := by
  have hden : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt a.den_pos)
  have hnum : (a.num : ℚ) ≠ 0 := by
    intro h
    apply ha
    rw [← Rat.num_div_den a, h, zero_div]
  have hn : (a.den : ℚ) * a = a.num := by
    rw [mul_comm]
    exact (eq_div_iff hden).mp (Rat.num_div_den a).symm
  have hf' := hf.nat_mul a.den
  rw [hn] at hf'
  have hg' := hg.int_mul a.num
  simp only [mul_one] at hg'
  have hp : Function.Periodic (fun t : ℚ => P.eval (t : ℂ)) (a.num : ℚ) := by
    intro t
    change P.eval ((t + a.num : ℚ) : ℂ) = P.eval (t : ℂ)
    rw [hP, hP, hf' t, hg' t]
  have he := eq_C_of_rational_period hnum P hp
  rw [← hP b, he, eval_C]
  simpa only [Rat.cast_zero] using hP 0

/-- Right unit translation adds the slope to the left translation coordinate. -/
theorem translation_fibre_shift_right (b : ℚ) (u : ℚˣ) :
    translation (b + u) * dilation u = (translation b * dilation u) * translation 1 := by
  simpa only [Int.cast_zero, Int.cast_one, add_zero, mul_one, translation_zero, one_mul] using
    translation_add_mul_dil b (0 : ℤ) (1 : ℤ) u

/-- A periodic polynomial fibre is fixed by its value on the dilation axis. -/
theorem eq_zero_of_polynomial_fibres_right_period {q : AffineGroupQ → ℂ}
    (hq : HasPolynomialTranslationFibres q) (hd : ∀ u : ℚˣ, q (dilation u) = 0)
    (hp : ∀ g, q (g * translation 1) = q g) : q = 0 := by
  funext g
  rw [eq_translation_mul_dilation g]
  let u := Units.mk0 (affSlope g) (affSlope_ne_zero g)
  obtain ⟨P, hP⟩ := hq u
  have hper : Function.Periodic (fun b : ℚ => P.eval (b : ℂ)) (u : ℚ) := by
    intro b
    change P.eval ((b + u : ℚ) : ℂ) = P.eval (b : ℂ)
    rw [← hP, ← hP]
    rw [translation_fibre_shift_right, hp]
  have hc := eq_C_of_rational_period u.ne_zero P hper
  change q (translation (affShift g) * dilation u) = 0
  rw [hP, hc, eval_C]
  have h0 := hP 0
  rw [translation_zero, one_mul, hd, Rat.cast_zero] at h0
  exact h0.symm

#print axioms HasPolynomialTranslationFibres.adjoint
#print axioms polynomial_difference_of_rational_periods
#print axioms eq_zero_of_polynomial_fibres_right_period
end GaloisForLFunctions.BiarithmeticGeometry
