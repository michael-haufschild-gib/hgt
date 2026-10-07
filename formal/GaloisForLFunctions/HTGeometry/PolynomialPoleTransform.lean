import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Polynomial transport through a reciprocal coordinate

Reflecting a translated polynomial realizes X^N*p(b+1/X). Evaluation,
exact degree when p(b) is nonzero, and coprimality of numerator/denominator
are preserved with the common maximal degree used to clear powers.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The polynomial X^N*p(b+1/X), with N at least the degree of p. -/
noncomputable def polynomialPoleTransform (p : Polynomial ℂ) (b : ℂ) (N : ℕ) : Polynomial ℂ :=
  (p.comp (Polynomial.X + Polynomial.C b)).reflect N

private theorem shifted_natDegree (p : Polynomial ℂ) (b : ℂ) :
    (p.comp (Polynomial.X + Polynomial.C b)).natDegree = p.natDegree := by
  simp only [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]

/-- A nonzero value at the chosen pole becomes the top coefficient of the transform. -/
theorem natDegree_polynomialPoleTransform (p : Polynomial ℂ) (b : ℂ) (N : ℕ)
    (hN : p.natDegree ≤ N) (hb : p.eval b ≠ 0) :
    (polynomialPoleTransform p b N).natDegree = N := by
  apply le_antisymm
  · exact Polynomial.natDegree_reflect_le.trans (by simpa [shifted_natDegree] using max_le le_rfl hN)
  · apply Polynomial.le_natDegree_of_ne_zero
    simpa [polynomialPoleTransform, Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.eval_comp] using hb

/-- Evaluation of the reciprocal coordinate transform, valid over every extension field. -/
theorem aeval_polynomialPoleTransform {E : Type*} [Field E] [Algebra ℂ E]
    (p : Polynomial ℂ) (b : ℂ) (N : ℕ) (hN : p.natDegree ≤ N)
    (y : E) (hy : y ≠ 0) :
    Polynomial.aeval y (polynomialPoleTransform p b N) =
      y ^ N * Polynomial.aeval (y⁻¹ + algebraMap ℂ E b) p := by
  letI : Invertible (y⁻¹) := invertibleOfNonzero (inv_ne_zero hy)
  have he := Polynomial.eval₂_reflect_mul_pow (algebraMap ℂ E) (y⁻¹) N
    (p.comp (Polynomial.X + Polynomial.C b)) (by simpa [shifted_natDegree] using hN)
  rw [invOf_eq_inv, inv_inv] at he
  change Polynomial.aeval y (polynomialPoleTransform p b N) * (y⁻¹) ^ N =
    Polynomial.aeval (y⁻¹) (p.comp (Polynomial.X + Polynomial.C b)) at he
  rw [Polynomial.aeval_comp, map_add, Polynomial.aeval_X, Polynomial.aeval_C] at he
  calc
    _ = (Polynomial.aeval y (polynomialPoleTransform p b N) * (y⁻¹) ^ N) * y ^ N := by
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hy, one_pow, mul_one]
    _ = _ := by rw [he]; ring

/-- Clearing the common maximal degree preserves coprimality under reciprocal translation. -/
theorem isCoprime_polynomialPoleTransform (p q : Polynomial ℂ) (b : ℂ)
    (hp : p ≠ 0) (hq : q ≠ 0) (hpq : IsCoprime p q) :
    IsCoprime (polynomialPoleTransform p b (max p.natDegree q.natDegree))
      (polynomialPoleTransform q b (max p.natDegree q.natDegree)) := by
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
  intro c
  by_cases hc : c = 0
  · subst c
    simp only [Polynomial.coe_aeval_eq_eval]
    rcases le_total p.natDegree q.natDegree with hpqdeg | hqpdeg
    · right
      have hd := shifted_natDegree q b
      rw [max_eq_right hpqdeg]
      change (polynomialPoleTransform q b q.natDegree).eval 0 ≠ 0
      rw [← Polynomial.coeff_zero_eq_eval_zero, polynomialPoleTransform, Polynomial.coeff_reflect,
        Polynomial.revAt_zero, ← hd, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.comp_X_add_C_ne_zero_iff.mpr hq)
    · left
      have hd := shifted_natDegree p b
      rw [max_eq_left hqpdeg]
      change (polynomialPoleTransform p b p.natDegree).eval 0 ≠ 0
      rw [← Polynomial.coeff_zero_eq_eval_zero, polynomialPoleTransform, Polynomial.coeff_reflect,
        Polynomial.revAt_zero, ← hd, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.comp_X_add_C_ne_zero_iff.mpr hp)
  · rw [aeval_polynomialPoleTransform p b _ (le_max_left _ _) c hc,
      aeval_polynomialPoleTransform q b _ (le_max_right _ _) c hc]
    exact (Polynomial.aeval_ne_zero_of_isCoprime hpq (c⁻¹ + algebraMap ℂ ℂ b)).imp
      (mul_ne_zero (pow_ne_zero _ hc)) (mul_ne_zero (pow_ne_zero _ hc))

end GaloisForLFunctions.HTGeometry
