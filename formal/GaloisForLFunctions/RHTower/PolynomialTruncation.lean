/-
Reusable polynomial truncation and exact-tail infrastructure.

This is the RHTower analogue of the lower/high-tail split used in the Böttcher
formalization, specialized to the common "retain degrees `< N`" cutoff used by
the spur multiplier jet.
-/
import Mathlib

namespace RHTower
namespace PolynomialTruncation

open Polynomial

noncomputable section

variable {R : Type*} [CommSemiring R]

/-- Low-degree truncation of a polynomial, retaining coefficients in degrees `< N`. -/
def lowTrunc (P : R[X]) (N : ℕ) : R[X] :=
  ∑ i ∈ Finset.range N, Polynomial.monomial i (P.coeff i)

/-- Coefficients of the low-degree truncation. -/
theorem coeff_lowTrunc (P : R[X]) (N i : ℕ) :
    (lowTrunc P N).coeff i = if i ∈ Finset.range N then P.coeff i else 0 := by
  rw [lowTrunc, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range N) i (fun i => P.coeff i)]

/-- Retained coefficients are unchanged. -/
theorem coeff_lowTrunc_of_lt (P : R[X]) {N i : ℕ} (hi : i < N) :
    (lowTrunc P N).coeff i = P.coeff i := by
  rw [coeff_lowTrunc, if_pos (Finset.mem_range.mpr hi)]

/-- Coefficients at or above the cutoff vanish in the low truncation. -/
theorem coeff_lowTrunc_eq_zero_of_le (P : R[X]) {N i : ℕ} (hi : N ≤ i) :
    (lowTrunc P N).coeff i = 0 := by
  rw [coeff_lowTrunc, if_neg]
  intro hmem
  exact not_lt_of_ge hi (Finset.mem_range.mp hmem)

/-- Evaluation of the low truncation as the finite coefficient sum. -/
theorem eval_lowTrunc (P : R[X]) (N : ℕ) (t : R) :
    (lowTrunc P N).eval t = ∑ i ∈ Finset.range N, P.coeff i * t ^ i := by
  rw [lowTrunc, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Polynomial.eval_monomial]

end

noncomputable section

variable {R : Type*} [CommRing R]

/-- The discarded high-degree tail after retaining degrees `< N`. -/
def highTail (P : R[X]) (N : ℕ) : R[X] :=
  P - lowTrunc P N

/-- The high tail has zero coefficients below the cutoff. -/
theorem coeff_highTail_eq_zero_of_lt (P : R[X]) {N i : ℕ} (hi : i < N) :
    (highTail P N).coeff i = 0 := by
  rw [highTail, Polynomial.coeff_sub, coeff_lowTrunc_of_lt P hi, sub_self]

/-- The discarded tail is divisible by `X^N`. -/
theorem X_pow_dvd_highTail (P : R[X]) (N : ℕ) :
    Polynomial.X ^ N ∣ highTail P N := by
  rw [Polynomial.X_pow_dvd_iff]
  intro i hi
  exact coeff_highTail_eq_zero_of_lt P hi

/-- Exact tail factorization after low-degree truncation. -/
theorem exists_tailFactor (P : R[X]) (N : ℕ) :
    ∃ Q : R[X], P = lowTrunc P N + Polynomial.X ^ N * Q := by
  rcases X_pow_dvd_highTail P N with ⟨Q, hQ⟩
  refine ⟨Q, ?_⟩
  rw [← hQ]
  simp [highTail]

/-- Evaluated exact tail factorization after low-degree truncation. -/
theorem exists_eval_tailFactor (P : R[X]) (N : ℕ) (t : R) :
    ∃ Q : R[X], P.eval t = (lowTrunc P N).eval t + t ^ N * Q.eval t := by
  rcases exists_tailFactor P N with ⟨Q, hQ⟩
  refine ⟨Q, ?_⟩
  calc
    P.eval t = (lowTrunc P N + Polynomial.X ^ N * Q).eval t :=
      congrArg (fun q : R[X] => q.eval t) hQ
    _ = (lowTrunc P N).eval t + t ^ N * Q.eval t := by
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

end

end PolynomialTruncation
end RHTower
