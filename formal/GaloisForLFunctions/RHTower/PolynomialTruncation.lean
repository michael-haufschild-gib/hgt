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

/-- Explicit quotient for the tail beginning at `cutoff`, using coefficients through
`cutoff + N`. -/
def shiftedTailUpTo (P : R[X]) (cutoff N : ℕ) : R[X] :=
  ∑ r ∈ Finset.range (N + 1), Polynomial.monomial r (P.coeff (cutoff + r))

/-- Evaluation of the explicit shifted tail quotient. -/
theorem eval_shiftedTailUpTo (P : R[X]) (cutoff N : ℕ) (t : R) :
    (shiftedTailUpTo P cutoff N).eval t =
      ∑ r ∈ Finset.range (N + 1), P.coeff (cutoff + r) * t ^ r := by
  rw [shiftedTailUpTo, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  simp [Polynomial.eval_monomial]

/-- Evaluation-level exact tail split through a known degree bound. -/
theorem eval_eq_lowTrunc_add_pow_mul_shiftedTailUpTo_of_natDegree_le
    (P : R[X]) (cutoff N : ℕ) (t : R) (hdeg : P.natDegree ≤ cutoff + N) :
    P.eval t = (lowTrunc P cutoff).eval t + t ^ cutoff * (shiftedTailUpTo P cutoff N).eval t := by
  have hdeg' : P.natDegree < cutoff + (N + 1) := by omega
  calc
    P.eval t = ∑ i ∈ Finset.range (cutoff + (N + 1)), P.coeff i * t ^ i := by
      exact Polynomial.eval_eq_sum_range' (p := P) hdeg' t
    _ = (∑ i ∈ Finset.range cutoff, P.coeff i * t ^ i) +
        ∑ r ∈ Finset.range (N + 1), P.coeff (cutoff + r) * t ^ (cutoff + r) := by
      rw [Finset.sum_range_add]
    _ = (lowTrunc P cutoff).eval t + t ^ cutoff * (shiftedTailUpTo P cutoff N).eval t := by
      rw [eval_lowTrunc, eval_shiftedTailUpTo, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      rw [pow_add]
      ring

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

noncomputable section

/-- Absolute evaluation bound for the explicit shifted tail quotient over the reals. -/
theorem abs_eval_shiftedTailUpTo_le (P : ℝ[X]) (cutoff N : ℕ) (t : ℝ) :
    |(shiftedTailUpTo P cutoff N).eval t| ≤
      ∑ r ∈ Finset.range (N + 1), |P.coeff (cutoff + r)| * |t| ^ r := by
  rw [eval_shiftedTailUpTo]
  calc
    |∑ r ∈ Finset.range (N + 1), P.coeff (cutoff + r) * t ^ r|
        ≤ ∑ r ∈ Finset.range (N + 1), |P.coeff (cutoff + r) * t ^ r| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ r ∈ Finset.range (N + 1), |P.coeff (cutoff + r)| * |t| ^ r := by
      apply Finset.sum_congr rfl
      intro r _
      rw [abs_mul, abs_pow]

end

end PolynomialTruncation
end RHTower
