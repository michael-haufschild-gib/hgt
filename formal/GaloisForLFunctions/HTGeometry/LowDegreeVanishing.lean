import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# A low-degree coefficient family vanishing at enough points is zero

A polynomial function `z ↦ ∑_{l < k} a_l z^l` vanishing at `k` distinct points has all coefficients
zero.  This is the uniqueness input of a division statement: two remainders of degree below the
divisor's that agree at the divisor's roots agree outright.

Stated for the coefficient family rather than for a `Polynomial`, because that is the form a
division remainder takes — a finite sum with analytically defined coefficients.

* `HTGeometry.coeff_eq_zero_of_eval_eq_zero_of_card`;
* `HTGeometry.eq_zero_of_multisetProd_dvd_of_natDegree_lt`.
-/

namespace HTGeometry

/-- **A degree-`< k` coefficient family vanishing at `k` distinct points is zero.** -/
theorem coeff_eq_zero_of_eval_eq_zero_of_card {k : ℕ} (a : ℕ → ℂ) (s : Finset ℂ)
    (hcard : k ≤ s.card) (hvan : ∀ z ∈ s, ∑ l ∈ Finset.range k, a l * z ^ l = 0) :
    ∀ l < k, a l = 0 := by
  classical
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · intro l hl
    omega
  set p : Polynomial ℂ := ∑ l ∈ Finset.range k, Polynomial.C (a l) * Polynomial.X ^ l with hp
  have heval : ∀ z : ℂ, Polynomial.eval z p = ∑ l ∈ Finset.range k, a l * z ^ l := by
    intro z
    rw [hp, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp
  have hdegle : p.natDegree ≤ k - 1 := by
    rw [hp]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun l hl => ?_
    have hlk : l ≤ k - 1 := by
      have hl' := Finset.mem_range.1 hl
      omega
    exact le_trans (le_trans (Polynomial.natDegree_C_mul_le _ _)
      (le_of_eq (Polynomial.natDegree_X_pow l))) hlk
  have hdeg : p.natDegree < s.card := by omega
  have hzero : p = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p s ?_ hdeg
    intro z hz
    rw [heval z]
    exact hvan z hz
  intro l hl
  have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff l) hzero
  simp only [Polynomial.coeff_zero] at hcoeff
  rw [hp] at hcoeff
  simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Finset.sum_ite_eq', Finset.mem_range, hl] using hcoeff

/-- **The multiplicity form.**  A polynomial of degree below the cardinality of a multiset, divisible
by the product of the linear factors at that multiset, is zero.  This is the uniqueness statement
with repeated roots allowed: divisibility already accounts for the multiplicities, so no separate
order-of-vanishing bookkeeping is needed. -/
theorem eq_zero_of_multisetProd_dvd_of_natDegree_lt {M : Multiset ℂ} {P : Polynomial ℂ}
    (hdvd : (M.map fun r => Polynomial.X - Polynomial.C r).prod ∣ P)
    (hdeg : P.natDegree < Multiset.card M) : P = 0 := by
  refine Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd ?_
  rwa [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]

end HTGeometry
