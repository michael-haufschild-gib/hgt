/-
# The order-`q` determinant of a Schatten operator is the determinant of its spectrum

Membership in a Schatten class is all that is needed: every power above the exponent splits into
Hilbert–Schmidt factors, so every power trace is a genuine operator trace, and Lidskii turns each of
them into the corresponding power sum of the eigenvalues.  The operator determinant and the
determinant of the signed greedy spectrum therefore agree, with no factorisation hypothesis carried.

Main results:
* `opSchattenDet_eq_schattenDet_of_memSchattenClass` — **the identification from class membership
  alone**.
-/
import GaloisForLFunctions.HTGeometry.SchattenPowerHilbertSchmidt
import GaloisForLFunctions.HTGeometry.SchattenOperatorDeterminant

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open ContinuousLinearMap RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The operator determinant is the determinant of its spectrum, from class membership alone.** -/
theorem opSchattenDet_eq_schattenDet_of_memSchattenClass {p : ℝ} (hp : 0 < p)
    {S : H →L[ℂ] H} (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric)
    (hS : MemSchattenClass p S) {q : ℕ} (hq : 0 < q) (hpq : p + 1 ≤ (q : ℝ)) (z : ℂ) :
    opSchattenDet q S z = schattenDet q (fun n => ((sgVal S n : ℝ) : ℂ)) z := by
  refine opSchattenDet_eq_schattenDet hq hcpt hsym (fun m hm => ?_) z
  have hqm : ((q : ℝ)) ≤ (m : ℝ) := by exact_mod_cast hm
  exact exists_hilbertSchmidt_factorization_pow_of_le hp hS (le_trans hpq hqm)

/-- The same statement for the regularized exponent. -/
theorem opSchattenDetExp_eq_schattenDetExp_of_memSchattenClass {p : ℝ} (hp : 0 < p)
    {S : H →L[ℂ] H} (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric)
    (hS : MemSchattenClass p S) {q : ℕ} (hq : 0 < q) (hpq : p + 1 ≤ (q : ℝ)) (z : ℂ) :
    opSchattenDetExp q S z = schattenDetExp q (fun n => ((sgVal S n : ℝ) : ℂ)) z := by
  refine opSchattenDetExp_eq_schattenDetExp hq hcpt hsym (fun m hm => ?_) z
  have hqm : ((q : ℝ)) ≤ (m : ℝ) := by exact_mod_cast hm
  exact exists_hilbertSchmidt_factorization_pow_of_le hp hS (le_trans hpq hqm)

end

end GaloisForLFunctions.HTGeometry
