import GaloisForLFunctions.RHTower.PrimeArchHankelDeterminantCriterion
import GaloisForLFunctions.RHTower.PrimeArchThetaHankelDegreeTail
import GaloisForLFunctions.RHTower.XiPrimeMarkedFiniteSixthHeadBudget

/-!
# The third leading Hankel determinant of the prime--archimedean source

The RH criterion is positivity of every leading determinant of the central moment Hankel matrix.
Sizes one and two are settled unconditionally.  This module records the explicit size-three
determinant in the source moments, which is the next case, and the two reductions a source estimate
must discharge: the determinant itself and its strict Sylvester form.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Explicit expansion of the size-three leading Hankel determinant. -/
theorem det_primeArchSourceMomentHankelMatrix_three :
    (primeArchSourceMomentHankelMatrix 3).det =
      normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 * normalizedPrimeArchMoment 4 -
        normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 3 ^ (2 : ℕ) -
        normalizedPrimeArchMoment 1 ^ (2 : ℕ) * normalizedPrimeArchMoment 4 +
        2 * normalizedPrimeArchMoment 1 * normalizedPrimeArchMoment 2 *
          normalizedPrimeArchMoment 3 -
        normalizedPrimeArchMoment 2 ^ (3 : ℕ) := by
  rw [Matrix.det_fin_three]
  simp only [primeArchSourceMomentHankelMatrix_apply]
  norm_num
  ring

/-- Sylvester form of the size-three case: positivity of the size-three determinant is exactly the
statement that the fourth source moment, weighted by the already settled size-two determinant,
exceeds the cubic formed by the lower moments. -/
theorem det_primeArchSourceMomentHankelMatrix_three_pos_iff_schur :
    0 < (primeArchSourceMomentHankelMatrix 3).det ↔
      normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 3 ^ (2 : ℕ) -
          2 * normalizedPrimeArchMoment 1 * normalizedPrimeArchMoment 2 *
            normalizedPrimeArchMoment 3 +
          normalizedPrimeArchMoment 2 ^ (3 : ℕ) <
        (normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
          normalizedPrimeArchMoment 1 ^ (2 : ℕ)) * normalizedPrimeArchMoment 4 := by
  rw [det_primeArchSourceMomentHankelMatrix_three]
  constructor <;> intro h <;> nlinarith [h]

/-- The size-two leading determinant is unconditionally strict: the Stein enclosure of the first
theta atom already discharges it. -/
theorem det_primeArchSourceMomentHankelMatrix_two_pos :
    0 < (primeArchSourceMomentHankelMatrix 2).det := by
  rw [det_primeArchSourceMomentHankelMatrix_two]
  exact normalizedPrimeArch_firstHankelMinor_pos_from_stein

/-- **RH reduces to the determinant tail from size three.**  Sizes zero, one and two of the
leading-determinant hierarchy are unconditional theorems, so no ratio hypothesis remains: the
Riemann hypothesis follows from positivity of the leading determinants of size at least three
alone. -/
theorem riemannHypothesis_of_primeArchSourceMomentHankelDeterminantTailFromThree
    (htail : PrimeArchSourceMomentHankelDeterminantTailFromThreePositive) :
    RiemannHypothesis := by
  apply primeArchSourceMomentHankelDeterminantsPositive_iff_riemannHypothesis.mp
  intro n
  rcases lt_trichotomy n 2 with hn | rfl | hn
  · interval_cases n
    · simp
    · exact det_primeArchSourceMomentHankelMatrix_one_pos
  · exact det_primeArchSourceMomentHankelMatrix_two_pos
  · exact htail n (by omega)

end

end RHTower
