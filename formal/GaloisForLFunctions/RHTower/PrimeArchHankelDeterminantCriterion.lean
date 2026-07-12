import GaloisForLFunctions.RHTower.XiCentralHankelDeterminantCriterion
import GaloisForLFunctions.RHTower.PrimeArchThetaAllOrderCumulant

open Complex Set Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The source-side central moment Hankel matrix, read only from Taylor coefficients of the fixed
normalized continued prime--Gamma germ. -/
def primeArchSourceMomentHankelMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => analyticTraceMoments
    (normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace)
      ((i : ℕ) + (j : ℕ))

/-- Every matrix entry is the corresponding prime--archimedean cumulant.  Together with
`thetaCusp_allOrderCumulantRecurrence` and `normalizedPrimeArchMoment_recursive`, this makes the
leading determinant in each degree a finite expression in theta-cusp raw moments and the lower
cumulants. -/
theorem primeArchSourceMomentHankelMatrix_apply
    (n : ℕ) (i j : Fin n) :
    primeArchSourceMomentHankelMatrix n i j =
      normalizedPrimeArchMoment ((i : ℕ) + (j : ℕ)) := rfl

/-- The first nonempty determinant in the hierarchy is already unconditionally strict. -/
theorem det_primeArchSourceMomentHankelMatrix_one_pos :
    0 < (primeArchSourceMomentHankelMatrix 1).det := by
  rw [Matrix.det_fin_one]
  exact normalizedPrimeArchMoment_zero_pos

/-- The next leading determinant is exactly the first nonconstant prime--archimedean Hankel
minor. -/
theorem det_primeArchSourceMomentHankelMatrix_two :
    (primeArchSourceMomentHankelMatrix 2).det =
      normalizedPrimeArchMoment 0 * normalizedPrimeArchMoment 2 -
        normalizedPrimeArchMoment 1 ^ 2 := by
  rw [Matrix.det_fin_two]
  simp only [primeArchSourceMomentHankelMatrix_apply]
  norm_num
  ring

/-- At size two, determinant nonnegativity is the explicit theta-cusp sixth-moment inequality
already isolated by the cumulant calculation. -/
theorem det_primeArchSourceMomentHankelMatrix_two_nonneg_iff_thetaCusp :
    0 ≤ (primeArchSourceMomentHankelMatrix 2).det ↔
      ThetaCuspSixthMomentHankelInequality := by
  rw [det_primeArchSourceMomentHankelMatrix_two,
    normalizedPrimeArch_firstMinor_nonneg_iff_thetaCuspSixthMomentHankelInequality]

/-- Unconditional entrywise identification of the source Taylor matrix with the Xi central moment
matrix. -/
theorem primeArchSourceMomentHankelMatrix_eq_xiCentralMomentHankelMatrix (n : ℕ) :
    primeArchSourceMomentHankelMatrix n = xiCentralMomentHankelMatrix n := by
  ext i j
  exact analyticTraceMoments_normalizedPrimeArchSource ((i : ℕ) + (j : ℕ))

/-- One strict leading-determinant inequality in every degree, formulated entirely in Taylor
coefficients of the fixed normalized prime--Gamma source germ. -/
def PrimeArchSourceMomentHankelDeterminantsPositive : Prop :=
  ∀ n : ℕ, 0 < (primeArchSourceMomentHankelMatrix n).det

/-- The source determinant hierarchy is exactly the Xi determinant hierarchy. -/
theorem primeArchSourceMomentHankelDeterminantsPositive_iff_xi :
    PrimeArchSourceMomentHankelDeterminantsPositive ↔
      XiCentralMomentHankelDeterminantsPositive := by
  simp only [PrimeArchSourceMomentHankelDeterminantsPositive,
    XiCentralMomentHankelDeterminantsPositive,
    primeArchSourceMomentHankelMatrix_eq_xiCentralMomentHankelMatrix]

/-- **Scalar source criterion for RH.** Positivity of one leading determinant in every degree of
the fixed prime--Gamma Taylor moment matrix implies, and is implied by, RH. -/
theorem primeArchSourceMomentHankelDeterminantsPositive_iff_riemannHypothesis :
    PrimeArchSourceMomentHankelDeterminantsPositive ↔ RiemannHypothesis := by
  rw [primeArchSourceMomentHankelDeterminantsPositive_iff_xi,
    xiCentralMomentHankelDeterminantsPositive_iff_riemannHypothesis]

end

end RHTower
