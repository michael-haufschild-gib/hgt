import GaloisForLFunctions.HTGeometry.PaperFourierLawMeasure
import GaloisForLFunctions.HTGeometry.FinitePowerCovarianceDeterminant
import GaloisForLFunctions.HTGeometry.PowerCovarianceMatrix

/-! # Power-covariance determinant of any finite atomic probability law -/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory FourierLLogL
open scoped BigOperators

/-- Repeated nodes and zero weights are allowed: both sides then record the rank loss. -/
theorem atomicProbability_powerCovarianceMatrix_det {β : Type*}
    [MeasurableSpace β] [MeasurableSingletonClass β] {n : ℕ}
    (P : Law (Fin (n + 1))) (φ : Fin (n + 1) → β) (f : β → ℝ) :
    (powerCovarianceMatrix (P.atomicProbability φ : Measure β) f n).det =
      (Matrix.vandermonde (fun i => f (φ i))).det ^ 2 * ∏ i, P i := by
  have hL2 (g : β → ℝ) : MemLp g 2 (P.atomicProbability φ : Measure β) :=
    (memLp_two_iff_integrable_sq (Law.integrable_atomicProbability P φ g).aestronglyMeasurable).mpr
      (Law.integrable_atomicProbability P φ (fun x => g x ^ 2))
  have hmatrix : powerCovarianceMatrix (P.atomicProbability φ : Measure β) f n =
      fun i j : Fin n =>
        (∑ l, P l * f (φ l) ^ ((i.val + 1) + (j.val + 1))) -
        (∑ l, P l * f (φ l) ^ (i.val + 1)) *
          (∑ l, P l * f (φ l) ^ (j.val + 1)) := by
    ext i j
    rw [powerCovarianceMatrix, covariance_eq_sub (hL2 _) (hL2 _)]
    simp only [Law.integral_atomicProbability, Law.Ex, Pi.mul_apply, ← pow_add]
  rw [hmatrix]
  exact det_finite_power_covariance _ _ P.total

end GaloisForLFunctions.HTGeometry
