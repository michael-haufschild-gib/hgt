import GaloisForLFunctions.RHTower.FiniteQuantumObserverOperationalRecurrence
import GaloisForLFunctions.HilbertMetric.Correlation.ExceptionalEnergy

/-!
# Centered energy error of a finite observer matrix

The observer's Hilbert--Schmidt energy is the Euclidean energy of its entries.
The exceptional-source inequality therefore controls arbitrary coherent matrix
errors, with the exact quadratic correction retained.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric
open _root_.RHTower
noncomputable section

private def observerMatrixVector {d : ℕ} (A : Fin d → Fin d → ℂ) :
    EuclideanSpace ℂ (Fin d × Fin d) := WithLp.toLp 2 fun p => A p.1 p.2

private theorem observerMatrixVector_norm_sq {d : ℕ} (A : Fin d → Fin d → ℂ) :
    ‖observerMatrixVector A‖ ^ 2 = finiteMatrixHSEnergy A := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ p : Fin d × Fin d, ‖A p.1 p.2‖ ^ 2) = ∑ i, ∑ j, ‖A i j‖ ^ 2
  simpa only [Finset.univ_product_univ] using
    Finset.sum_product' (Finset.univ : Finset (Fin d)) Finset.univ (fun i j => ‖A i j‖ ^ 2)

private theorem observerMatrixVector_sub {d : ℕ} (A B : Fin d → Fin d → ℂ) :
    observerMatrixVector (A - B) = observerMatrixVector A - observerMatrixVector B := rfl

/-- Sharp centered Hilbert--Schmidt error for an arbitrary removed observer matrix. -/
theorem observerMatrix_deletion_centered {d : ℕ} (A B : Fin d → Fin d → ℂ) :
    (finiteMatrixHSEnergy (A - B) - finiteMatrixHSEnergy A - finiteMatrixHSEnergy B) ^ 2 ≤
      4 * finiteMatrixHSEnergy A * finiteMatrixHSEnergy B := by
  letI : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin d × Fin d)) :=
    InnerProductSpace.rclikeToReal ℂ _
  have h := energy_sub_centered (observerMatrixVector A) (observerMatrixVector B)
  simpa only [← observerMatrixVector_sub, observerMatrixVector_norm_sq] using h

/-- Absolute observer-energy error paid by the removed matrix and its interaction radius. -/
theorem observerMatrix_deletion_error {d : ℕ} (A B : Fin d → Fin d → ℂ) :
    |finiteMatrixHSEnergy (A - B) - finiteMatrixHSEnergy A| ≤
      finiteMatrixHSEnergy B +
        2 * Real.sqrt (finiteMatrixHSEnergy A) * Real.sqrt (finiteMatrixHSEnergy B) := by
  letI : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin d × Fin d)) :=
    InnerProductSpace.rclikeToReal ℂ _
  have h := energy_sub_error (observerMatrixVector A) (observerMatrixVector B)
  have hn (M : Fin d → Fin d → ℂ) : Real.sqrt (finiteMatrixHSEnergy M) =
      ‖observerMatrixVector M‖ := by
    rw [← observerMatrixVector_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  simpa only [← observerMatrixVector_sub, observerMatrixVector_norm_sq, hn] using h

end
end GaloisForLFunctions.HilbertMetric

#print axioms GaloisForLFunctions.HilbertMetric.observerMatrix_deletion_centered
#print axioms GaloisForLFunctions.HilbertMetric.observerMatrix_deletion_error
