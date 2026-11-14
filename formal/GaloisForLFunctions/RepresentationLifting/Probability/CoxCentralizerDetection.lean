import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.CoxResidualClassification
import GaloisForLFunctions.RepresentationLifting.ModularTrace

/-!
# Gamma–Cox detection of dual-number endomorphisms

The commutator residual vanishes precisely on the square-zero shift's
centralizer. Its limiting binary test therefore identifies the repeated block
structure of a dual-number-linear endomorphism.
-/

open Filter Topology
open scoped Classical
open GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox
namespace GaloisForLFunctions.RepresentationLifting
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The commutator norm detects the full centralizer structure. -/
theorem cox_dualNumber_centralizer (T : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    Tendsto (fun K => detection K ‖T * dualNumberShift - dualNumberShift * T‖) atTop
      (𝓝 (if ∃ A B : Matrix ι ι ℝ, T = Matrix.fromBlocks A B 0 A then 1 else 0)) := by
  simpa only [norm_eq_zero, sub_eq_zero, commute_dualNumberShift_iff] using
    tendsto_detection ‖T * dualNumberShift - dualNumberShift * T‖

/-- Every matrix in a finite list is classified for dual-number linearity. -/
theorem cox_dualNumber_centralizer_family {τ : Type*} [Fintype τ]
    (T : τ → Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    Tendsto (fun K => (binaryLaw K
      (fun i => ‖T i * dualNumberShift - dualNumberShift * T i‖)).real
      {b | b ≠ fun i => decide (∃ A B : Matrix ι ι ℝ, T i = Matrix.fromBlocks A B 0 A)})
      atTop (𝓝 0) := by
  exact tendsto_classification_error
    (fun i => ‖T i * dualNumberShift - dualNumberShift * T i‖)
    (fun i => ∃ A B : Matrix ι ι ℝ, T i = Matrix.fromBlocks A B 0 A) fun i => by
    simp only [norm_eq_zero, sub_eq_zero, commute_dualNumberShift_iff]

end
end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.cox_dualNumber_centralizer
#print axioms GaloisForLFunctions.RepresentationLifting.cox_dualNumber_centralizer_family
