import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.CoxResidualClassification
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeFisherEntropy

/-!
# Gamma–Cox detection of detailed balance

The entropy field and Fisher current cost have the same edgewise equilibrium
criterion. Their detectors recover it on arbitrary finite state lists, without
requiring connected transport graphs or nonzero edge coefficients.
-/

open Filter Topology
open scoped Classical
open GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Vanishing entropy velocity detects equality along every active edge. -/
theorem cox_entropy_equilibrium (a : ι → ι → ℝ) (x : ι → ℝ) :
    Tendsto (fun K => detection K ‖entropyField a x‖) atTop
      (𝓝 (if ∀ i j, (a i j = 0 ∧ a j i = 0) ∨ x i = x j then 1 else 0)) := by
  simpa only [norm_eq_zero, entropyField_eq_zero_iff] using
    tendsto_detection ‖entropyField a x‖

/-- Fisher-cost detection recognizes the actual relative-entropy stationary field. -/
theorem cox_fisher_equilibrium (a : ι → ι → ℝ) (r x : ι → ℝ) :
    Tendsto (fun K => detection K (entropyFisherCost a x)) atTop
      (𝓝 (if relativeEntropyField a r x = 0 then 1 else 0)) := by
  simpa only [entropyFisherCost_eq_zero_iff a r x] using
    tendsto_detection (entropyFisherCost a x)

/-- Entropy and Fisher detectors have the same limit despite different residual scales. -/
theorem cox_fisher_entropy_gap (a : ι → ι → ℝ) (x : ι → ℝ) :
    Tendsto (fun K => detection K (entropyFisherCost a x) -
      detection K ‖entropyField a x‖) atTop (𝓝 0) := by
  have h := (cox_fisher_equilibrium a (fun _ => 0) x).sub (cox_entropy_equilibrium a x)
  simpa only [relativeEntropyField_eq_zero_iff, sub_self] using h

/-- Every state in a finite list is classified simultaneously for detailed balance. -/
theorem cox_equilibrium_family {τ : Type*} [Fintype τ]
    (a : ι → ι → ℝ) (x : τ → ι → ℝ) :
    Tendsto (fun K => (binaryLaw K (fun j => ‖entropyField a (x j)‖)).real
      {b | b ≠ fun j => decide (∀ i l, (a i l = 0 ∧ a l i = 0) ∨ x j i = x j l)})
      atTop (𝓝 0) := by
  exact tendsto_classification_error (fun j => ‖entropyField a (x j)‖)
    (fun j => ∀ i l, (a i l = 0 ∧ a l i = 0) ∨ x j i = x j l) fun j => by
    simp only [norm_eq_zero, entropyField_eq_zero_iff]

end
end GaloisForLFunctions.HTGeometry.SchafferExl

#print axioms GaloisForLFunctions.HTGeometry.SchafferExl.cox_entropy_equilibrium
#print axioms GaloisForLFunctions.HTGeometry.SchafferExl.cox_fisher_equilibrium
#print axioms GaloisForLFunctions.HTGeometry.SchafferExl.cox_fisher_entropy_gap
#print axioms GaloisForLFunctions.HTGeometry.SchafferExl.cox_equilibrium_family
