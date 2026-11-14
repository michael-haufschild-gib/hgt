import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.CoxResidualClassification
import GaloisForLFunctions.HTGeometry.SymmetricCharacters.MixtureRigidity

/-!
# Gamma–Cox detection of mixture rigidity

The covariance defect tests equality of observables on the positive-weight
support. Zero-weight components remain unrestricted, including the empty mixture.
-/

open Filter Topology
open scoped Classical
open GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox
namespace GaloisForLFunctions.SymmetricCharacters
noncomputable section
variable {I : Type*} [Fintype I]

/-- Covariance-defect detection recovers equality on the mixture's positive support. -/
theorem cox_mixture_rigidity (w : I → NNReal) (v : I → ℝ) :
    Tendsto (fun K => detection K (mixtureDefect w v)) atTop
      (𝓝 (if ∀ i j, w i = 0 ∨ w j = 0 ∨ v i = v j then 1 else 0)) := by
  simpa only [mixtureDefect_eq_zero_iff] using tendsto_detection (mixtureDefect w v)

/-- A finite list of observables is classified simultaneously for support rigidity. -/
theorem cox_mixture_rigidity_family {τ : Type*} [Fintype τ]
    (w : I → NNReal) (v : τ → I → ℝ) :
    Tendsto (fun K => (binaryLaw K (fun j => mixtureDefect w (v j))).real
      {b | b ≠ fun j => decide (∀ i l, w i = 0 ∨ w l = 0 ∨ v j i = v j l)})
      atTop (𝓝 0) := by
  exact tendsto_classification_error (fun j => mixtureDefect w (v j))
    (fun j => ∀ i l, w i = 0 ∨ w l = 0 ∨ v j i = v j l) fun j => by
    simp only [mixtureDefect_eq_zero_iff]

end
end GaloisForLFunctions.SymmetricCharacters

#print axioms GaloisForLFunctions.SymmetricCharacters.cox_mixture_rigidity
#print axioms GaloisForLFunctions.SymmetricCharacters.cox_mixture_rigidity_family
