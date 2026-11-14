import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.CoxResidualClassification
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaRootGeometry

/-!
# Gamma–Cox detection of elastica cubic collisions

The Weierstrass discriminant detects repeated cubic roots and the two degenerate
Jacobi moduli. Finite parameter collections are classified simultaneously.
-/

open Filter Topology
open scoped Classical
open GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox
namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
noncomputable section

/-- Cubic discriminant detection identifies exactly the repeated-root locus. -/
theorem cox_root_collision (P : Parameters) :
    Tendsto (fun K => detection K (discriminant P)) atTop
      (𝓝 (if e₁ P = e₂ P ∨ e₂ P = e₃ P ∨ e₁ P = e₃ P then 1 else 0)) := by
  simpa only [← repeated_root_iff_singular] using tendsto_detection (discriminant P)

/-- The same detector identifies the degenerate moduli zero and one. -/
theorem cox_degenerate_modulus (P : Parameters) :
    Tendsto (fun K => detection K (discriminant P)) atTop
      (𝓝 (if P.modulus = 0 ∨ P.modulus = 1 then 1 else 0)) := by
  simpa only [discriminant_eq_zero_iff] using tendsto_detection (discriminant P)

/-- All cubic collisions in a finite parameter family are detected consistently. -/
theorem cox_root_collision_family {ι : Type*} [Fintype ι] (P : ι → Parameters) :
    Tendsto (fun K => (binaryLaw K (fun i => discriminant (P i))).real
      {b | b ≠ fun i => decide (e₁ (P i) = e₂ (P i) ∨ e₂ (P i) = e₃ (P i) ∨
        e₁ (P i) = e₃ (P i))}) atTop (𝓝 0) := by
  exact tendsto_classification_error (fun i => discriminant (P i))
    (fun i => e₁ (P i) = e₂ (P i) ∨ e₂ (P i) = e₃ (P i) ∨ e₁ (P i) = e₃ (P i)) fun i => by
    simp only [← repeated_root_iff_singular]

end
end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

#print axioms GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica.cox_root_collision
#print axioms GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica.cox_degenerate_modulus
#print axioms GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica.cox_root_collision_family
