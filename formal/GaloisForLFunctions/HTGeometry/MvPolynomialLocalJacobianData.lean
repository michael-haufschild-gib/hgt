import GaloisForLFunctions.HTGeometry.MvPolynomialLocalizedRelationLifts
import GaloisForLFunctions.HTGeometry.MvPolynomialLocalCotangentUnits

/-!
# Local polynomial relation data at a formally smooth point

This module combines cached localized relation lifts with source-residue cotangent independence.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct

noncomputable section

set_option maxHeartbeats 2000000 in
theorem exists_originalRelations_of_sourceResidue_basis
    {σ : Type} [Finite σ]
    (I : Ideal (MvPolynomial σ ℂ))
    (p : PrimeSpectrum ((MvPolynomial σ ℂ) ⧸ I)) :
    ∀ {m : ℕ} (v : Fin m → localPresentationKernel I p),
      Submodule.span (localPolynomialRing I p) (Set.range v) = ⊤ →
      LinearIndependent (IsLocalRing.ResidueField (localPolynomialRing I p))
        (fun i ↦ localPresentationSourceResidueCotangentMap I p
          (1 ⊗ₜ[localPolynomialRing I p] v i)) →
      ∃ (relation : Fin m → MvPolynomial σ ℂ)
        (u : Fin m → localPresentationKernel I p),
        (∀ i, relation i ∈ I) ∧
        (∀ i, (u i).1 = algebraMap (MvPolynomial σ ℂ)
          (localPolynomialRing I p) (relation i)) ∧
        Ideal.span (Set.range (fun i ↦
          algebraMap (MvPolynomial σ ℂ) (localPolynomialRing I p)
            (relation i))) = localPresentationKernel I p ∧
        LinearIndependent (IsLocalRing.ResidueField (localPolynomialRing I p))
          (fun i ↦ localPresentationSourceResidueCotangentMap I p
            (1 ⊗ₜ[localPolynomialRing I p] u i)) := by
  intro m v hvspan hvli
  obtain ⟨relation, u, denominatorUnit, hrelation_mem, huval, hideal, hu⟩ :=
    exists_originalRelations_of_localized_generators I p v hvspan
  have huli : LinearIndependent
      (IsLocalRing.ResidueField (localPolynomialRing I p))
      (fun i ↦ localPresentationSourceResidueCotangentMap I p
        (1 ⊗ₜ[localPolynomialRing I p] u i)) := by
    rw [hu]
    exact localPresentationSourceResidueCotangentMap_linearIndependent_units_smul
      I p v denominatorUnit hvli
  refine ⟨relation, u, hrelation_mem, huval, hideal, ?_⟩
  exact huli

end

end GaloisForLFunctions.HTGeometry
