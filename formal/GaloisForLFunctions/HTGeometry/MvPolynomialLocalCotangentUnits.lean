import GaloisForLFunctions.HTGeometry.MvPolynomialLocalJacobianBasis
import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Unit rescaling for local polynomial cotangent data
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct

noncomputable section

set_option synthInstance.maxHeartbeats 200000 in
/-- The local-polynomial specialization of unit invariance for source-residue cotangent
independence.  Keeping the statement in the project's local-ring abbreviations avoids repeated
normalization through nested localizations. -/
theorem localPresentationSourceResidueCotangentMap_linearIndependent_units_smul
    {σ : Type} [Finite σ]
    (I : Ideal (MvPolynomial σ ℂ))
    (p : PrimeSpectrum ((MvPolynomial σ ℂ) ⧸ I))
    {m : ℕ} (v : Fin m → localPresentationKernel I p)
    (d : Fin m → (localPolynomialRing I p)ˣ)
    (hli : LinearIndependent
      (IsLocalRing.ResidueField (localPolynomialRing I p))
      (fun i ↦ localPresentationSourceResidueCotangentMap I p
        (1 ⊗ₜ[localPolynomialRing I p] v i))) :
    LinearIndependent
      (IsLocalRing.ResidueField (localPolynomialRing I p))
      (fun i ↦ localPresentationSourceResidueCotangentMap I p
        (1 ⊗ₜ[localPolynomialRing I p]
          ((d i : localPolynomialRing I p) • v i))) := by
  let P := localPolynomialRing I p
  let K := IsLocalRing.ResidueField P
  let dK : Fin m → Kˣ := fun i ↦
    Units.map (algebraMap P K) (d i)
  have hscaled :
      (fun i ↦ localPresentationSourceResidueCotangentMap I p
        (1 ⊗ₜ[P] ((d i : P) • v i))) =
      (fun i ↦ (dK i : K) •
        localPresentationSourceResidueCotangentMap I p
          (1 ⊗ₜ[P] v i)) := by
    funext i
    simp [dK]
    rw [IsScalarTower.algebraMap_smul]
  rw [hscaled]
  simpa only [Pi.smul_apply] using hli.units_smul dK

end

end GaloisForLFunctions.HTGeometry
