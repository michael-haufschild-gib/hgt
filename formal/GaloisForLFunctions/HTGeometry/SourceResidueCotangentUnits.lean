import GaloisForLFunctions.HTGeometry.SourceResidueCotangent
import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Unit rescaling in source-residue cotangent spaces
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct

noncomputable section

/-- Pointwise rescaling of presentation-kernel generators by local units preserves linear
independence of their source-residue cotangent images. -/
theorem sourceResidueCotangentMap_linearIndependent_units_smul
    (R P S : Type*) [CommRing R] [CommRing P] [CommRing S]
    [Algebra R P] [Algebra P S] [IsLocalRing P]
    (hker : RingHom.ker (algebraMap P S) ≤
      IsLocalRing.maximalIdeal P)
    {m : ℕ} (v : Fin m → RingHom.ker (algebraMap P S))
    (d : Fin m → Pˣ)
    (hli : LinearIndependent (IsLocalRing.ResidueField P)
      (fun i ↦ sourceResidueCotangentMap R P S hker
        (1 ⊗ₜ[P] v i))) :
    LinearIndependent (IsLocalRing.ResidueField P)
      (fun i ↦ sourceResidueCotangentMap R P S hker
        (1 ⊗ₜ[P] ((d i : P) • v i))) := by
  let K := IsLocalRing.ResidueField P
  let dK : Fin m → Kˣ := fun i ↦
    Units.map (algebraMap P K) (d i)
  have hscaled :
      (fun i ↦ sourceResidueCotangentMap R P S hker
        (1 ⊗ₜ[P] ((d i : P) • v i))) =
      (fun i ↦ (dK i : K) • sourceResidueCotangentMap R P S hker
        (1 ⊗ₜ[P] v i)) := by
    funext i
    simp [dK]
  rw [hscaled]
  simpa only [Pi.smul_apply] using hli.units_smul dK

end

end GaloisForLFunctions.HTGeometry
