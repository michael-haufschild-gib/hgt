import GaloisForLFunctions.HTGeometry.SourceResidueCotangent

/-!
# Evaluation of the source-residue cotangent map
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct

noncomputable section

/-- On a pure tensor with scalar `1`, the source-residue cotangent map is the Kähler
differential of the underlying presentation-kernel element. -/
@[simp]
theorem sourceResidueCotangentMap_one_tmul
    (R P S : Type*) [CommRing R] [CommRing P] [CommRing S]
    [Algebra R P] [Algebra P S] [IsLocalRing P]
    (hker : RingHom.ker (algebraMap P S) ≤
      IsLocalRing.maximalIdeal P)
    (x : RingHom.ker (algebraMap P S)) :
    sourceResidueCotangentMap R P S hker
        (1 ⊗ₜ[P] x) =
      1 ⊗ₜ[P] KaehlerDifferential.D R P x.1 := by
  simp [sourceResidueCotangentMap]
  rfl

end

end GaloisForLFunctions.HTGeometry
