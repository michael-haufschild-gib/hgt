import GaloisForLFunctions.HTGeometry.IntersectionNormal
import GaloisForLFunctions.HTGeometry.IntermediateFieldComap

/-!
# The subgroup fixing the intersection is normal

The intersection of two normal subextensions is normal, and reading it inside the first factor
changes nothing up to isomorphism, so it stays normal there.  In characteristic zero normal means
Galois, and the subgroup of the first factor's automorphism group fixing a Galois subextension is a
normal subgroup.

That is the group-side hypothesis of the base change step, discharged from normality of the two
factors alone.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- **The intersection stays normal when read inside the first factor.** -/
instance normal_comap_inf (E M : IntermediateField F L) [Normal F L] [Normal F E] [Normal F M] :
    Normal F (IntermediateField.comap E.val (E ⊓ M)) :=
  Normal.of_algEquiv (comapValEquiv (inf_le_left : E ⊓ M ≤ E)).symm

/-- **The subgroup fixing the intersection is normal.** -/
theorem fixingSubgroup_comap_inf_normal [CharZero F] (E M : IntermediateField F L)
    [Normal F L] [FiniteDimensional F E] [IsGalois F E] [Normal F M] :
    (IntermediateField.comap E.val (E ⊓ M)).fixingSubgroup.Normal := by
  haveI : Normal F E := IsGalois.to_normal
  haveI : IsGalois F (IntermediateField.comap E.val (E ⊓ M)) := ⟨⟩
  infer_instance

end GaloisForLFunctions.HTGeometry
