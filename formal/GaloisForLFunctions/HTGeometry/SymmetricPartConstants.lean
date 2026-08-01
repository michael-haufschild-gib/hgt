import GaloisForLFunctions.HTGeometry.SymmetricCoefficientField
import GaloisForLFunctions.HTGeometry.PrimitiveRootTransport

/-!
# The constants inside the symmetric part

A constant is a symmetric rational function, so the constants embed in the symmetric part.  The
embedding is injective, being a homomorphism of fields.

Hence a primitive root of unity in the constants gives one in the symmetric part, which is the
hypothesis the cyclicity of a Kummer extension needs of the base.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] {d : ℕ}

/-- The constants, mapped into the symmetric part. -/
noncomputable def constToSymmetricPart (K : Type*) [Field K] (d : ℕ) :
    K →+* symmetricPart K d where
  toFun c := ⟨algebraMap K (SymmetricRationalField K d) c,
    (symmetricPartField K d).algebraMap_mem' c⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

/-- **The symmetric part contains primitive roots of unity of every order.** -/
theorem primitiveRoots_nonempty_symmetricPart (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    (d : ℕ) {n : ℕ} (hn : 0 < n) : (primitiveRoots n (symmetricPart K d)).Nonempty :=
  primitiveRoots_nonempty_of_injective (constToSymmetricPart K d) hn
    (primitiveRoots_nonempty_of_isAlgClosed K hn)

end GaloisForLFunctions.HTGeometry
