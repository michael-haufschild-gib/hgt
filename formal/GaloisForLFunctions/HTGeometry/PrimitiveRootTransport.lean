import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Primitive roots of unity in an algebraically closed field and its extensions

An algebraically closed field of characteristic zero contains a primitive root of unity of every
positive order, and an injective ring map carries a primitive root to a primitive root.  So every
extension of such a field contains them too.

That is the hypothesis the cyclicity of a Kummer extension needs of the base.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **An algebraically closed field of characteristic zero has primitive roots of every order.** -/
theorem primitiveRoots_nonempty_of_isAlgClosed (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    {n : ℕ} (hn : 0 < n) : (primitiveRoots n K).Nonempty := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  exact ⟨ζ, (mem_primitiveRoots hn).2 hζ⟩

/-- **Primitive roots survive an injective ring map.** -/
theorem primitiveRoots_nonempty_of_injective {K F : Type*} [Field K] [Field F]
    (f : K →+* F) {n : ℕ} (hn : 0 < n) (h : (primitiveRoots n K).Nonempty) :
    (primitiveRoots n F).Nonempty := by
  obtain ⟨ζ, hζ⟩ := h
  exact ⟨f ζ, (mem_primitiveRoots hn).2
    (((mem_primitiveRoots hn).1 hζ).map_of_injective f.injective)⟩

/-- **An extension of an algebraically closed field of characteristic zero has primitive roots.** -/
theorem primitiveRoots_nonempty_of_algebra (K F : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] {n : ℕ} (hn : 0 < n) : (primitiveRoots n F).Nonempty :=
  primitiveRoots_nonempty_of_injective (algebraMap K F) hn
    (primitiveRoots_nonempty_of_isAlgClosed K hn)

end GaloisForLFunctions.HTGeometry
