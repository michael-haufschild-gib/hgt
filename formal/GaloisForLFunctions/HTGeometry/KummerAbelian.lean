import Mathlib.FieldTheory.KummerExtension

/-!
# A Kummer extension has abelian Galois group

Adjoining an `n`-th root to a field containing a primitive `n`-th root of unity gives an extension
whose automorphism group is the group of `n`-th roots of unity, which is commutative.

This supplies the abelian-quotient hypothesis of the base change step: every subextension of a
Kummer extension has abelian Galois group over the base.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] {n : ℕ} [NeZero n]

/-- **The Galois group of a Kummer extension is abelian.** -/
theorem commute_gal_XPowSubC (hζ : (primitiveRoots n K).Nonempty) {a : K}
    (hirr : Irreducible (Polynomial.X ^ n - Polynomial.C a)) :
    ∀ x y : (AdjoinRoot (Polynomial.X ^ n - Polynomial.C a) ≃ₐ[K]
      AdjoinRoot (Polynomial.X ^ n - Polynomial.C a)), x * y = y * x := by
  intro x y
  obtain ⟨x', rfl⟩ := (autAdjoinRootXPowSubCEquiv hζ hirr).surjective x
  obtain ⟨y', rfl⟩ := (autAdjoinRootXPowSubCEquiv hζ hirr).surjective y
  rw [← map_mul, ← map_mul, mul_comm]

end GaloisForLFunctions.HTGeometry
