import GaloisForLFunctions.HTGeometry.PaperDiscriminantRootUnits
import GaloisForLFunctions.HTGeometry.LocallyNilpotentDerivationSlice

/-!
# An exact polynomial chart for the ordered discriminant complement

The paid common-translation clock has every root coordinate as a slice.
Applying the existing native slice theorem expresses the full localized
ring as a polynomial algebra over its translation constants, preserving
the original coefficient field. Every root difference lies in the base.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable (K : Type*) [Field K] [CharZero K] (n : ℕ)

private def fieldKernel {B : Type*} [CommRing B] [Algebra K B]
    [Algebra ℚ B] [IsScalarTower ℚ K B] (D : Derivation K B B) : Subalgebra K B :=
  { (derivationKernel (D.restrictScalars ℚ)).toSubsemiring with
    algebraMap_mem' := D.map_algebraMap }

private def fieldSliceEquiv {B : Type*} [CommRing B] [Algebra K B]
    [Algebra ℚ B] [IsScalarTower ℚ K B] (D : Derivation K B B)
    {s : B} (hs : D s = 1) (hD : StableCoordinate.IsLocallyNilpotent D) :
    Polynomial (fieldKernel K D) ≃ₐ[K] B :=
  AlgEquiv.ofBijective
    ((Polynomial.aeval s : Polynomial (fieldKernel K D) →ₐ[fieldKernel K D] B).restrictScalars K)
    (bijective_aeval_of_locallyNilpotent (D.restrictScalars ℚ) hs hD)

/-- The full invariant coefficient algebra of simultaneous root translation. -/
def paperDiscriminantTranslationConstants :
    Subalgebra K (PaperRootDiscriminantOpen K n) :=
  fieldKernel K (paperDiscriminantTranslation K n)

/-- Membership in the chart's coefficient algebra is exactly translation invariance. -/
@[simp] theorem paperDiscriminantTranslationConstants_mem
    (a : PaperRootDiscriminantOpen K n) :
    a ∈ paperDiscriminantTranslationConstants K n ↔
      paperDiscriminantTranslation K n a = 0 := Iff.rfl

/-- All root differences belong to the invariant coefficient algebra. -/
theorem paperDiscriminantRootDifference_mem_constants (i j : Fin n) :
    paperDiscriminantRoot i - paperDiscriminantRoot j ∈
      paperDiscriminantTranslationConstants K n := by
  change paperDiscriminantTranslation K n
    (paperDiscriminantRoot i - paperDiscriminantRoot j) = 0
  rw [map_sub, paperDiscriminantTranslation_root, paperDiscriminantTranslation_root, sub_self]

/-- The entire discriminant-open ring is a polynomial algebra over its invariant coefficients. -/
def paperDiscriminantTranslationSlice :
    Polynomial (paperDiscriminantTranslationConstants K (n + 1)) ≃ₐ[K]
      PaperRootDiscriminantOpen K (n + 1) :=
  fieldSliceEquiv K (paperDiscriminantTranslation K (n + 1))
    (paperDiscriminantTranslation_root (0 : Fin (n + 1)))
    (paperDiscriminantTranslation_locallyNilpotent (n + 1))

/-- The new polynomial variable is the first native root coordinate. -/
@[simp] theorem paperDiscriminantTranslationSlice_X :
    paperDiscriminantTranslationSlice K n Polynomial.X =
      paperDiscriminantRoot (0 : Fin (n + 1)) :=
  Polynomial.aeval_X _

/-- The polynomial chart leaves every invariant coefficient unchanged. -/
@[simp] theorem paperDiscriminantTranslationSlice_C
    (a : paperDiscriminantTranslationConstants K (n + 1)) :
    paperDiscriminantTranslationSlice K n (Polynomial.C a) = a :=
  Polynomial.aeval_C (paperDiscriminantRoot (0 : Fin (n + 1))) a

/-- Every localized expression has a unique polynomial expansion in the first root. -/
theorem paperDiscriminantTranslation_unique_polynomial
    (a : PaperRootDiscriminantOpen K (n + 1)) :
    ∃! p : Polynomial (paperDiscriminantTranslationConstants K (n + 1)),
      Polynomial.aeval (paperDiscriminantRoot (0 : Fin (n + 1))) p = a := by
  obtain ⟨p, hp⟩ := (paperDiscriminantTranslationSlice K n).surjective a
  exact ⟨p, hp, fun q hq =>
    (paperDiscriminantTranslationSlice K n).injective (hq.trans hp.symm)⟩

end

end GaloisForLFunctions.HTGeometry
