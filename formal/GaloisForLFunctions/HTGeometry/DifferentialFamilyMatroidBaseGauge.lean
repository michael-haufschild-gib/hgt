import GaloisForLFunctions.HTGeometry.AffineBaseJetGauge
import GaloisForLFunctions.HTGeometry.DifferentialFamilyMatroid

/-!
# Differential-family matroids modulo affine base gauge

Coordinatewise affine gauges with nonzero linear coefficient in the differential base preserve
not only independence of the whole family, but the independence of every indexed subfamily.
Consequently they preserve the entire represented differential matroid, without a finiteness
hypothesis on the family.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

universe u v

/-- **Affine base-gauge matroid law.** Affine base-jet equivalent families represent exactly the
same differential matroid, for an arbitrary index type. -/
theorem differentialFamilyMatroid_eq_of_affineBaseJetEquivalentFamilies
    {F K : Type u} {ι : Type v} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K] [CharZero K]
    (x y : ι → K) (hxy : AffineBaseJetEquivalentFamilies F x y) :
    differentialFamilyMatroid (F := F) y =
      differentialFamilyMatroid (F := F) x := by
  obtain ⟨a, b, ha, hy⟩ := (affineBaseJetEquivalentFamilies_iff x y).1 hxy
  apply Matroid.ext_indep
  · simp [differentialFamilyMatroid]
  · intro I _
    rw [differentialFamilyMatroid_indep_iff,
      differentialFamilyMatroid_indep_iff]
    apply differentialIndependent_iff_of_affineBaseJetEquivalentFamilies
    apply (affineBaseJetEquivalentFamilies_iff
      (fun i : I ↦ x i) (fun i : I ↦ y i)).2
    exact ⟨fun i ↦ a i, fun i ↦ b i, fun i ↦ ha i, fun i ↦ hy i⟩

/-- Signed base-jet replacement preserves the entire represented differential matroid. -/
theorem differentialFamilyMatroid_eq_of_signedBaseJetEquivalentFamilies
    {F K : Type u} {ι : Type v} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K] [CharZero K]
    (x y : ι → K) (hxy : SignedBaseJetEquivalentFamilies F x y) :
    differentialFamilyMatroid (F := F) y =
      differentialFamilyMatroid (F := F) x :=
  differentialFamilyMatroid_eq_of_affineBaseJetEquivalentFamilies x y
    hxy.affineBaseJetEquivalentFamilies

/-- A literal coordinatewise affine differential-base gauge preserves the full represented
matroid. -/
theorem differentialFamilyMatroid_affineBase_eq
    {F K : Type u} {ι : Type v} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K] [CharZero K]
    (x : ι → K) (a b : ι → F) (ha : ∀ i, a i ≠ 0) :
    differentialFamilyMatroid (F := F)
        (fun i ↦ algebraMap F K (a i) * x i + algebraMap F K (b i)) =
      differentialFamilyMatroid (F := F) x :=
  differentialFamilyMatroid_eq_of_affineBaseJetEquivalentFamilies x _
    (affineBaseJetEquivalentFamilies_affineBase x a b ha)

/-- Coordinatewise translation by differential-base values preserves the full represented
matroid. -/
theorem differentialFamilyMatroid_addBase_eq
    {F K : Type u} {ι : Type v} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K] [CharZero K]
    (x : ι → K) (b : ι → F) :
    differentialFamilyMatroid (F := F)
        (fun i ↦ x i + algebraMap F K (b i)) =
      differentialFamilyMatroid (F := F) x := by
  simpa using differentialFamilyMatroid_affineBase_eq
    x (fun _ ↦ 1) b (fun _ ↦ one_ne_zero)

end

end GaloisForLFunctions
