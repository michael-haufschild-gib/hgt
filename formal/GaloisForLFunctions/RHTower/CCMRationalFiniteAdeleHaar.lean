import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic
import GaloisForLFunctions.RHTower.CCMRationalFiniteBruhatReal

/-!
# Normalized Haar integration on the rational finite adeles

This file supplies the analytic infrastructure absent from mathlib's finite-adele wrapper.
The height-one completions of `ℚ` are transported to `ℚ_[p]`, their valuation rings are
transported to `ℤ_[p]`, and the restricted product is therefore locally compact.

The additive Haar measure is normalized by assigning mass one to the compact open subring
`∏ₚ ℤₚ`.  The resulting integral is then bundled as a complex-linear functional on the actual
compactly supported locally constant Bruhat space.  No abstract replacement functional is used.
-/

noncomputable section

open MeasureTheory
open IsDedekindDomain Rat.HeightOneSpectrum

namespace GaloisForLFunctions
namespace RHTower

/-- Rational completion at a height-one prime. -/
abbrev CCMRationalLocalField (v : HeightOneSpectrum ℤ) :=
  v.adicCompletion ℚ

/-- Valuation ring in the rational completion at a height-one prime. -/
noncomputable abbrev CCMRationalLocalIntegers (v : HeightOneSpectrum ℤ) :=
  v.adicCompletionIntegers ℚ

/-- Every rational nonarchimedean completion is locally compact. -/
noncomputable instance ccmRationalLocalFieldLocallyCompact
    (v : HeightOneSpectrum ℤ) :
    LocallyCompactSpace (CCMRationalLocalField v) := by
  exact (adicCompletion.padicEquiv v).toHomeomorph.isOpenEmbedding.locallyCompactSpace

/-- Every rational nonarchimedean completion is Hausdorff. -/
noncomputable instance ccmRationalLocalFieldT2
    (v : HeightOneSpectrum ℤ) :
    T2Space (CCMRationalLocalField v) := by
  exact (adicCompletion.padicEquiv v).toHomeomorph.isEmbedding.t2Space

/-- Every rational local valuation ring is compact. -/
noncomputable instance ccmRationalLocalIntegersCompact
    (v : HeightOneSpectrum ℤ) :
    CompactSpace (CCMRationalLocalIntegers v) := by
  letI : Algebra ℤ (CCMRationalLocalIntegers v) := Ring.toIntAlgebra _
  exact Homeomorph.compactSpace
    (adicCompletionIntegers.padicIntEquiv v).toHomeomorph.symm

instance ccmRationalLocalIntegersOpen :
    Fact (∀ v : HeightOneSpectrum ℤ,
      IsOpen (CCMRationalLocalIntegers v : Set (CCMRationalLocalField v))) :=
  ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩

/-- The rational finite adele ring is locally compact. -/
noncomputable instance ccmRationalFiniteAdeleLocallyCompact :
    LocallyCompactSpace CCMRationalFiniteAdele := by
  unfold CCMRationalFiniteAdele
  unfold IsDedekindDomain.FiniteAdeleRing
  exact RestrictedProduct.locallyCompactSpace_of_addGroup
    (fun v : HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ)
    (Filter.Eventually.of_forall fun v ↦
      isCompact_iff_compactSpace.mpr
        (inferInstance : CompactSpace (v.adicCompletionIntegers ℚ)))

/-- The rational finite adele ring is Hausdorff. -/
noncomputable instance ccmRationalFiniteAdeleT2 :
    T2Space CCMRationalFiniteAdele := by
  unfold CCMRationalFiniteAdele
  unfold IsDedekindDomain.FiniteAdeleRing
  exact @RestrictedProduct.instT2Space
    (HeightOneSpectrum ℤ)
    (fun v ↦ v.adicCompletion ℚ)
    (fun v ↦ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
    Filter.cofinite
    (fun _ ↦ inferInstance)
    (fun v ↦ ccmRationalLocalFieldT2 v)

/-- Canonical Borel measurable structure for rational finite adeles. -/
noncomputable instance ccmRationalFiniteAdeleMeasurableSpace :
    MeasurableSpace CCMRationalFiniteAdele :=
  borel _

instance ccmRationalFiniteAdeleBorelSpace :
    BorelSpace CCMRationalFiniteAdele :=
  ⟨rfl⟩

/-- Compact open subring of integral finite adeles `∏ₚ ℤₚ`. -/
noncomputable def ccmRationalIntegralFiniteAdeles : Set CCMRationalFiniteAdele :=
  {x | ∀ v : HeightOneSpectrum ℤ,
    x v ∈ (CCMRationalLocalIntegers v : Set (CCMRationalLocalField v))}

theorem ccmRationalIntegralFiniteAdeles_isOpen :
    IsOpen ccmRationalIntegralFiniteAdeles := by
  exact RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum ℤ ↦ CCMRationalLocalField v)
    (A := fun v : HeightOneSpectrum ℤ ↦
      (CCMRationalLocalIntegers v : Set (CCMRationalLocalField v)))
    (fun _ ↦ Valued.isOpen_valuationSubring _)

theorem ccmRationalIntegralFiniteAdeles_isCompact :
    IsCompact ccmRationalIntegralFiniteAdeles := by
  letI : CompactSpace ((v : HeightOneSpectrum ℤ) → CCMRationalLocalIntegers v) :=
    Pi.compactSpace
  rw [show ccmRationalIntegralFiniteAdeles = Set.range
      (RestrictedProduct.structureMap
        (fun v : HeightOneSpectrum ℤ ↦ CCMRationalLocalField v)
        (fun v : HeightOneSpectrum ℤ ↦
          (CCMRationalLocalIntegers v : Set (CCMRationalLocalField v)))
        Filter.cofinite) by
    ext x
    rw [ccmRationalIntegralFiniteAdeles, RestrictedProduct.range_structureMap]
    rfl]
  exact isCompact_range (RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : HeightOneSpectrum ℤ ↦ CCMRationalLocalField v)
    (A := fun v : HeightOneSpectrum ℤ ↦
      (CCMRationalLocalIntegers v : Set (CCMRationalLocalField v)))
    (fun _ ↦ Valued.isOpen_valuationSubring _)).continuous

theorem ccmRationalIntegralFiniteAdeles_nonempty :
    ccmRationalIntegralFiniteAdeles.Nonempty := by
  refine ⟨0, ?_⟩
  rw [ccmRationalIntegralFiniteAdeles]
  exact fun _ ↦ zero_mem _

/-- The integral finite adeles as a compact set with nonempty interior. -/
noncomputable def ccmRationalIntegralFiniteAdelesPositive :
    TopologicalSpace.PositiveCompacts CCMRationalFiniteAdele where
  carrier := ccmRationalIntegralFiniteAdeles
  isCompact' := ccmRationalIntegralFiniteAdeles_isCompact
  interior_nonempty' := by
    rw [ccmRationalIntegralFiniteAdeles_isOpen.interior_eq]
    exact ccmRationalIntegralFiniteAdeles_nonempty

/-- Additive Haar measure normalized by `vol(∏ₚ ℤₚ) = 1`. -/
noncomputable def ccmRationalFiniteAdeleHaar : Measure CCMRationalFiniteAdele :=
  Measure.addHaarMeasure ccmRationalIntegralFiniteAdelesPositive

instance ccmRationalFiniteAdeleHaarIsAddHaar :
    ccmRationalFiniteAdeleHaar.IsAddHaarMeasure := by
  unfold ccmRationalFiniteAdeleHaar
  infer_instance

instance ccmRationalFiniteAdeleHaarRegular :
    ccmRationalFiniteAdeleHaar.Regular := by
  unfold ccmRationalFiniteAdeleHaar
  infer_instance

@[simp]
theorem ccmRationalFiniteAdeleHaar_integral_subring :
    ccmRationalFiniteAdeleHaar ccmRationalIntegralFiniteAdeles = 1 := by
  exact Measure.addHaarMeasure_self

/-- Every compactly supported locally constant finite-adele function is Haar integrable. -/
theorem ccmRationalFiniteBruhat_integrable
    (f : CCMRationalFiniteBruhatSchwartz) :
    Integrable (f.1 : CCMRationalFiniteAdele → ℂ) ccmRationalFiniteAdeleHaar :=
  f.1.continuous.integrable_of_hasCompactSupport f.2

/-- Normalized finite-adelic Haar integral on the actual Bruhat space. -/
noncomputable def ccmRationalFiniteBruhatIntegral :
    CCMRationalFiniteBruhatSchwartz →ₗ[ℂ] ℂ where
  toFun f := ∫ x, f.1 x ∂ccmRationalFiniteAdeleHaar
  map_add' f g := by
    simpa using integral_add
      (ccmRationalFiniteBruhat_integrable f)
      (ccmRationalFiniteBruhat_integrable g)
  map_smul' z f := by
    simpa using integral_smul z (f.1 : CCMRationalFiniteAdele → ℂ)

@[simp]
theorem ccmRationalFiniteBruhatIntegral_apply
    (f : CCMRationalFiniteBruhatSchwartz) :
    ccmRationalFiniteBruhatIntegral f =
      ∫ x, f.1 x ∂ccmRationalFiniteAdeleHaar :=
  rfl

end RHTower
end GaloisForLFunctions
