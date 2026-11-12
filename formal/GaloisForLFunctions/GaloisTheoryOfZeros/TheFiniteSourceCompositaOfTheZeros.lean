import GaloisForLFunctions.GaloisTheoryOfZeros.ThePermutationActionOnAllZeroFibres

/-!
# Finite source composita and the full arithmetic action

The splitting fields of finite collections of complete ordinate fibres exhaust
the whole zero field. A proposed permutation of all fibres extends uniquely
exactly when each finite collection is induced by an automorphism of its own
source splitting-field compositum.
-/

noncomputable section
set_option autoImplicit false
open Complex Polynomial Set RHTower
open scoped BigOperators
namespace GaloisForLFunctions.GaloisTheoryOfZeros

private theorem sourceFibrePolynomial_map_in_zeroField (t : ℝ) :
    (sourceFibrePolynomial t).map (algebraMap fullFibreSourceField fullFibreZeroExtension) =
      ∏ q ∈ ordinateFibreCopies t,
        (X-C (centeredZeroInFibreExtension q) : fullFibreZeroExtension[X]) := by
  classical
  apply Polynomial.map_injective (algebraMap fullFibreZeroExtension ℂ)
    (algebraMap fullFibreZeroExtension ℂ).injective
  rw [Polynomial.map_map,← IsScalarTower.algebraMap_eq fullFibreSourceField fullFibreZeroExtension ℂ,
    sourceFibrePolynomial_map_eq_prod]
  change _ = (Polynomial.mapRingHom (algebraMap fullFibreZeroExtension ℂ))
    (∏ q ∈ ordinateFibreCopies t, (X-C (centeredZeroInFibreExtension q) : fullFibreZeroExtension[X]))
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro q _
  change X-C (xiSpectralPoint q) =
    (X-C (centeredZeroInFibreExtension q) : fullFibreZeroExtension[X]).map
      (algebraMap fullFibreZeroExtension ℂ)
  rw [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C]
  rfl

private theorem sourceFibrePolynomial_splits_in_zeroField (t : ℝ) :
    ((sourceFibrePolynomial t).map (algebraMap fullFibreSourceField fullFibreZeroExtension)).Splits := by
  rw [sourceFibrePolynomial_map_in_zeroField]
  apply Polynomial.Splits.prod
  intro q _
  exact Polynomial.Splits.of_natDegree_le_one (le_of_eq (natDegree_X_sub_C _))

/-- The complete source splitting field of a single ordinate fibre, inside the full zero field. -/
def singleFibreField (t : ℝ) : IntermediateField fullFibreSourceField fullFibreZeroExtension :=
  IntermediateField.adjoin fullFibreSourceField ((sourceFibrePolynomial t).rootSet fullFibreZeroExtension)

instance singleFibreField_isSplittingField (t : ℝ) :
    Polynomial.IsSplittingField fullFibreSourceField (singleFibreField t) (sourceFibrePolynomial t) := by
  change Polynomial.IsSplittingField fullFibreSourceField
    (IntermediateField.adjoin fullFibreSourceField ((sourceFibrePolynomial t).rootSet fullFibreZeroExtension))
    (sourceFibrePolynomial t)
  exact IntermediateField.adjoin_rootSet_isSplittingField (sourceFibrePolynomial_splits_in_zeroField t)

instance singleFibreField_normal (t : ℝ) : Normal fullFibreSourceField (singleFibreField t) :=
  Normal.of_isSplittingField (sourceFibrePolynomial t)

instance singleFibreField_finite (t : ℝ) : FiniteDimensional fullFibreSourceField (singleFibreField t) :=
  Polynomial.IsSplittingField.finiteDimensional (singleFibreField t) (sourceFibrePolynomial t)

/-- The intrinsic source compositum of a finite collection of complete ordinate fibres. -/
def finiteFibreField (S : Finset ℝ) : IntermediateField fullFibreSourceField fullFibreZeroExtension :=
  ⨆ t ∈ S, singleFibreField t

/-- The source equation of a finite collection of whole fibres retains all their analytic multiplicities. -/
def finiteFibrePolynomial (S : Finset ℝ) : fullFibreSourceField[X] :=
  ∏ t ∈ S, sourceFibrePolynomial t

/-- Each finite source compositum is the splitting field of its complete product equation. -/
instance finiteFibreField_isSplittingField (S : Finset ℝ) :
    Polynomial.IsSplittingField fullFibreSourceField (finiteFibreField S) (finiteFibrePolynomial S) := by
  classical
  change Polynomial.IsSplittingField fullFibreSourceField
    (⨆ t ∈ S, singleFibreField t : IntermediateField fullFibreSourceField fullFibreZeroExtension)
    (∏ t ∈ S, sourceFibrePolynomial t)
  exact IntermediateField.isSplittingField_iSup
    (Finset.prod_ne_zero_iff.mpr fun t _ => (sourceFibrePolynomial_monic t).ne_zero)
    (fun t _ => singleFibreField_isSplittingField t)

instance finiteFibreField_normal (S : Finset ℝ) : Normal fullFibreSourceField (finiteFibreField S) :=
  Normal.of_isSplittingField (finiteFibrePolynomial S)

instance finiteFibreField_finite (S : Finset ℝ) : FiniteDimensional fullFibreSourceField (finiteFibreField S) :=
  Polynomial.IsSplittingField.finiteDimensional (finiteFibreField S) (finiteFibrePolynomial S)

/-- Finite collections of complete fibres give finite Galois extensions of the actual source field. -/
instance finiteFibreField_isGalois (S : Finset ℝ) : IsGalois fullFibreSourceField (finiteFibreField S) := ⟨⟩

theorem singleFibreField_le_finite {S : Finset ℝ} {t : ℝ} (ht : t ∈ S) :
    singleFibreField t ≤ finiteFibreField S :=
  le_iSup_of_le t (le_iSup_of_le ht le_rfl)

theorem finiteFibreField_mono {S T : Finset ℝ} (hST : S ⊆ T) :
    finiteFibreField S ≤ finiteFibreField T := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  exact singleFibreField_le_finite (hST ht)

private theorem fibreRootInField_mem_source_roots (t : ℝ) (z : ↥(fibreZeroSupport t)) :
    fibreRootInField t z ∈ (sourceFibrePolynomial t).rootSet fullFibreZeroExtension := by
  classical
  obtain ⟨q,hq,hqz⟩ := Finset.mem_image.mp z.property
  have hC : (fibreRootInField t z : ℂ) ∈ (sourceFibrePolynomial t).rootSet ℂ :=
    (sourceFibrePolynomial_rootSet t _).mpr ⟨q,hq,hqz⟩
  apply Polynomial.mem_rootSet'.mpr
  refine ⟨((sourceFibrePolynomial_monic t).map _).ne_zero,?_⟩
  apply (IntermediateField.val fullFibreZeroExtension).injective
  change (IntermediateField.val fullFibreZeroExtension)
    (aeval (fibreRootInField t z) (sourceFibrePolynomial t)) =
      (IntermediateField.val fullFibreZeroExtension) 0
  rw [map_zero,← Polynomial.aeval_algHom_apply (IntermediateField.val fullFibreZeroExtension)]
  exact (Polynomial.mem_rootSet'.mp hC).2

/-- Every root of a selected complete fibre belongs to its finite source compositum. -/
theorem fibreRootInField_mem_finite {S : Finset ℝ} {t : ℝ} (ht : t ∈ S)
    (z : ↥(fibreZeroSupport t)) : fibreRootInField t z ∈ finiteFibreField S :=
  singleFibreField_le_finite ht
    (IntermediateField.subset_adjoin _ _ (fibreRootInField_mem_source_roots t z))

/-- A complete source root field is generated by its distinct finite support. -/
theorem singleFibreField_le_iff (t : ℝ)
    (H : IntermediateField fullFibreSourceField fullFibreZeroExtension) :
    singleFibreField t ≤ H ↔ ∀ z : ↥(fibreZeroSupport t), fibreRootInField t z ∈ H := by
  classical
  constructor
  · intro h z
    exact h (IntermediateField.subset_adjoin _ _ (fibreRootInField_mem_source_roots t z))
  · intro h
    apply IntermediateField.adjoin_le_iff.mpr
    intro r hr
    have hz := (Polynomial.mem_rootSet'.mp hr).2
    have hC := congrArg (fun x : fullFibreZeroExtension => (x : ℂ)) hz
    change (IntermediateField.val fullFibreZeroExtension)
      (aeval r (sourceFibrePolynomial t)) = 0 at hC
    rw [← Polynomial.aeval_algHom_apply (IntermediateField.val fullFibreZeroExtension)] at hC
    have hrC : (r : ℂ) ∈ (sourceFibrePolynomial t).rootSet ℂ :=
      Polynomial.mem_rootSet'.mpr ⟨((sourceFibrePolynomial_monic t).map _).ne_zero,hC⟩
    obtain ⟨q,hq,hqr⟩ := (sourceFibrePolynomial_rootSet t (r : ℂ)).mp hrC
    let z : ↥(fibreZeroSupport t) :=
      ⟨xiSpectralPoint q,Finset.mem_image.mpr ⟨q,hq,rfl⟩⟩
    have he : fibreRootInField t z = r := Subtype.ext hqr
    rw [← he]
    exact h z

/-- All finite source composita together exhaust the entire centered zero field. -/
theorem iSup_finiteFibreField :
    (⨆ S : Finset ℝ, finiteFibreField S) = ⊤ := by
  classical
  let H : IntermediateField fullFibreSourceField fullFibreZeroExtension :=
    ⨆ S : Finset ℝ, finiteFibreField S
  have hroot (q : XiZeroCopy) : centeredZeroInFibreExtension q ∈ H := by
    let t := (xiSpectralPoint q).re
    let z : ↥(fibreZeroSupport t) :=
      ⟨xiSpectralPoint q,Finset.mem_image.mpr ⟨q,(mem_ordinateFibreCopies t q).mpr rfl,rfl⟩⟩
    exact (le_iSup finiteFibreField {t})
      (fibreRootInField_mem_finite (S := {t}) (Finset.mem_singleton_self t) z)
  have hclosure : Subfield.closure (Set.range xiSpectralPoint) ≤
      H.toSubfield.map (algebraMap fullFibreZeroExtension ℂ) := by
    apply Subfield.closure_le.mpr
    rintro z ⟨q,rfl⟩
    exact ⟨centeredZeroInFibreExtension q,hroot q,rfl⟩
  apply top_unique
  intro z _
  have hz : (z : ℂ) ∈ Subfield.closure (Set.range xiSpectralPoint) := by
    rw [← fullFibreZeroExtension_toSubfield]
    exact z.property
  obtain ⟨a,ha,he⟩ := hclosure hz
  have haz : a = z := Subtype.ext he
  rwa [haz] at ha

/-- A selected fibre point as an element of its finite source compositum. -/
def fibreRootAtStage (S : Finset ℝ) (t : ℝ) (ht : t ∈ S)
    (z : ↥(fibreZeroSupport t)) : finiteFibreField S :=
  ⟨fibreRootInField t z,fibreRootInField_mem_finite ht z⟩

/-- The prescribed root permutations respect the arithmetic of a finite source compositum. -/
def FiniteSourceCompatibility (π : ∀ t : ℝ, fibreDivisorSymmetries t) (S : Finset ℝ) : Prop :=
  ∃ τ : finiteFibreField S ≃ₐ[fullFibreSourceField] finiteFibreField S,
    ∀ t (ht : t ∈ S) (z : ↥(fibreZeroSupport t)),
      ((τ (fibreRootAtStage S t ht z) : fullFibreZeroExtension) : ℂ) = ((π t).val z : ℂ)

private theorem stage_restriction_on_root
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension)
    (S : Finset ℝ) (t : ℝ) (ht : t ∈ S) (z : ↥(fibreZeroSupport t)) :
    (((σ.restrictNormal (finiteFibreField S)) (fibreRootAtStage S t ht z) :
      fullFibreZeroExtension) : ℂ) = (σ (fibreRootInField t z) : ℂ) :=
  congrArg (fun a : fullFibreZeroExtension => (a : ℂ))
    (AlgEquiv.restrictNormal_commutes σ (finiteFibreField S) (fibreRootAtStage S t ht z))

/-- The full arithmetic image is characterized by intrinsic finite source-field compatibility. -/
theorem allFibreDivisorAction_source_compatibility (π : ∀ t : ℝ, fibreDivisorSymmetries t) :
    π ∈ Set.range allFibreDivisorAction ↔ ∀ S : Finset ℝ, FiniteSourceCompatibility π S := by
  constructor
  · rintro ⟨σ,rfl⟩ S
    refine ⟨σ.restrictNormal (finiteFibreField S),fun t ht z => ?_⟩
    exact stage_restriction_on_root σ S t ht z
  · intro h
    apply (allFibreDivisorAction_mem_range_iff π).mpr
    intro S
    obtain ⟨τ,hτ⟩ := h S
    obtain ⟨σ,hσ⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := fullFibreSourceField) (K₁ := finiteFibreField S) fullFibreZeroExtension τ
    change σ.restrictNormal (finiteFibreField S) = τ at hσ
    refine ⟨σ,fun t ht => ?_⟩
    apply Subtype.ext
    apply Equiv.ext
    intro z
    apply Subtype.ext
    change (σ (fibreRootInField t z) : ℂ) = ((π t).val z : ℂ)
    rw [← stage_restriction_on_root σ S t ht z,hσ]
    exact hτ t ht z

/-- Finite source arithmetic determines a unique automorphism of the full infinite zero field. -/
theorem source_compatible_unique_extension (π : ∀ t : ℝ, fibreDivisorSymmetries t) :
    (∃! σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension,
      allFibreDivisorAction σ = π) ↔ ∀ S : Finset ℝ, FiniteSourceCompatibility π S := by
  rw [← allFibreDivisorAction_source_compatibility]
  constructor
  · rintro ⟨σ,hσ,_⟩
    exact ⟨σ,hσ⟩
  · rintro ⟨σ,hσ⟩
    exact ⟨σ,hσ,fun τ hτ => allFibreDivisorAction_injective (hτ.trans hσ.symm)⟩

end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.finiteFibreField_finite
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.finiteFibreField_isGalois
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.iSup_finiteFibreField
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.source_compatible_unique_extension

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.finiteFibreField_isSplittingField
