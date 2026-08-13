import GaloisForLFunctions.RHTower.FieldOneFiniteStageModuleOneFundamentalDomain
import GaloisForLFunctions.RHTower.FieldOneFiniteStageIdeleClassSplitting

/-!
# Exact finite-stage idele fundamental domain

The Connes--Marcolli unfolding argument uses a fundamental domain for the diagonal action of the
rational `S`-units on the finite-stage ideles.  This file constructs that decomposition on the
literal arithmetic objects:

`Q_S^* × (K_S × R_+^*) ≃ A_S^*`.

Here `K_S` is the actual module-one idele-class group, represented by its unique norm-one local
unit tuple.  The proof does not choose prime coordinates or a transversal by choice: the already
proved canonical splitting of the idele-class quotient supplies the quotient coordinate, and the
quotient relation supplies the unique diagonal `S`-unit.  This is the algebraic foundation needed
for the measure-theoretic unfolding in Connes--Marcolli Lemma 2.32.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain
open scoped NNReal

/-- Canonical representative of a split idele class: norm-one finite coordinates followed by the
positive real section. -/
def fieldOneFiniteStageIdeleFundamentalSection
    (S : Finset (HeightOneSpectrum ℤ))
    (z : FieldOneFiniteStageModuleOneClass S × NNRealˣ) :
    FieldOneFiniteStageIdele S :=
  fieldOneFiniteStageNormOneTorusIdele S
      ((fieldOneFiniteStageNormOneTorusContinuousMulEquiv S).symm z.1) *
    fieldOneFiniteStagePositiveRealIdeleSection S z.2

/-- The class of the canonical representative is exactly the inverse of the canonical split
coordinate. -/
theorem fieldOneFiniteStageIdeleFundamentalSection_class
    (S : Finset (HeightOneSpectrum ℤ))
    (z : FieldOneFiniteStageModuleOneClass S × NNRealˣ) :
    QuotientGroup.mk' (fieldOneFiniteStageSUnitImage S)
        (fieldOneFiniteStageIdeleFundamentalSection S z) =
      (fieldOneFiniteStageIdeleClassSplitMulEquiv S).symm z := by
  rw [fieldOneFiniteStageIdeleFundamentalSection, map_mul]
  change
    ((fieldOneFiniteStageNormOneTorusToModuleOne S
        ((fieldOneFiniteStageNormOneTorusContinuousMulEquiv S).symm z.1)).1 :
        FieldOneFiniteStageIdeleClassGroup S) *
      fieldOneFiniteStagePositiveRealClassSection S z.2 =
    z.1.1 * fieldOneFiniteStagePositiveRealClassSection S z.2
  have hk :
      fieldOneFiniteStageNormOneTorusToModuleOne S
          ((fieldOneFiniteStageNormOneTorusContinuousMulEquiv S).symm z.1) =
        z.1 := by
    change (fieldOneFiniteStageNormOneTorusContinuousMulEquiv S)
        ((fieldOneFiniteStageNormOneTorusContinuousMulEquiv S).symm z.1) = z.1
    exact (fieldOneFiniteStageNormOneTorusContinuousMulEquiv S).apply_symm_apply z.1
  rw [congrArg Subtype.val hk]

theorem fieldOneFiniteStageIdeleFundamentalSection_continuous
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStageIdeleFundamentalSection S) := by
  apply Continuous.mul
  · apply Continuous.prodMk
    · exact continuous_const
    · apply continuous_pi
      intro v
      exact continuous_subtype_val.comp <|
        (continuous_apply v).comp <|
          (fieldOneFiniteStageNormOneTorusContinuousMulEquiv S).symm.continuous.comp
            continuous_fst
  · exact (fieldOneFiniteStagePositiveRealIdeleSection_continuous S).comp continuous_snd

/-- The diagonal `S`-unit coordinate followed by the canonical split representative. -/
def fieldOneFiniteStageIdeleFundamentalMap
    (S : Finset (HeightOneSpectrum ℤ))
    (x : fieldOneSUnitSubgroup S ×
      (FieldOneFiniteStageModuleOneClass S × NNRealˣ)) :
    FieldOneFiniteStageIdele S :=
  fieldOneFiniteStageDiagonalUnit S x.1.1 *
    fieldOneFiniteStageIdeleFundamentalSection S x.2

theorem fieldOneFiniteStageIdeleFundamentalMap_class
    (S : Finset (HeightOneSpectrum ℤ))
    (x : fieldOneSUnitSubgroup S ×
      (FieldOneFiniteStageModuleOneClass S × NNRealˣ)) :
    QuotientGroup.mk' (fieldOneFiniteStageSUnitImage S)
        (fieldOneFiniteStageIdeleFundamentalMap S x) =
      (fieldOneFiniteStageIdeleClassSplitMulEquiv S).symm x.2 := by
  rw [fieldOneFiniteStageIdeleFundamentalMap, map_mul]
  have hdiag :
      QuotientGroup.mk' (fieldOneFiniteStageSUnitImage S)
          (fieldOneFiniteStageDiagonalUnit S x.1.1) = 1 := by
    apply (QuotientGroup.eq_one_iff _).2
    exact ⟨x.1.1, x.1.2, rfl⟩
  rw [hdiag, one_mul, fieldOneFiniteStageIdeleFundamentalSection_class]

theorem fieldOneFiniteStageIdeleFundamentalMap_injective
    (S : Finset (HeightOneSpectrum ℤ)) :
    Function.Injective (fieldOneFiniteStageIdeleFundamentalMap S) := by
  intro x y hxy
  have hclass := congrArg
    (QuotientGroup.mk' (fieldOneFiniteStageSUnitImage S)) hxy
  rw [fieldOneFiniteStageIdeleFundamentalMap_class,
    fieldOneFiniteStageIdeleFundamentalMap_class] at hclass
  have hsplit : x.2 = y.2 :=
    (fieldOneFiniteStageIdeleClassSplitMulEquiv S).symm.injective hclass
  have hunit : x.1 = y.1 := by
    apply Subtype.ext
    apply fieldOneFiniteStageDiagonalUnit_injective S
    apply mul_right_cancel
    change fieldOneFiniteStageDiagonalUnit S x.1.1 *
        fieldOneFiniteStageIdeleFundamentalSection S x.2 =
      fieldOneFiniteStageDiagonalUnit S y.1.1 *
        fieldOneFiniteStageIdeleFundamentalSection S y.2 at hxy
    rw [hsplit] at hxy
    exact hxy
  exact Prod.ext hunit hsplit

theorem fieldOneFiniteStageIdeleFundamentalMap_surjective
    (S : Finset (HeightOneSpectrum ℤ)) :
    Function.Surjective (fieldOneFiniteStageIdeleFundamentalMap S) := by
  intro u
  let z := fieldOneFiniteStageIdeleClassSplitMulEquiv S
    (QuotientGroup.mk' (fieldOneFiniteStageSUnitImage S) u)
  have hclass :
      QuotientGroup.mk' (fieldOneFiniteStageSUnitImage S)
          (fieldOneFiniteStageIdeleFundamentalSection S z) =
        QuotientGroup.mk' (fieldOneFiniteStageSUnitImage S) u := by
    rw [fieldOneFiniteStageIdeleFundamentalSection_class]
    exact (fieldOneFiniteStageIdeleClassSplitMulEquiv S).symm_apply_apply _
  rw [QuotientGroup.mk'_eq_mk'] at hclass
  obtain ⟨h, hh, hmul⟩ := hclass
  change h ∈ Subgroup.map
    (fieldOneFiniteStageDiagonalUnit S) (fieldOneSUnitSubgroup S) at hh
  rw [Subgroup.mem_map] at hh
  obtain ⟨q, hq, rfl⟩ := hh
  let qS : fieldOneSUnitSubgroup S := ⟨q, hq⟩
  refine ⟨(qS, z), ?_⟩
  change fieldOneFiniteStageDiagonalUnit S q *
      fieldOneFiniteStageIdeleFundamentalSection S z = u
  simpa [mul_comm] using hmul

/-- Exact, source-level fundamental-domain equivalence for finite-stage ideles. -/
def fieldOneFiniteStageIdeleFundamentalEquiv
    (S : Finset (HeightOneSpectrum ℤ)) :
    (fieldOneSUnitSubgroup S ×
      (FieldOneFiniteStageModuleOneClass S × NNRealˣ)) ≃
      FieldOneFiniteStageIdele S :=
  Equiv.ofBijective (fieldOneFiniteStageIdeleFundamentalMap S)
    ⟨fieldOneFiniteStageIdeleFundamentalMap_injective S,
      fieldOneFiniteStageIdeleFundamentalMap_surjective S⟩

@[simp]
theorem fieldOneFiniteStageIdeleFundamentalEquiv_apply
    (S : Finset (HeightOneSpectrum ℤ))
    (x : fieldOneSUnitSubgroup S ×
      (FieldOneFiniteStageModuleOneClass S × NNRealˣ)) :
    fieldOneFiniteStageIdeleFundamentalEquiv S x =
      fieldOneFiniteStageDiagonalUnit S x.1.1 *
        fieldOneFiniteStageIdeleFundamentalSection S x.2 :=
  rfl

/-! ## Canonical topological decomposition using the diagonal image -/

/-- Split idele-class coordinate of a literal finite-stage idele. -/
def fieldOneFiniteStageIdeleSplitCoordinate
    (S : Finset (HeightOneSpectrum ℤ))
    (u : FieldOneFiniteStageIdele S) :
    FieldOneFiniteStageModuleOneClass S × NNRealˣ :=
  fieldOneFiniteStageIdeleClassSplitHomeomorph S
    (QuotientGroup.mk' (fieldOneFiniteStageSUnitImage S) u)

theorem fieldOneFiniteStageIdeleSplitCoordinate_continuous
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStageIdeleSplitCoordinate S) :=
  (fieldOneFiniteStageIdeleClassSplitHomeomorph S).continuous.comp
    continuous_quotient_mk'

theorem fieldOneFiniteStageIdeleFundamentalSection_splitCoordinate
    (S : Finset (HeightOneSpectrum ℤ))
    (z : FieldOneFiniteStageModuleOneClass S × NNRealˣ) :
    fieldOneFiniteStageIdeleSplitCoordinate S
        (fieldOneFiniteStageIdeleFundamentalSection S z) = z := by
  rw [fieldOneFiniteStageIdeleSplitCoordinate,
    fieldOneFiniteStageIdeleFundamentalSection_class]
  exact (fieldOneFiniteStageIdeleClassSplitHomeomorph S).apply_symm_apply z

/-- Residual diagonal element left after removing the canonical split representative. -/
def fieldOneFiniteStageIdeleSUnitResidual
    (S : Finset (HeightOneSpectrum ℤ))
    (u : FieldOneFiniteStageIdele S) :
    fieldOneFiniteStageSUnitImage S :=
  ⟨u * (fieldOneFiniteStageIdeleFundamentalSection S
      (fieldOneFiniteStageIdeleSplitCoordinate S u))⁻¹, by
    apply (QuotientGroup.eq_one_iff _).1
    change QuotientGroup.mk' (fieldOneFiniteStageSUnitImage S)
        (u * (fieldOneFiniteStageIdeleFundamentalSection S
          (fieldOneFiniteStageIdeleSplitCoordinate S u))⁻¹) = 1
    rw [map_mul, map_inv,
      fieldOneFiniteStageIdeleFundamentalSection_class]
    change QuotientGroup.mk' (fieldOneFiniteStageSUnitImage S) u *
        ((fieldOneFiniteStageIdeleClassSplitHomeomorph S).symm
          (fieldOneFiniteStageIdeleClassSplitHomeomorph S
            (QuotientGroup.mk' (fieldOneFiniteStageSUnitImage S) u)))⁻¹ = 1
    rw [(fieldOneFiniteStageIdeleClassSplitHomeomorph S).symm_apply_apply]
    simp⟩

theorem fieldOneFiniteStageIdeleSUnitResidual_continuous
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStageIdeleSUnitResidual S) := by
  apply Continuous.subtype_mk
  exact continuous_id.mul <|
    ((fieldOneFiniteStageIdeleFundamentalSection_continuous S).comp
      (fieldOneFiniteStageIdeleSplitCoordinate_continuous S)).inv

/-- Multiplication of a diagonal-image coordinate with the canonical split representative. -/
def fieldOneFiniteStageIdeleImageFundamentalMap
    (S : Finset (HeightOneSpectrum ℤ))
    (x : fieldOneFiniteStageSUnitImage S ×
      (FieldOneFiniteStageModuleOneClass S × NNRealˣ)) :
    FieldOneFiniteStageIdele S :=
  x.1.1 * fieldOneFiniteStageIdeleFundamentalSection S x.2

theorem fieldOneFiniteStageIdeleImageFundamentalMap_continuous
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStageIdeleImageFundamentalMap S) :=
  (continuous_subtype_val.comp continuous_fst).mul
    ((fieldOneFiniteStageIdeleFundamentalSection_continuous S).comp continuous_snd)

theorem fieldOneFiniteStageIdeleImageFundamentalMap_splitCoordinate
    (S : Finset (HeightOneSpectrum ℤ))
    (x : fieldOneFiniteStageSUnitImage S ×
      (FieldOneFiniteStageModuleOneClass S × NNRealˣ)) :
    fieldOneFiniteStageIdeleSplitCoordinate S
        (fieldOneFiniteStageIdeleImageFundamentalMap S x) = x.2 := by
  rw [fieldOneFiniteStageIdeleSplitCoordinate,
    fieldOneFiniteStageIdeleImageFundamentalMap, map_mul]
  have hxone :
      QuotientGroup.mk' (fieldOneFiniteStageSUnitImage S) x.1.1 = 1 :=
    (QuotientGroup.eq_one_iff _).2 x.1.2
  rw [hxone, one_mul, fieldOneFiniteStageIdeleFundamentalSection_class]
  exact (fieldOneFiniteStageIdeleClassSplitHomeomorph S).apply_symm_apply x.2

theorem fieldOneFiniteStageIdeleImageFundamentalMap_residual
    (S : Finset (HeightOneSpectrum ℤ))
    (x : fieldOneFiniteStageSUnitImage S ×
      (FieldOneFiniteStageModuleOneClass S × NNRealˣ)) :
    fieldOneFiniteStageIdeleSUnitResidual S
        (fieldOneFiniteStageIdeleImageFundamentalMap S x) = x.1 := by
  have hsplit := fieldOneFiniteStageIdeleImageFundamentalMap_splitCoordinate S x
  apply Subtype.ext
  change fieldOneFiniteStageIdeleImageFundamentalMap S x *
      (fieldOneFiniteStageIdeleFundamentalSection S
        (fieldOneFiniteStageIdeleSplitCoordinate S
          (fieldOneFiniteStageIdeleImageFundamentalMap S x)))⁻¹ = x.1.1
  rw [hsplit]
  simp [fieldOneFiniteStageIdeleImageFundamentalMap]

/-- Exact topological fundamental-domain decomposition.  The diagonal image is discrete, while
the second factor is the compact module-one group times the positive real module. -/
def fieldOneFiniteStageIdeleImageFundamentalHomeomorph
    (S : Finset (HeightOneSpectrum ℤ)) :
    (fieldOneFiniteStageSUnitImage S ×
      (FieldOneFiniteStageModuleOneClass S × NNRealˣ)) ≃ₜ
      FieldOneFiniteStageIdele S where
  toFun := fieldOneFiniteStageIdeleImageFundamentalMap S
  invFun u :=
    (fieldOneFiniteStageIdeleSUnitResidual S u,
      fieldOneFiniteStageIdeleSplitCoordinate S u)
  left_inv x := by
    apply Prod.ext
    · exact fieldOneFiniteStageIdeleImageFundamentalMap_residual S x
    · exact fieldOneFiniteStageIdeleImageFundamentalMap_splitCoordinate S x
  right_inv u := by
    change (fieldOneFiniteStageIdeleSUnitResidual S u).1 *
        fieldOneFiniteStageIdeleFundamentalSection S
          (fieldOneFiniteStageIdeleSplitCoordinate S u) = u
    rw [fieldOneFiniteStageIdeleSUnitResidual]
    simp
  continuous_toFun := fieldOneFiniteStageIdeleImageFundamentalMap_continuous S
  continuous_invFun :=
    (fieldOneFiniteStageIdeleSUnitResidual_continuous S).prodMk
      (fieldOneFiniteStageIdeleSplitCoordinate_continuous S)

/-- The canonical split representative respects multiplication. -/
def fieldOneFiniteStageIdeleFundamentalSectionMonoidHom
    (S : Finset (HeightOneSpectrum ℤ)) :
    (FieldOneFiniteStageModuleOneClass S × NNRealˣ) →*
      FieldOneFiniteStageIdele S where
  toFun := fieldOneFiniteStageIdeleFundamentalSection S
  map_one' := by
    apply Prod.ext
    · simp [fieldOneFiniteStageIdeleFundamentalSection]
    · funext v
      apply Units.ext
      simp [fieldOneFiniteStageIdeleFundamentalSection]
  map_mul' z w := by
    change
      fieldOneFiniteStageNormOneTorusIdele S
          ((fieldOneFiniteStageNormOneTorusContinuousMulEquiv S).symm (z.1 * w.1)) *
          fieldOneFiniteStagePositiveRealIdeleSection S (z.2 * w.2) =
        (fieldOneFiniteStageNormOneTorusIdele S
            ((fieldOneFiniteStageNormOneTorusContinuousMulEquiv S).symm z.1) *
            fieldOneFiniteStagePositiveRealIdeleSection S z.2) *
          (fieldOneFiniteStageNormOneTorusIdele S
              ((fieldOneFiniteStageNormOneTorusContinuousMulEquiv S).symm w.1) *
            fieldOneFiniteStagePositiveRealIdeleSection S w.2)
    rw [map_mul, map_mul, map_mul]
    ac_rfl

/-- The topological fundamental-domain map as a multiplicative equivalence. -/
def fieldOneFiniteStageIdeleImageFundamentalMulEquiv
    (S : Finset (HeightOneSpectrum ℤ)) :
    (fieldOneFiniteStageSUnitImage S ×
      (FieldOneFiniteStageModuleOneClass S × NNRealˣ)) ≃*
      FieldOneFiniteStageIdele S where
  toEquiv := (fieldOneFiniteStageIdeleImageFundamentalHomeomorph S).toEquiv
  map_mul' x y := by
    change (x.1 * y.1).1 *
          fieldOneFiniteStageIdeleFundamentalSection S (x.2 * y.2) =
        (x.1.1 * fieldOneFiniteStageIdeleFundamentalSection S x.2) *
          (y.1.1 * fieldOneFiniteStageIdeleFundamentalSection S y.2)
    have hsection := map_mul
      (fieldOneFiniteStageIdeleFundamentalSectionMonoidHom S) x.2 y.2
    change fieldOneFiniteStageIdeleFundamentalSection S (x.2 * y.2) =
      fieldOneFiniteStageIdeleFundamentalSection S x.2 *
        fieldOneFiniteStageIdeleFundamentalSection S y.2 at hsection
    rw [hsection]
    ac_rfl

/-- Continuous multiplicative equivalence realizing
`A_S^* ≃ Q_S^* × K_S × R_+^*`. -/
def fieldOneFiniteStageIdeleImageFundamentalContinuousMulEquiv
    (S : Finset (HeightOneSpectrum ℤ)) :
    (fieldOneFiniteStageSUnitImage S ×
      (FieldOneFiniteStageModuleOneClass S × NNRealˣ)) ≃ₜ*
      FieldOneFiniteStageIdele S where
  toMulEquiv := fieldOneFiniteStageIdeleImageFundamentalMulEquiv S
  continuous_toFun := fieldOneFiniteStageIdeleImageFundamentalMap_continuous S
  continuous_invFun :=
    (fieldOneFiniteStageIdeleImageFundamentalHomeomorph S).symm.continuous

end

end GaloisForLFunctions.RHTower
