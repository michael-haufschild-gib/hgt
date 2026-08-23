import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldValuationSequence

/-! # Hasse classification of valuation-zero units -/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped WithZero

universe u v

noncomputable section

/-- Integral units map canonically into the valuation-zero units of a DVR fraction field. -/
noncomputable def discreteValuationRingUnitsToTameValKernel
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] :
    Aˣ →* (tameValHom ((IsDiscreteValuationRing.maximalIdeal A).valuation F)).ker :=
  MonoidHom.codRestrict (Units.map (algebraMap A F).toMonoidHom)
    (tameValHom ((IsDiscreteValuationRing.maximalIdeal A).valuation F)).ker fun x => by
      rw [tameValHom_mem_ker_iff]
      exact Valuation.Integers.one_of_isUnit' x.isUnit fun y =>
        IsDedekindDomain.HeightOneSpectrum.valuation_le_one
          (K := F) (IsDiscreteValuationRing.maximalIdeal A) y

/-- The integral-unit map into valuation-zero field units is injective. -/
theorem discreteValuationRingUnitsToTameValKernel_injective
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] :
    Function.Injective (discreteValuationRingUnitsToTameValKernel A F) := by
  intro x y h
  apply Units.map_injective (IsFractionRing.injective A F)
  exact congrArg Subtype.val h

/-- Every valuation-zero field unit comes from an integral unit. -/
theorem discreteValuationRingUnitsToTameValKernel_surjective
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] :
    Function.Surjective (discreteValuationRingUnitsToTameValKernel A F) := by
  intro a
  obtain ⟨b, hb⟩ :=
    discreteValuationRingFractionField_tameValHom_ker_unitsMap_surjective A F a.1 a.2
  exact ⟨b, Subtype.ext hb⟩

/-- The unit group of a DVR is canonically the valuation-zero subgroup of its fraction field. -/
noncomputable def discreteValuationRingUnitsEquivTameValKernel
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] :
    Aˣ ≃* (tameValHom ((IsDiscreteValuationRing.maximalIdeal A).valuation F)).ker :=
  MulEquiv.ofBijective (discreteValuationRingUnitsToTameValKernel A F)
    ⟨discreteValuationRingUnitsToTameValKernel_injective A F,
      discreteValuationRingUnitsToTameValKernel_surjective A F⟩

@[simp] theorem discreteValuationRingUnitsEquivTameValKernel_apply
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] (x : Aˣ) :
    discreteValuationRingUnitsEquivTameValKernel A F x =
      discreteValuationRingUnitsToTameValKernel A F x := by
  rfl

/-- Two integral units have the same valuation-zero field image exactly when they agree. -/
theorem discreteValuationRingUnitsToTameValKernel_congr_hasse_iff
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] (x y : Aˣ) :
    discreteValuationRingUnitsToTameValKernel A F x =
        discreteValuationRingUnitsToTameValKernel A F y ↔ x = y := by
  exact ⟨fun h => discreteValuationRingUnitsToTameValKernel_injective A F h, congrArg _⟩

/-- Every valuation-zero field unit has a unique integral-unit representative. -/
theorem discreteValuationRingFractionField_tameValKer_existsUnique_integralUnit
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (a : (tameValHom ((IsDiscreteValuationRing.maximalIdeal A).valuation F)).ker) :
    ∃! b : Aˣ, Units.map (algebraMap A F) b = a.1 := by
  obtain ⟨b, hb⟩ :=
    discreteValuationRingFractionField_tameValHom_ker_unitsMap_surjective A F a.1 a.2
  refine ⟨b, hb, ?_⟩
  intro y hy
  apply Units.map_injective (IsFractionRing.injective A F)
  exact hy.trans hb.symm

end


end GaloisForLFunctions.HTGeometry.ABHN
