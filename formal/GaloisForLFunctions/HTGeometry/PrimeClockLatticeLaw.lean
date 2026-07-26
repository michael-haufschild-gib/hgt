import GaloisForLFunctions.HTGeometry.PrimeClockCompletionCorrespondence
import GaloisForLFunctions.HTGeometry.PrimeProfileInvariantGrassmannRepresentation

/-!
# The lattice law of the prime-clock correspondence

The prime-clock correspondence sends a source family to its complete clock submodule and to the
embedded differential field its carriers generate, and inclusion on one side is inclusion on the
other.  This module records that the correspondence is a map of lattices.

Joining two source families is disjoint union of their index sets.  On the module side that is the
join of the two clock submodules, and on the field side it is the compositum, so the correspondence
carries joins to joins.

For meets the intrinsic statement is on the pullback: a prime-profile carrier lies in both embedded
fields exactly when its clock class lies in both clock submodules.  Hence the pullback of an
intersection of source-generated fields is the intersection of the corresponding clock submodules.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Set

noncomputable section

variable {I J : Type*}

/-! ### Joins -/

/-- The clock jets of a disjoint union of source families are the jets of the two families. -/
theorem range_primeProfileClockJetFamily_sumElim
    (c : I → ArithmeticFunction ℂ) (d : J → ArithmeticFunction ℂ) :
    Set.range (primeProfileClockJetFamily (Sum.elim c d)) =
      Set.range (primeProfileClockJetFamily c) ∪
        Set.range (primeProfileClockJetFamily d) := by
  ext q
  constructor
  · rintro ⟨⟨k, n⟩, rfl⟩
    cases k with
    | inl i => exact Or.inl ⟨(i, n), rfl⟩
    | inr j => exact Or.inr ⟨(j, n), rfl⟩
  · rintro (⟨⟨i, n⟩, rfl⟩ | ⟨⟨j, n⟩, rfl⟩)
    · exact ⟨(Sum.inl i, n), rfl⟩
    · exact ⟨(Sum.inr j, n), rfl⟩

/-- **Join on the module side.**  The clock submodule of a disjoint union of source families is the
join of the two clock submodules. -/
theorem primeProfileClockSubmodule_sumElim
    (c : I → ArithmeticFunction ℂ) (d : J → ArithmeticFunction ℂ) :
    primeProfileClockSubmodule (Sum.elim c d) =
      primeProfileClockSubmodule c ⊔ primeProfileClockSubmodule d := by
  rw [primeProfileClockSubmodule, primeProfileClockSubmodule, primeProfileClockSubmodule,
    range_primeProfileClockJetFamily_sumElim, Submodule.span_union]

/-- **Join on the field side.**  The embedded differential field of a disjoint union of source
families is the compositum of the two embedded fields. -/
theorem primeProfile_differentialAdjoin_sumElim
    (c : I → ArithmeticFunction ℂ) (d : J → ArithmeticFunction ℂ) :
    GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
        (Set.range (fun k => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (Sum.elim c d k))) =
      GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
          (Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (c i))) ⊔
        GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
          (Set.range (fun j => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (d j))) := by
  have hrange : (Set.range (fun k => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (Sum.elim c d k))) =
      Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (c i)) ∪
        Set.range (fun j => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (d j)) := by
    ext z
    constructor
    · rintro ⟨k, rfl⟩
      cases k with
      | inl i => exact Or.inl ⟨i, rfl⟩
      | inr j => exact Or.inr ⟨j, rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr j, rfl⟩
  have hjet : GaloisForLFunctions.differentialJetSet
      (Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (c i)) ∪
        Set.range (fun j => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (d j))) =
      GaloisForLFunctions.differentialJetSet
          (Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (c i))) ∪
        GaloisForLFunctions.differentialJetSet
          (Set.range (fun j => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (d j))) := by
    ext z
    constructor
    · rintro ⟨x, hx | hx, n, rfl⟩
      · exact Or.inl ⟨x, hx, n, rfl⟩
      · exact Or.inr ⟨x, hx, n, rfl⟩
    · rintro (⟨x, hx, n, rfl⟩ | ⟨x, hx, n, rfl⟩)
      · exact ⟨x, Or.inl hx, n, rfl⟩
      · exact ⟨x, Or.inr hx, n, rfl⟩
  rw [GaloisForLFunctions.differentialAdjoin, hrange, hjet,
    IntermediateField.adjoin_union, GaloisForLFunctions.differentialAdjoin,
    GaloisForLFunctions.differentialAdjoin]

/-! ### Meets -/

/-- **Intrinsic meet law.**  A prime-profile carrier lies in two source-generated embedded
differential fields exactly when its clock class lies in both clock submodules; hence the pullback
of the intersection is the intersection of the clock submodules. -/
theorem primeProfileCarrierPullback_inf
    (c : I → ArithmeticFunction ℂ) (d : J → ArithmeticFunction ℂ)
    (hcsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (c i))
    (hdsupport : ∀ j, PrimeProfileSupportedOnPositivePrimePowers (d j)) :
    primeProfileCarrierPullback
        (GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
            (Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
              arithmeticFunctionFractionField (c i))) ⊓
          GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
            (Set.range (fun j => algebraMap (ArithmeticFunction ℂ)
              arithmeticFunctionFractionField (d j)))) =
      ((primeProfileClockSubmodule c ⊓ primeProfileClockSubmodule d :
        Submodule ℂ PrimeProfileClockQuotient) : Set PrimeProfileClockQuotient) := by
  ext q
  unfold primeProfileCarrierPullback
  constructor
  · rintro ⟨f, hfsupport, rfl, hcf, hdf⟩
    exact ⟨(primeProfileCarrier_mem_differentialAdjoin_iff_intrinsicClockClass_mem
        c hcsupport f hfsupport).mp hcf,
      (primeProfileCarrier_mem_differentialAdjoin_iff_intrinsicClockClass_mem
        d hdsupport f hfsupport).mp hdf⟩
  · rintro ⟨hqc, hqd⟩
    refine ⟨primeProfileClockRepresentative q,
      primeProfileClockRepresentative_supportedOnPositivePrimePowers q,
      primeProfileClockClass_representative q, ?_, ?_⟩
    · apply (primeProfileCarrier_mem_differentialAdjoin_iff_intrinsicClockClass_mem
        c hcsupport _ (primeProfileClockRepresentative_supportedOnPositivePrimePowers q)).mpr
      simpa only [primeProfileClockClass_representative] using hqc
    · apply (primeProfileCarrier_mem_differentialAdjoin_iff_intrinsicClockClass_mem
        d hdsupport _ (primeProfileClockRepresentative_supportedOnPositivePrimePowers q)).mpr
      simpa only [primeProfileClockClass_representative] using hqd

/-- The embedded differential field of a source family is the Grassmann field of its complete
clock submodule.  The submodule is clock-invariant, so its represented basis field is already
closed under differentiation. -/
theorem primeProfile_differentialAdjoin_eq_grassmannField_clockSubmodule
    (c : I → ArithmeticFunction ℂ)
    (hcsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (c i)) :
    GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
        (Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (c i))) =
      primeProfileGrassmannField (primeProfileClockSubmodule c) := by
  have hinv : PrimeProfileClockInvariant (primeProfileClockSubmodule c) :=
    primeProfileClockSubmodule_invariant c
  have hsrc := primeProfileClockSubmodule_grassmannSource (primeProfileClockSubmodule c) hinv
  have hfield := (primeProfile_differentialAdjoin_eq_iff_intrinsicClockSubmodule_eq
    c (primeProfileGrassmannSource (primeProfileClockSubmodule c)) hcsupport
    (primeProfileGrassmannSource_supportedOnPositivePrimePowers _)).mpr hsrc.symm
  rw [hfield, differentialAdjoin_grassmannSource_eq_grassmannField _ hinv]

/-- **Meet law.**  A source family presenting the intersection of two clock submodules generates
exactly the intersection of the two embedded differential fields. -/
theorem primeProfile_differentialAdjoin_inf_of_clockSubmodule_eq_inf
    {H : Type*} (c : I → ArithmeticFunction ℂ) (d : J → ArithmeticFunction ℂ)
    (e : H → ArithmeticFunction ℂ)
    (hcsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (c i))
    (hdsupport : ∀ j, PrimeProfileSupportedOnPositivePrimePowers (d j))
    (hesupport : ∀ h, PrimeProfileSupportedOnPositivePrimePowers (e h))
    (hmodule : primeProfileClockSubmodule e =
      primeProfileClockSubmodule c ⊓ primeProfileClockSubmodule d) :
    GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
        (Set.range (fun h => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (e h))) =
      GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
          (Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (c i))) ⊓
        GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
          (Set.range (fun j => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (d j))) := by
  rw [primeProfile_differentialAdjoin_eq_grassmannField_clockSubmodule e hesupport,
    primeProfile_differentialAdjoin_eq_grassmannField_clockSubmodule c hcsupport,
    primeProfile_differentialAdjoin_eq_grassmannField_clockSubmodule d hdsupport,
    primeProfileGrassmannField_inf, hmodule]

/-- **Join law, intrinsic form.**  A source family presenting the join of two clock submodules
generates exactly the compositum of the two embedded differential fields. -/
theorem primeProfile_differentialAdjoin_sup_of_clockSubmodule_eq_sup
    {H : Type*} (c : I → ArithmeticFunction ℂ) (d : J → ArithmeticFunction ℂ)
    (e : H → ArithmeticFunction ℂ)
    (hcsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (c i))
    (hdsupport : ∀ j, PrimeProfileSupportedOnPositivePrimePowers (d j))
    (hesupport : ∀ h, PrimeProfileSupportedOnPositivePrimePowers (e h))
    (hmodule : primeProfileClockSubmodule e =
      primeProfileClockSubmodule c ⊔ primeProfileClockSubmodule d) :
    GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
        (Set.range (fun h => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (e h))) =
      GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
          (Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (c i))) ⊔
        GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
          (Set.range (fun j => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (d j))) := by
  rw [primeProfile_differentialAdjoin_eq_grassmannField_clockSubmodule e hesupport,
    primeProfile_differentialAdjoin_eq_grassmannField_clockSubmodule c hcsupport,
    primeProfile_differentialAdjoin_eq_grassmannField_clockSubmodule d hdsupport,
    primeProfileGrassmannField_sup, hmodule]

end

end GaloisForLFunctions.HTGeometry
