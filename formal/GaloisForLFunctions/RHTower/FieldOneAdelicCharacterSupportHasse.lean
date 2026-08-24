import GaloisForLFunctions.HTGeometry.ABHN.FinsuppReciprocitySupportCardinality
import GaloisForLFunctions.RHTower.FieldOneRationalPrimaryReciprocity

/-!
# Hasse support laws for the rational adelic character

The local values of the standard finite-adele character form a `Finsupp`.  Its sum is the global
finite character, so a character-neutral finite adele cannot have exactly one active place.  For a
diagonal rational, adjoining the negative archimedean phase gives an unconditional all-place
zero-sum profile.  Thus every nonintegral rational has an active finite place compensating its
archimedean phase.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry.ABHN
open IsDedekindDomain

noncomputable section

noncomputable local instance : DecidableEq (HeightOneSpectrum ℤ) := Classical.decEq _

/-- Finitely supported profile of local additive-character values of a rational finite adele. -/
noncomputable def fieldOneFiniteAdeleLocalUnitCharacterProfile
    (x : FieldOneFiniteAdele) : HeightOneSpectrum ℤ →₀ UnitAddCircle := by
  classical
  let h := fieldOneFiniteAdeleLocalUnitCharacter_hasFiniteSupport x
  exact
    { toFun := fun v => fieldOneFiniteAdeleLocalUnitCharacter v (x v)
      support := h.toFinset
      mem_support_toFun := by
        intro v
        rw [h.mem_toFinset]
        rfl }

@[simp]
theorem fieldOneFiniteAdeleLocalUnitCharacterProfile_apply
    (x : FieldOneFiniteAdele) (v : HeightOneSpectrum ℤ) :
    fieldOneFiniteAdeleLocalUnitCharacterProfile x v =
      fieldOneFiniteAdeleLocalUnitCharacter v (x v) := rfl

/-- Summing the local profile recovers the canonical finite-adele character. -/
theorem fieldOneFiniteAdeleLocalUnitCharacterProfile_sum
    (x : FieldOneFiniteAdele) :
    (fieldOneFiniteAdeleLocalUnitCharacterProfile x).sum (fun _ z => z) =
      fieldOneFiniteAdeleStandardUnitAddCircleRaw x := by
  classical
  change
    (fieldOneFiniteAdeleLocalUnitCharacterProfile x).support.sum
        (fun v => fieldOneFiniteAdeleLocalUnitCharacter v (x v)) =
      ∑ᶠ v, fieldOneFiniteAdeleLocalUnitCharacter v (x v)
  symm
  apply finsum_eq_finsetSum_of_support_subset
  intro v hv
  exact Finsupp.mem_support_iff.mpr hv

/-- A nonzero character-neutral finite adele has at least two active local phases. -/
theorem fieldOneFiniteAdeleLocalUnitCharacterProfile_two_le_support_card
    (x : FieldOneFiniteAdele)
    (hglobal : fieldOneFiniteAdeleStandardUnitAddCircleCharacter x = 0)
    (hne : fieldOneFiniteAdeleLocalUnitCharacterProfile x ≠ 0) :
    2 ≤ (fieldOneFiniteAdeleLocalUnitCharacterProfile x).support.card := by
  apply finsupp_two_le_support_card_of_sum_eq_zero
    (fieldOneFiniteAdeleLocalUnitCharacterProfile x)
  · rw [fieldOneFiniteAdeleLocalUnitCharacterProfile_sum]
    exact hglobal
  · exact hne

/-- A nonzero character-neutral finite adele has two distinct active finite places. -/
theorem fieldOneFiniteAdeleLocalUnitCharacterProfile_exists_two_nonzero_places
    (x : FieldOneFiniteAdele)
    (hglobal : fieldOneFiniteAdeleStandardUnitAddCircleCharacter x = 0)
    (hne : fieldOneFiniteAdeleLocalUnitCharacterProfile x ≠ 0) :
    ∃ v w : HeightOneSpectrum ℤ, v ≠ w ∧
      fieldOneFiniteAdeleLocalUnitCharacter v (x v) ≠ 0 ∧
      fieldOneFiniteAdeleLocalUnitCharacter w (x w) ≠ 0 := by
  simpa only [fieldOneFiniteAdeleLocalUnitCharacterProfile_apply] using
    finsupp_exists_two_nonzero_places_of_sum_eq_zero
      (fieldOneFiniteAdeleLocalUnitCharacterProfile x)
      (by
        rw [fieldOneFiniteAdeleLocalUnitCharacterProfile_sum]
        exact hglobal)
      hne

/-- Every active phase of a character-neutral finite adele has a distinct active partner. -/
theorem fieldOneFiniteAdeleLocalUnitCharacterProfile_exists_other_nonzero_place
    (x : FieldOneFiniteAdele)
    (hglobal : fieldOneFiniteAdeleStandardUnitAddCircleCharacter x = 0)
    {v : HeightOneSpectrum ℤ}
    (hv : fieldOneFiniteAdeleLocalUnitCharacter v (x v) ≠ 0) :
    ∃ w, w ≠ v ∧ fieldOneFiniteAdeleLocalUnitCharacter w (x w) ≠ 0 := by
  apply finsupp_exists_other_nonzero_place_of_sum_eq_zero
    (fieldOneFiniteAdeleLocalUnitCharacterProfile x)
  · rw [fieldOneFiniteAdeleLocalUnitCharacterProfile_sum]
    exact hglobal
  · simpa using hv

/-- Embedding of the unique rational archimedean character coordinate. -/
def fieldOneRationalArchimedeanCharacterEmbedding :
    Unit ↪ (Unit ⊕ HeightOneSpectrum ℤ) :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- Embedding of rational finite places into the all-place character index. -/
def fieldOneRationalFiniteCharacterEmbedding :
    HeightOneSpectrum ℤ ↪ (Unit ⊕ HeightOneSpectrum ℤ) :=
  ⟨Sum.inr, Sum.inr_injective⟩

/-- All-place additive-character profile of a diagonal rational. -/
noncomputable def fieldOneRationalAllPlaceUnitCharacterProfile (q : ℚ) :
    (Unit ⊕ HeightOneSpectrum ℤ) →₀ UnitAddCircle :=
  Finsupp.single (Sum.inl ()) (-fieldOneRationalUnitAddCircleCharacter q) +
    Finsupp.embDomain fieldOneRationalFiniteCharacterEmbedding
      (fieldOneFiniteAdeleLocalUnitCharacterProfile
        (algebraMap ℚ FieldOneFiniteAdele q))

@[simp]
theorem fieldOneRationalAllPlaceUnitCharacterProfile_inl
    (q : ℚ) (u : Unit) :
    fieldOneRationalAllPlaceUnitCharacterProfile q (Sum.inl u) =
      -fieldOneRationalUnitAddCircleCharacter q := by
  cases u
  simp [fieldOneRationalAllPlaceUnitCharacterProfile,
    Finsupp.embDomain_apply, fieldOneRationalFiniteCharacterEmbedding]

@[simp]
theorem fieldOneRationalAllPlaceUnitCharacterProfile_inr
    (q : ℚ) (v : HeightOneSpectrum ℤ) :
    fieldOneRationalAllPlaceUnitCharacterProfile q (Sum.inr v) =
      fieldOneFiniteAdeleLocalUnitCharacter v
        ((algebraMap ℚ FieldOneFiniteAdele q) v) := by
  simp [fieldOneRationalAllPlaceUnitCharacterProfile,
    Finsupp.embDomain_apply, fieldOneRationalFiniteCharacterEmbedding]

/-- The rational all-place character profile satisfies additive global reciprocity. -/
theorem fieldOneRationalAllPlaceUnitCharacterProfile_sum_eq_zero (q : ℚ) :
    (fieldOneRationalAllPlaceUnitCharacterProfile q).sum (fun _ z => z) = 0 := by
  rw [fieldOneRationalAllPlaceUnitCharacterProfile,
    Finsupp.sum_add_index' (by intros; rfl) (by intros; rfl),
    Finsupp.sum_single_index (by simp), Finsupp.sum_embDomain,
    fieldOneFiniteAdeleLocalUnitCharacterProfile_sum]
  change -fieldOneRationalUnitAddCircleCharacter q +
    fieldOneFiniteAdeleStandardUnitAddCircleCharacter
      (algebraMap ℚ FieldOneFiniteAdele q) = 0
  rw [fieldOneFiniteAdeleStandardUnitAddCircleCharacter_algebraMap_rat]
  exact neg_add_cancel _

/-- A nonzero archimedean rational phase makes the all-place profile nonzero. -/
theorem fieldOneRationalAllPlaceUnitCharacterProfile_ne_zero
    (q : ℚ) (hq : fieldOneRationalUnitAddCircleCharacter q ≠ 0) :
    fieldOneRationalAllPlaceUnitCharacterProfile q ≠ 0 := by
  intro hzero
  have hcoord := Finsupp.ext_iff.mp hzero (Sum.inl ())
  simpa using hq (neg_eq_zero.mp (by simpa using hcoord))

/-- A nontrivial rational phase has all-place support cardinality at least two. -/
theorem fieldOneRationalAllPlaceUnitCharacterProfile_two_le_support_card
    (q : ℚ) (hq : fieldOneRationalUnitAddCircleCharacter q ≠ 0) :
    2 ≤ (fieldOneRationalAllPlaceUnitCharacterProfile q).support.card :=
  finsupp_two_le_support_card_of_sum_eq_zero
    (fieldOneRationalAllPlaceUnitCharacterProfile q)
    (fieldOneRationalAllPlaceUnitCharacterProfile_sum_eq_zero q)
    (fieldOneRationalAllPlaceUnitCharacterProfile_ne_zero q hq)

/-- A nontrivial rational phase activates two distinct all-place coordinates. -/
theorem fieldOneRationalAllPlaceUnitCharacterProfile_exists_two_nonzero_places
    (q : ℚ) (hq : fieldOneRationalUnitAddCircleCharacter q ≠ 0) :
    ∃ v w : Unit ⊕ HeightOneSpectrum ℤ, v ≠ w ∧
      fieldOneRationalAllPlaceUnitCharacterProfile q v ≠ 0 ∧
      fieldOneRationalAllPlaceUnitCharacterProfile q w ≠ 0 :=
  finsupp_exists_two_nonzero_places_of_sum_eq_zero
    (fieldOneRationalAllPlaceUnitCharacterProfile q)
    (fieldOneRationalAllPlaceUnitCharacterProfile_sum_eq_zero q)
    (fieldOneRationalAllPlaceUnitCharacterProfile_ne_zero q hq)

/-- Every active all-place rational phase has a distinct active partner. -/
theorem fieldOneRationalAllPlaceUnitCharacterProfile_exists_other_nonzero_place
    (q : ℚ) {v : Unit ⊕ HeightOneSpectrum ℤ}
    (hv : fieldOneRationalAllPlaceUnitCharacterProfile q v ≠ 0) :
    ∃ w, w ≠ v ∧ fieldOneRationalAllPlaceUnitCharacterProfile q w ≠ 0 :=
  finsupp_exists_other_nonzero_place_of_sum_eq_zero
    (fieldOneRationalAllPlaceUnitCharacterProfile q)
    (fieldOneRationalAllPlaceUnitCharacterProfile_sum_eq_zero q) hv

/-- A nonzero archimedean rational phase is compensated at a finite place. -/
theorem fieldOneRationalAllPlaceUnitCharacterProfile_exists_finite_of_arch_ne_zero
    (q : ℚ) (hq : fieldOneRationalUnitAddCircleCharacter q ≠ 0) :
    ∃ v : HeightOneSpectrum ℤ,
      fieldOneFiniteAdeleLocalUnitCharacter v
        ((algebraMap ℚ FieldOneFiniteAdele q) v) ≠ 0 := by
  obtain ⟨w, hwne, hw⟩ :=
    fieldOneRationalAllPlaceUnitCharacterProfile_exists_other_nonzero_place
      q (v := Sum.inl ()) (by simpa using neg_ne_zero.mpr hq)
  cases w with
  | inl u => exact False.elim (hwne (by cases u; rfl))
  | inr v => exact ⟨v, by simpa using hw⟩

/-- The rational archimedean phase vanishes exactly on embedded integers. -/
theorem fieldOneRationalUnitAddCircleCharacter_eq_zero_iff_integer (q : ℚ) :
    fieldOneRationalUnitAddCircleCharacter q = 0 ↔
      ∃ n : ℤ, q = n := by
  change (((q : ℝ) : UnitAddCircle) = 0) ↔ _
  rw [AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hn' : (n : ℝ) = (q : ℝ) := by simpa using hn
    exact_mod_cast hn'.symm
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    simp

/-- Every nonintegral rational has a finite place carrying a nonzero local phase. -/
theorem fieldOneRationalAllPlaceUnitCharacterProfile_exists_finite_of_not_integer
    (q : ℚ) (hq : ¬ ∃ n : ℤ, q = n) :
    ∃ v : HeightOneSpectrum ℤ,
      fieldOneFiniteAdeleLocalUnitCharacter v
        ((algebraMap ℚ FieldOneFiniteAdele q) v) ≠ 0 :=
  fieldOneRationalAllPlaceUnitCharacterProfile_exists_finite_of_arch_ne_zero q
    (by
      intro hzero
      exact hq ((fieldOneRationalUnitAddCircleCharacter_eq_zero_iff_integer q).mp hzero))

end

end GaloisForLFunctions.RHTower
