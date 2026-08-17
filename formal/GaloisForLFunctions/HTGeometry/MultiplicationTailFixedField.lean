import GaloisForLFunctions.HTGeometry.DifferentialKolchinClosure

/-!
# The tail of an increasing tower of translation fixed fields

An intersection of translation fixed fields is the fixed field of the union of the labelling sets,
and — when every element has Kolchin-closed stabilizer — of the Kolchin closure of that union.

This is the field-theoretic skeleton of a multiplication tail: if the `n`-th pullback of the
function field is the field fixed by the `m^n`-torsion translations, the tail is the field fixed by
the Kolchin closure of all `m`-primary torsion.  Only the two geometric identifications — the finite
Galois description of each level and the identification of that closure — remain outside.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K L A : Type*} [Field K] [Field L] [Algebra K L] [Differential L]

/-- The fixed field of a union of labelling sets is the intersection of the fixed fields. -/
theorem mem_differentialTranslationFixedField_iUnion_iff {ι' : Type*}
    (translation : A → DifferentialAlgEquiv K L) (S : ι' → Set A) {z : L} :
    z ∈ differentialTranslationFixedField translation (⋃ n, S n)
      ↔ ∀ n, z ∈ differentialTranslationFixedField translation (S n) := by
  simp only [mem_differentialTranslationFixedField_iff]
  constructor
  · intro hz n a ha
    exact hz a (Set.mem_iUnion.mpr ⟨n, ha⟩)
  · intro hz a ha
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
    exact hz n a hn

/-- Monotone labelling sets give an antitone tower of fixed fields. -/
theorem differentialTranslationFixedField_antitone
    (translation : A → DifferentialAlgEquiv K L) {S T : Set A} (hST : S ⊆ T) :
    differentialTranslationFixedField translation T
      ≤ differentialTranslationFixedField translation S := by
  intro z hz
  exact fun a ha => hz a (hST ha)

variable {ι : Type*} [Differential K]

/-- **The multiplication-tail identity, field-theoretic form.**  The intersection of the tower of
translation fixed fields is the field fixed by the Kolchin closure of all the labels. -/
theorem mem_iInter_differentialTranslationFixedField_iff_kolchinClosure {ι' : Type*}
    (translation : (ι → K) → DifferentialAlgEquiv K L) (S : ι' → Set (ι → K))
    (hclosed : ∀ z : L,
      IsKolchinClosedOver K {a : ι → K | (translation a).toAlgEquiv z = z}) {z : L} :
    (∀ n, z ∈ differentialTranslationFixedField translation (S n))
      ↔ z ∈ differentialTranslationFixedField translation
          (kolchinClosureOver K (⋃ n, S n)) := by
  have hclosureEq :
      differentialTranslationFixedField translation (⋃ n, S n)
        = differentialTranslationFixedField translation (kolchinClosureOver K (⋃ n, S n)) :=
    differentialTranslationFixedField_eq_of_kolchinClosureOver_eq translation _ _ rfl hclosed
  rw [← mem_differentialTranslationFixedField_iUnion_iff translation S, hclosureEq]

/-- The same statement with the tower on the left, as an inclusion of intermediate fields. -/
theorem iInf_le_differentialTranslationFixedField_kolchinClosure {ι' : Type*}
    (translation : (ι → K) → DifferentialAlgEquiv K L) (S : ι' → Set (ι → K))
    (hclosed : ∀ z : L,
      IsKolchinClosedOver K {a : ι → K | (translation a).toAlgEquiv z = z}) :
    (⨅ n, differentialTranslationFixedField translation (S n))
      ≤ differentialTranslationFixedField translation
          (kolchinClosureOver K (⋃ n, S n)) := by
  intro z hz
  refine (mem_iInter_differentialTranslationFixedField_iff_kolchinClosure
    translation S hclosed).mp fun n => ?_
  exact (iInf_le (fun n => differentialTranslationFixedField translation (S n)) n) hz

/-- The reverse inclusion. -/
theorem differentialTranslationFixedField_kolchinClosure_le_iInf {ι' : Type*}
    (translation : (ι → K) → DifferentialAlgEquiv K L) (S : ι' → Set (ι → K))
    (hclosed : ∀ z : L,
      IsKolchinClosedOver K {a : ι → K | (translation a).toAlgEquiv z = z}) :
    differentialTranslationFixedField translation
        (kolchinClosureOver K (⋃ n, S n))
      ≤ ⨅ n, differentialTranslationFixedField translation (S n) :=
  le_iInf fun n _ hz =>
    (mem_iInter_differentialTranslationFixedField_iff_kolchinClosure
      translation S hclosed).mpr hz n

/-- **The multiplication-tail identity.** -/
theorem iInf_differentialTranslationFixedField_eq_kolchinClosure {ι' : Type*}
    (translation : (ι → K) → DifferentialAlgEquiv K L) (S : ι' → Set (ι → K))
    (hclosed : ∀ z : L,
      IsKolchinClosedOver K {a : ι → K | (translation a).toAlgEquiv z = z}) :
    (⨅ n, differentialTranslationFixedField translation (S n))
      = differentialTranslationFixedField translation
          (kolchinClosureOver K (⋃ n, S n)) :=
  le_antisymm (iInf_le_differentialTranslationFixedField_kolchinClosure translation S hclosed)
    (differentialTranslationFixedField_kolchinClosure_le_iInf translation S hclosed)


/-! ### The stabilizer of a subfield -/

/-- The set of labels whose translation fixes a given set of field elements pointwise. -/
def translationStabilizerSet (translation : A → DifferentialAlgEquiv K L) (E : Set L) : Set A :=
  {a : A | ∀ z ∈ E, (translation a).toAlgEquiv z = z}

omit [Differential K] in
theorem mem_translationStabilizerSet_iff {translation : A → DifferentialAlgEquiv K L} {E : Set L}
    {a : A} :
    a ∈ translationStabilizerSet translation E ↔ ∀ z ∈ E, (translation a).toAlgEquiv z = z :=
  Iff.rfl

omit [Differential K] in
/-- Stabilizing more elements is a stronger condition. -/
theorem translationStabilizerSet_antitone (translation : A → DifferentialAlgEquiv K L)
    {E E' : Set L} (hEE : E ⊆ E') :
    translationStabilizerSet translation E' ⊆ translationStabilizerSet translation E :=
  fun _ ha z hz => ha z (hEE hz)

/-- **The stabilizer of a subfield is Kolchin closed.**  It is the intersection of the individual
element stabilizers, and Kolchin-closed sets are closed under arbitrary intersections. -/
theorem isKolchinClosedOver_translationStabilizerSet
    (translation : (ι → K) → DifferentialAlgEquiv K L) (E : Set L)
    (hclosed : ∀ z : L,
      IsKolchinClosedOver K {a : ι → K | (translation a).toAlgEquiv z = z}) :
    IsKolchinClosedOver K (translationStabilizerSet translation E) := by
  classical
  have hrw : translationStabilizerSet translation E
      = ⋂₀ {X : Set (ι → K) | ∃ z ∈ E, X = {a | (translation a).toAlgEquiv z = z}} := by
    ext a
    simp only [mem_translationStabilizerSet_iff, Set.mem_sInter, Set.mem_setOf_eq]
    constructor
    · rintro ha X ⟨z, hz, rfl⟩
      exact ha z hz
    · intro ha z hz
      exact ha {a | (translation a).toAlgEquiv z = z} ⟨z, hz, rfl⟩
  rw [hrw]
  refine isKolchinClosedOver_sInter _ ?_
  rintro X ⟨z, -, rfl⟩
  exact hclosed z

/-- **The Kolchin closure of a label set stabilizes its own fixed field.** -/
theorem kolchinClosureOver_subset_translationStabilizerSet
    (translation : (ι → K) → DifferentialAlgEquiv K L) (S : Set (ι → K))
    (hclosed : ∀ z : L,
      IsKolchinClosedOver K {a : ι → K | (translation a).toAlgEquiv z = z}) :
    kolchinClosureOver K S
      ⊆ translationStabilizerSet translation
          ((differentialTranslationFixedField translation S : IntermediateField K L) : Set L) := by
  refine kolchinClosureOver_minimal (fun a ha z hz => hz a ha)
    (isKolchinClosedOver_translationStabilizerSet translation _ hclosed)

/-- **The tail is stabilized by the Kolchin closure of all its labels.**  This is the inclusion half
of the identification of the tail stabilizer with the closure of the deck group. -/
theorem kolchinClosureOver_iUnion_subset_translationStabilizerSet_tail {ι' : Type*}
    (translation : (ι → K) → DifferentialAlgEquiv K L) (S : ι' → Set (ι → K))
    (hclosed : ∀ z : L,
      IsKolchinClosedOver K {a : ι → K | (translation a).toAlgEquiv z = z}) :
    kolchinClosureOver K (⋃ n, S n)
      ⊆ translationStabilizerSet translation
          ((⨅ n, differentialTranslationFixedField translation (S n) :
            IntermediateField K L) : Set L) := by
  intro a ha z hz
  have hz' : z ∈ differentialTranslationFixedField translation
      (kolchinClosureOver K (⋃ n, S n)) := by
    rw [← iInf_differentialTranslationFixedField_eq_kolchinClosure translation S hclosed]
    exact hz
  exact hz' a ha

/-- The exact identification, once the reverse inclusion is available: the stabilizer of the tail is
the Kolchin closure of all its labels. -/
theorem translationStabilizerSet_tail_eq_kolchinClosureOver {ι' : Type*}
    (translation : (ι → K) → DifferentialAlgEquiv K L) (S : ι' → Set (ι → K))
    (hclosed : ∀ z : L,
      IsKolchinClosedOver K {a : ι → K | (translation a).toAlgEquiv z = z})
    (hgalois : translationStabilizerSet translation
        ((⨅ n, differentialTranslationFixedField translation (S n) :
          IntermediateField K L) : Set L)
      ⊆ kolchinClosureOver K (⋃ n, S n)) :
    translationStabilizerSet translation
        ((⨅ n, differentialTranslationFixedField translation (S n) :
          IntermediateField K L) : Set L)
      = kolchinClosureOver K (⋃ n, S n) :=
  le_antisymm hgalois
    (kolchinClosureOver_iUnion_subset_translationStabilizerSet_tail translation S hclosed)

end

end GaloisForLFunctions.HTGeometry
