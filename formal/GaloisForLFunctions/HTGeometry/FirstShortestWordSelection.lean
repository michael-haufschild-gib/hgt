import GaloisForLFunctions.HTGeometry.GateRateDistortion

/-!
# The first shortest qualifying word is a measurable encoder

Order the words of a countable alphabet by length and then by their encoding.  For a request state
the qualifying words are those whose endpoint lies within the tolerance, and the encoder selects
the first of them in that order.  Its fibre over a word is the closed tube of that word minus the
countable union of all earlier tubes, hence Borel; the encoder is therefore a measurable
deterministic map into the discrete word space, and its length is exactly the robust word
complexity — with both equal to zero when nothing qualifies.
-/

open Function
open scoped Classical

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Order

variable {Γ : Type*} [Encodable Γ]

/-- Shortlex key of a word: length first, then its encoding. -/
def wordKey (w : List Γ) : ℕ ×ₗ ℕ := toLex (w.length, Encodable.encode w)

theorem wordKey_injective : Function.Injective (wordKey (Γ := Γ)) := by
  intro v w h
  have h2 : Encodable.encode v = Encodable.encode w :=
    congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).2) h
  exact Encodable.encode_injective h2

theorem length_le_of_wordKey_le {v w : List Γ} (h : wordKey v ≤ wordKey w) :
    v.length ≤ w.length := by
  rcases Prod.Lex.le_iff.mp h with hlt | heq
  · exact le_of_lt hlt
  · exact le_of_eq heq.1

end Order

section Pure

variable {Γ : Type*} [Encodable Γ]
variable {X : Type*} [MetricSpace X]

/-- A word whose endpoint is within `eps` of the requested state. -/
def Qualifies (endpoint : List Γ → X) (eps : ℝ) (x : X) (w : List Γ) : Prop :=
  dist (endpoint w) x ≤ eps

/-- **The first shortest qualifying word.**  Words are ordered by length and then by their
encoding, so the minimiser is canonical. -/
def firstQualifying (endpoint : List Γ → X) (eps : ℝ) (x : X) : List Γ :=
  if h : ∃ w, Qualifies endpoint eps x w then
    haveI : Nonempty {w : List Γ // Qualifies endpoint eps x w} := nonempty_subtype.mpr h
    (Function.argmin (fun w : {w : List Γ // Qualifies endpoint eps x w} => wordKey w.1)).1
  else []

theorem firstQualifying_qualifies {endpoint : List Γ → X} {eps : ℝ} {x : X}
    (h : ∃ w, Qualifies endpoint eps x w) :
    Qualifies endpoint eps x (firstQualifying endpoint eps x) := by
  unfold firstQualifying
  rw [dif_pos h]
  haveI : Nonempty {w : List Γ // Qualifies endpoint eps x w} := nonempty_subtype.mpr h
  exact (Function.argmin (fun w : {w : List Γ // Qualifies endpoint eps x w} => wordKey w.1)).2

theorem wordKey_firstQualifying_le {endpoint : List Γ → X} {eps : ℝ} {x : X}
    (h : ∃ w, Qualifies endpoint eps x w) {v : List Γ} (hv : Qualifies endpoint eps x v) :
    wordKey (firstQualifying endpoint eps x) ≤ wordKey v := by
  unfold firstQualifying
  rw [dif_pos h]
  haveI : Nonempty {w : List Γ // Qualifies endpoint eps x w} := nonempty_subtype.mpr h
  exact le_of_not_gt
    (Function.not_lt_argmin
      (fun w : {w : List Γ // Qualifies endpoint eps x w} => wordKey w.1) ⟨v, hv⟩)

theorem firstQualifying_eq_nil_of_not_exists {endpoint : List Γ → X} {eps : ℝ} {x : X}
    (h : ¬ ∃ w, Qualifies endpoint eps x w) : firstQualifying endpoint eps x = [] := by
  unfold firstQualifying
  rw [dif_neg h]

/-- The selection cell of a word: its closed tube minus every earlier qualifying tube. -/
def selectionCell (endpoint : List Γ → X) (eps : ℝ) (w : List Γ) : Set X :=
  {x | dist (endpoint w) x ≤ eps} \
    ⋃ v ∈ {v : List Γ | wordKey v < wordKey w}, {x | dist (endpoint v) x ≤ eps}

theorem mem_selectionCell_iff {endpoint : List Γ → X} {eps : ℝ} {w : List Γ} {x : X} :
    x ∈ selectionCell endpoint eps w ↔
      Qualifies endpoint eps x w ∧ ∀ v, Qualifies endpoint eps x v → wordKey w ≤ wordKey v := by
  unfold selectionCell Qualifies
  constructor
  · rintro ⟨hw, hno⟩
    refine ⟨hw, fun v hv => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hno (Set.mem_biUnion (by exact hlt) hv)
  · rintro ⟨hw, hmin⟩
    refine ⟨hw, ?_⟩
    intro hmem
    obtain ⟨v, hv, hvx⟩ := Set.mem_iUnion₂.mp hmem
    exact absurd (hmin v hvx) (not_le_of_gt hv)

/-- **The selection is exactly the cell decomposition.** -/
theorem firstQualifying_eq_iff_mem_selectionCell {endpoint : List Γ → X} {eps : ℝ} {x : X}
    (h : ∃ w, Qualifies endpoint eps x w) (w : List Γ) :
    firstQualifying endpoint eps x = w ↔ x ∈ selectionCell endpoint eps w := by
  constructor
  · rintro rfl
    exact mem_selectionCell_iff.mpr
      ⟨firstQualifying_qualifies h, fun v hv => wordKey_firstQualifying_le h hv⟩
  · intro hx
    obtain ⟨hw, hmin⟩ := mem_selectionCell_iff.mp hx
    apply wordKey_injective
    exact le_antisymm (wordKey_firstQualifying_le h hw) (hmin _ (firstQualifying_qualifies h))

/-- Robust word complexity: the least length of a qualifying word. -/
def wordComplexity (endpoint : List Γ → X) (eps : ℝ) (x : X) : ℕ :=
  sInf {l : ℕ | ∃ w : List Γ, w.length = l ∧ Qualifies endpoint eps x w}

/-- **The length identity.**  The selected word has exactly the robust complexity as its length,
with both equal to zero when nothing qualifies. -/
theorem wordComplexity_eq_length_firstQualifying (endpoint : List Γ → X) (eps : ℝ) (x : X) :
    wordComplexity endpoint eps x = (firstQualifying endpoint eps x).length := by
  by_cases h : ∃ w, Qualifies endpoint eps x w
  · have hmem : (firstQualifying endpoint eps x).length ∈
        {l : ℕ | ∃ w : List Γ, w.length = l ∧ Qualifies endpoint eps x w} :=
      ⟨_, rfl, firstQualifying_qualifies h⟩
    refine le_antisymm (Nat.sInf_le hmem) ?_
    obtain ⟨w0, hw0⟩ := h
    have hne : {l : ℕ | ∃ w : List Γ, w.length = l ∧ Qualifies endpoint eps x w}.Nonempty :=
      ⟨w0.length, w0, rfl, hw0⟩
    obtain ⟨v, hvlen, hv⟩ := Nat.sInf_mem hne
    calc (firstQualifying endpoint eps x).length ≤ v.length :=
          length_le_of_wordKey_le (wordKey_firstQualifying_le ⟨w0, hw0⟩ hv)
      _ = _ := hvlen
  · rw [firstQualifying_eq_nil_of_not_exists h]
    unfold wordComplexity
    have hempty : {l : ℕ | ∃ w : List Γ, w.length = l ∧ Qualifies endpoint eps x w} = ∅ := by
      ext l
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨w, _, hw⟩
      exact h ⟨w, hw⟩
    rw [hempty]
    simp

end Pure

section Measurability

variable {Γ : Type*} [Encodable Γ]
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [Encodable Γ] in
theorem measurableSet_tube (endpoint : List Γ → X) (eps : ℝ) (w : List Γ) :
    MeasurableSet {x : X | dist (endpoint w) x ≤ eps} :=
  measurableSet_le (by fun_prop) measurable_const

theorem measurableSet_selectionCell (endpoint : List Γ → X) (eps : ℝ) (w : List Γ) :
    MeasurableSet (selectionCell endpoint eps w) := by
  unfold selectionCell
  refine (measurableSet_tube endpoint eps w).diff ?_
  refine MeasurableSet.biUnion ?_ fun v _ => measurableSet_tube endpoint eps v
  exact Set.to_countable _

theorem measurableSet_noQualifier (endpoint : List Γ → X) (eps : ℝ) :
    MeasurableSet {x : X | ¬ ∃ w, Qualifies endpoint eps x w} := by
  have hcompl : {x : X | ¬ ∃ w, Qualifies endpoint eps x w} =
      (⋃ w : List Γ, {x : X | dist (endpoint w) x ≤ eps})ᶜ := by
    ext x
    simp [Qualifies]
  rw [hcompl]
  exact (MeasurableSet.iUnion fun w => measurableSet_tube endpoint eps w).compl

omit [MeasurableSpace X] [BorelSpace X] in
theorem preimage_firstQualifying (endpoint : List Γ → X) (eps : ℝ) (w : List Γ) :
    firstQualifying endpoint eps ⁻¹' {w} =
      selectionCell endpoint eps w ∪
        (if w = [] then {x : X | ¬ ∃ v, Qualifies endpoint eps x v} else ∅) := by
  ext x
  by_cases h : ∃ v, Qualifies endpoint eps x v
  · have hcell := firstQualifying_eq_iff_mem_selectionCell h w
    constructor
    · intro hx
      exact Or.inl (hcell.mp hx)
    · rintro (hx | hx)
      · exact hcell.mpr hx
      · split_ifs at hx with hw
        · exact absurd h hx
        · exact absurd hx (Set.notMem_empty x)
  · have hnil := firstQualifying_eq_nil_of_not_exists h
    constructor
    · intro hx
      have hw : w = [] := by
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
        rw [← hx, hnil]
      refine Or.inr ?_
      rw [if_pos hw]
      exact h
    · rintro (hx | hx)
      · exact absurd ⟨w, (mem_selectionCell_iff.mp hx).1⟩ h
      · split_ifs at hx with hw
        · rw [Set.mem_preimage, Set.mem_singleton_iff, hnil, hw]
        · exact absurd hx (Set.notMem_empty x)

/-- **Theorem B, the measurable selection.**  Every fibre of the first-shortest-word encoder is
Borel. -/
theorem measurableSet_preimage_firstQualifying (endpoint : List Γ → X) (eps : ℝ) (w : List Γ) :
    MeasurableSet (firstQualifying endpoint eps ⁻¹' {w}) := by
  rw [preimage_firstQualifying]
  refine (measurableSet_selectionCell endpoint eps w).union ?_
  split_ifs
  · exact measurableSet_noQualifier endpoint eps
  · exact MeasurableSet.empty

/-- The first-shortest-word encoder is measurable into the discrete word space. -/
theorem measurable_firstQualifying [MeasurableSpace (List Γ)]
    [MeasurableSingletonClass (List Γ)] (endpoint : List Γ → X) (eps : ℝ) :
    Measurable (firstQualifying endpoint eps) :=
  measurable_to_countable' fun w => measurableSet_preimage_firstQualifying endpoint eps w

/-- Hence the robust word complexity is measurable. -/
theorem measurable_wordComplexity (endpoint : List Γ → X) (eps : ℝ) :
    Measurable (wordComplexity endpoint eps) := by
  refine measurable_to_countable' fun n => ?_
  have hset : wordComplexity endpoint eps ⁻¹' {n} =
      ⋃ w ∈ {w : List Γ | w.length = n}, firstQualifying endpoint eps ⁻¹' {w} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_setOf_eq,
      exists_prop]
    rw [wordComplexity_eq_length_firstQualifying]
    constructor
    · intro hx
      exact ⟨firstQualifying endpoint eps x, hx, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact hw
  rw [hset]
  refine MeasurableSet.biUnion (Set.to_countable _) fun w _ => ?_
  exact measurableSet_preimage_firstQualifying endpoint eps w

end Measurability

end

end GaloisForLFunctions.HTGeometry
