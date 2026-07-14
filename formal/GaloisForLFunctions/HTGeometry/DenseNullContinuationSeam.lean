import Mathlib.MeasureTheory.Measure.Regular

namespace GaloisForLFunctions

open MeasureTheory Set

/-- Functions differing from a base point at only finitely many coordinates. -/
def finiteModification
    {I : Type*} (A : I → Type*) (base : ∀ i, A i) : Set (∀ i, A i) :=
  {f | {i | f i ≠ base i}.Finite}

/-- Finite modifications of any base point are dense in an arbitrary product topology. -/
theorem dense_finiteModification
    {I : Type*} {A : I → Type*} [∀ i, TopologicalSpace (A i)]
    (base : ∀ i, A i) :
    Dense (finiteModification A base) := by
  rw [dense_iff_inter_open]
  intro U hU
  rintro ⟨g, hg⟩
  rcases isOpen_pi_iff.mp hU g hg with ⟨J, V, hV, hVU⟩
  classical
  let f : ∀ i, A i := fun i => if hi : i ∈ J then g i else base i
  refine ⟨f, hVU ?_, ?_⟩
  · intro i hi
    have hiJ : i ∈ J := Finset.mem_coe.mp hi
    simpa only [f, dif_pos hiJ] using (hV i hiJ).2
  · show {i | f i ≠ base i}.Finite
    apply J.finite_toSet.subset
    intro i hi
    by_contra hiJ
    have hiJ' : i ∉ J := by simpa using hiJ
    exact hi (by simp [f, hiJ'])

/-- A null set has dense complement when every nonempty open set has positive measure. -/
theorem dense_compl_of_measure_zero_of_open_pos
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] (mu : Measure X) {S : Set X}
    (hSzero : mu S = 0)
    (hopen : forall U : Set X, IsOpen U -> U.Nonempty -> mu U ≠ 0) :
    Dense S.compl := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  by_contra hEmpty
  have hUS : U ⊆ S := by
    intro x hxU
    by_contra hxS
    exact hEmpty ⟨x, hxU, hxS⟩
  exact hopen U hU hUne (measure_mono_null hUS hSzero)

/-- A set and its complement are both dense exactly when its frontier is the whole space. -/
theorem frontier_eq_univ_of_dense_and_dense_compl
    {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : Dense S) (hSc : Dense Sᶜ) :
    frontier S = Set.univ := by
  have hSclosure : closure S = Set.univ := dense_iff_closure_eq.mp hS
  have hScclosure : closure Sᶜ = Set.univ := dense_iff_closure_eq.mp hSc
  rw [frontier_eq_closure_inter_closure, hSclosure, hScclosure]
  exact Set.univ_inter Set.univ

/-- On a dense/codense seam, every neighborhood contains points on both sides. -/
theorem every_open_neighborhood_meets_both_sides
    {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : Dense S) (hSc : Dense S.compl)
    (x : X) (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
    (U ∩ S).Nonempty ∧ (U ∩ S.compl).Nonempty := by
  constructor
  · exact (dense_iff_inter_open.mp hS) U hU ⟨x, hxU⟩
  · exact (dense_iff_inter_open.mp hSc) U hU ⟨x, hxU⟩

/-- The Boolean side indicator of a dense/codense seam. -/
noncomputable def seamIndicator {X : Type*} (S : Set X) (x : X) : Bool := by
  classical
  exact if x ∈ S then true else false

/-- The side of a dense/codense seam cannot be decided continuously at any point. -/
theorem nowhereContinuous_seamIndicator
    {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : Dense S) (hSc : Dense S.compl) :
    ∀ x : X, ¬ ContinuousAt (seamIndicator S) x := by
  classical
  intro x hx
  have hpre :
      seamIndicator S ⁻¹' ({seamIndicator S x} : Set Bool) ∈ nhds x := by
    apply hx
    exact (isOpen_discrete _).mem_nhds (by simp)
  rcases mem_nhds_iff.mp hpre with ⟨U, hUsub, hUopen, hxU⟩
  by_cases hxS : x ∈ S
  · rcases (dense_iff_inter_open.mp hSc) U hUopen ⟨x, hxU⟩ with ⟨z, hzU, hzSc⟩
    have hzpre := hUsub hzU
    have hzS : z ∈ S := by simpa [seamIndicator, hxS] using hzpre
    exact hzSc hzS
  · rcases (dense_iff_inter_open.mp hS) U hUopen ⟨x, hxU⟩ with ⟨z, hzU, hzS⟩
    have hzpre := hUsub hzU
    have hzSc : z ∉ S := by simpa [seamIndicator, hxS] using hzpre
    exact hzSc hzS

/-- No pair of continuous readouts can factor the side indicator of a nonempty
dense/codense seam. -/
theorem no_continuous_factorization_seamIndicator
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    {S : Set X} (hS : Dense S) (hSc : Dense S.compl)
    (q : X → Y) (c : Y → Bool) (hq : Continuous q) (hc : Continuous c) :
    seamIndicator S ≠ c ∘ q := by
  intro heq
  have hcontinuous : Continuous (seamIndicator S) := by
    rw [heq]
    exact hc.comp hq
  exact nowhereContinuous_seamIndicator hS hSc (Classical.choice inferInstance)
    hcontinuous.continuousAt

/-- A surjective readout from a closed seam in a compact carrier to a noncompact target
cannot be continuous. -/
theorem not_isClosed_or_not_continuous_of_surjective_to_noncompact
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    {S : Set X} (f : S → Y) (hf : Function.Surjective f)
    (hY : ¬ IsCompact (Set.univ : Set Y)) :
    ¬ IsClosed S ∨ ¬ Continuous f := by
  by_contra h
  push Not at h
  rcases h with ⟨hSclosed, hfcont⟩
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hSclosed.isCompact
  have hrange : IsCompact (Set.range f) := by
    simpa only [Set.image_univ] using isCompact_univ.image hfcont
  have hrange_eq : Set.range f = Set.univ := Set.range_eq_univ.mpr hf
  exact hY (hrange_eq ▸ hrange)

end GaloisForLFunctions
