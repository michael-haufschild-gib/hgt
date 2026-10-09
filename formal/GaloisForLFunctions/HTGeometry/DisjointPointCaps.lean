import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Topological completion by disjoint point caps

Attach one point to each disjoint open region modeled on a punctured space.
The final topology makes the old inclusion and every full cap open embeddings.
A continuous projection distinguishing old points from cap centers ensures
Hausdorffness; countably many caps preserve second countability.
-/

open Topology Set Function

namespace GaloisForLFunctions.HTGeometry

/-- Disjoint open regions identified with a punctured cap model. -/
structure PointCapData (Y D I : Type*) [TopologicalSpace Y] [TopologicalSpace D] where
  center : D
  region : I → Set Y
  isOpen_region : ∀ i, IsOpen (region i)
  disjoint_region : Pairwise (Disjoint on region)
  chart : ∀ i, {z : D // z ≠ center} ≃ₜ region i

namespace PointCapData

variable {Y D I : Type*} [TopologicalSpace Y] [TopologicalSpace D]

/-- Add one center to each punctured region. -/
def Space (_c : PointCapData Y D I) := Y ⊕ I

variable (c : PointCapData Y D I)

def old : Y → c.Space := Sum.inl

def point : I → c.Space := Sum.inr

noncomputable def cap (i : I) (z : D) : c.Space := by
  classical
  exact if h : z = c.center then c.point i else c.old (c.chart i ⟨z, h⟩)

@[simp] theorem cap_center (i : I) : c.cap i c.center = c.point i := by
  classical
  simp [cap]

theorem cap_ne_center (i : I) {z : D} (hz : z ≠ c.center) :
    c.cap i z = c.old (c.chart i ⟨z, hz⟩) := by
  classical
  simp [cap, hz]

theorem old_injective : Injective c.old := Sum.inl_injective

theorem cap_injective (i : I) : Injective (c.cap i) := by
  classical
  intro z w h
  by_cases hz : z = c.center
  · subst z
    by_cases hw : w = c.center
    · exact hw.symm
    · simp [cap_ne_center _ _ hw, cap_center, old, point] at h
  · by_cases hw : w = c.center
    · subst w
      simp [cap_ne_center _ _ hz, cap_center, old, point] at h
    · have he : c.chart i ⟨z, hz⟩ = c.chart i ⟨w, hw⟩ := by
        apply Subtype.ext
        exact c.old_injective (by simpa only [cap_ne_center _ _ hz, cap_ne_center _ _ hw] using h)
      exact congrArg Subtype.val ((c.chart i).injective he)

/-- The final topology for the old inclusion and every full cap chart. -/
instance spaceTopology : TopologicalSpace c.Space where
  IsOpen S := IsOpen (c.old ⁻¹' S) ∧ ∀ i, IsOpen (c.cap i ⁻¹' S)
  isOpen_univ := by simp
  isOpen_inter S T hS hT := ⟨hS.1.inter hT.1, fun i => (hS.2 i).inter (hT.2 i)⟩
  isOpen_sUnion S hS := by
    constructor
    · rw [preimage_sUnion]
      exact isOpen_biUnion fun s hs => (hS s hs).1
    · intro i
      rw [preimage_sUnion]
      exact isOpen_biUnion fun s hs => (hS s hs).2 i

theorem isOpen_iff (S : Set c.Space) :
    IsOpen S ↔ IsOpen (c.old ⁻¹' S) ∧ ∀ i, IsOpen (c.cap i ⁻¹' S) := Iff.rfl

theorem continuous_old : Continuous c.old := continuous_def.mpr fun _ hS => hS.1

theorem continuous_cap (i : I) : Continuous (c.cap i) := continuous_def.mpr fun _ hS => hS.2 i

/-- A map on the completion is continuous exactly when it is continuous in all pieces. -/
theorem continuous_iff [TopologicalSpace Z] (f : c.Space → Z) :
    Continuous f ↔ Continuous (f ∘ c.old) ∧ ∀ i, Continuous (f ∘ c.cap i) := by
  constructor
  · intro hf
    exact ⟨hf.comp c.continuous_old, fun i => hf.comp (c.continuous_cap i)⟩
  · rintro ⟨ho, hc⟩
    apply continuous_def.mpr
    intro S hS
    exact ⟨hS.preimage ho, fun i => hS.preimage (hc i)⟩

theorem old_preimage_cap_image (i : I) (S : Set D) :
    c.old ⁻¹' (c.cap i '' S) =
      Subtype.val '' (c.chart i '' (Subtype.val ⁻¹' S)) := by
  classical
  ext y
  constructor
  · rintro ⟨z, hz, heq⟩
    by_cases hzc : z = c.center
    · subst z
      simp [old, point] at heq
    · refine ⟨c.chart i ⟨z, hzc⟩, ⟨⟨z, hzc⟩, hz, rfl⟩, ?_⟩
      exact c.old_injective ((c.cap_ne_center i hzc).symm.trans heq)
  · rintro ⟨u, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, c.cap_ne_center i z.property⟩

theorem cap_preimage_old_image (i : I) (S : Set Y) :
    c.cap i ⁻¹' (c.old '' S) =
      Subtype.val '' ((c.chart i) ⁻¹' (Subtype.val ⁻¹' S)) := by
  classical
  ext z
  constructor
  · rintro ⟨y, hy, heq⟩
    by_cases hzc : z = c.center
    · subst z
      simp [old, point] at heq
    · refine ⟨⟨z, hzc⟩, ?_, rfl⟩
      have h := c.old_injective (heq.trans (c.cap_ne_center i hzc))
      change (c.chart i ⟨z, hzc⟩ : Y) ∈ S
      rw [← h]
      exact hy
  · rintro ⟨w, hw, rfl⟩
    exact ⟨c.chart i w, hw, (c.cap_ne_center i w.property).symm⟩

theorem disjoint_cap_ranges : Pairwise (Disjoint on fun i => range (c.cap i)) := by
  classical
  intro i j hij
  rw [onFun, disjoint_left]
  rintro x ⟨z, rfl⟩ ⟨w, heq⟩
  by_cases hz : z = c.center
  · subst z
    by_cases hw : w = c.center
    · subst w
      rw [cap_center, cap_center] at heq
      change (Sum.inr j : Y ⊕ I) = Sum.inr i at heq
      exact hij (Sum.inr_injective heq.symm)
    · simp [cap_ne_center _ _ hw, cap_center, old, point] at heq
  · by_cases hw : w = c.center
    · subst w
      simp [cap_ne_center _ _ hz, cap_center, old, point] at heq
    · have hv : (c.chart j ⟨w, hw⟩ : Y) = c.chart i ⟨z, hz⟩ :=
        c.old_injective (by simpa only [cap_ne_center _ _ hw, cap_ne_center _ _ hz] using heq)
      exact (disjoint_left.mp (c.disjoint_region hij)) (c.chart i ⟨z, hz⟩).property
        (hv ▸ (c.chart j ⟨w, hw⟩).property)

theorem isOpenMap_cap (i : I) : IsOpenMap (c.cap i) := by
  intro S hS
  constructor
  · rw [c.old_preimage_cap_image]
    exact (c.isOpen_region i).isOpenMap_subtype_val _
      ((c.chart i).isOpenMap _ (hS.preimage continuous_subtype_val))
  · intro j
    by_cases hji : j = i
    · subst j
      simpa only [preimage_image_eq _ (c.cap_injective i)] using hS
    · have he : c.cap j ⁻¹' (c.cap i '' S) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro z ⟨w, _, hw⟩
        exact (disjoint_left.mp (c.disjoint_cap_ranges hji)) (mem_range_self z) ⟨w, hw⟩
      rw [he]
      exact isOpen_empty

theorem isOpenEmbedding_cap (i : I) : IsOpenEmbedding (c.cap i) :=
  .of_continuous_injective_isOpenMap (c.continuous_cap i)
    (c.cap_injective i) (c.isOpenMap_cap i)

theorem isOpenMap_old [T1Space D] : IsOpenMap c.old := by
  intro S hS
  constructor
  · simpa only [preimage_image_eq _ c.old_injective] using hS
  · intro i
    rw [c.cap_preimage_old_image]
    exact (isOpen_ne : IsOpen {z : D | z ≠ c.center}).isOpenMap_subtype_val _
      ((hS.preimage continuous_subtype_val).preimage (c.chart i).continuous)

theorem isOpenEmbedding_old [T1Space D] : IsOpenEmbedding c.old :=
  .of_continuous_injective_isOpenMap c.continuous_old c.old_injective c.isOpenMap_old

theorem pieces_cover : range c.old ∪ ⋃ i, range (c.cap i) = univ := by
  apply eq_univ_iff_forall.mpr
  intro x
  cases x with
  | inl y => exact Or.inl ⟨y, rfl⟩
  | inr i => exact Or.inr (mem_iUnion.mpr ⟨i, ⟨c.center, c.cap_center i⟩⟩)

def extend (p : Y → Z) (b : I → Z) : c.Space → Z := fun x => Sum.elim p b x

/-- The extended projection is continuous once its cap coordinate functions are continuous. -/
theorem continuous_extend [TopologicalSpace Z] (p : Y → Z) (b : I → Z)
    (hp : Continuous p) (hc : ∀ i, Continuous (c.extend p b ∘ c.cap i)) :
    Continuous (c.extend p b) :=
  (c.continuous_iff _).mpr ⟨hp, hc⟩

/-- A continuous projection separating every old point from every new center
ensures that the cap completion is Hausdorff. -/
theorem t2Space_of_projection [T1Space D] [T2Space Y] [TopologicalSpace Z] [T2Space Z]
    (p : Y → Z) (b : I → Z) (hp : Continuous p)
    (hc : ∀ i, Continuous (c.extend p b ∘ c.cap i))
    (havoid : ∀ y i, p y ≠ b i) : T2Space c.Space := by
  have hf := c.continuous_extend p b hp hc
  have hsep : ∀ x y : c.Space, c.extend p b x ≠ c.extend p b y →
      ∃ U V, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V := by
    intro x y hxy
    obtain ⟨U, V, hU, hV, hx, hy, hd⟩ := t2_separation hxy
    exact ⟨_, _, hU.preimage hf, hV.preimage hf, hx, hy, hd.preimage _⟩
  refine ⟨fun x y hxy => ?_⟩
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      obtain ⟨U, V, hU, hV, hx, hy, hd⟩ :=
        t2_separation (show x ≠ y from fun h => hxy (congrArg c.old h))
      exact ⟨c.old '' U, c.old '' V, c.isOpenMap_old _ hU, c.isOpenMap_old _ hV,
        mem_image_of_mem _ hx, mem_image_of_mem _ hy,
        disjoint_image_of_injective c.old_injective hd⟩
    | inr i => exact hsep _ _ (havoid x i)
  | inr i =>
    cases y with
    | inl y => exact hsep _ _ (havoid y i).symm
    | inr j =>
      have hij : i ≠ j := fun h => hxy (congrArg c.point h)
      exact ⟨range (c.cap i), range (c.cap j),
        (c.isOpenEmbedding_cap i).isOpen_range, (c.isOpenEmbedding_cap j).isOpen_range,
        ⟨c.center, c.cap_center i⟩, ⟨c.center, c.cap_center j⟩, c.disjoint_cap_ranges hij⟩

/-- Countably many cap charts preserve second countability. -/
theorem secondCountableTopology [T1Space D] [SecondCountableTopology Y]
    [SecondCountableTopology D] [Countable I] : SecondCountableTopology c.Space := by
  let U : Option I → Set c.Space := fun i =>
    match i with
    | none => range c.old
    | some i => range (c.cap i)
  letI : ∀ i, SecondCountableTopology (U i) := by
    intro i
    cases i with
    | none => exact c.isOpenEmbedding_old.isEmbedding.toHomeomorph.symm.secondCountableTopology
    | some i => exact (c.isOpenEmbedding_cap i).isEmbedding.toHomeomorph.symm.secondCountableTopology
  apply TopologicalSpace.secondCountableTopology_of_countable_cover (U := U)
  · intro i
    cases i with
    | none => exact c.isOpenEmbedding_old.isOpen_range
    | some i => exact (c.isOpenEmbedding_cap i).isOpen_range
  · apply eq_univ_iff_forall.mpr
    intro x
    have hx : x ∈ range c.old ∪ ⋃ i, range (c.cap i) := by rw [c.pieces_cover]; trivial
    rcases hx with hx | hx
    · exact mem_iUnion.mpr ⟨none, hx⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨some i, hi⟩

end PointCapData
end GaloisForLFunctions.HTGeometry
