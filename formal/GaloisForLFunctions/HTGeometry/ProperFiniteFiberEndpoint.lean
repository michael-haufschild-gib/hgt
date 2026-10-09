import GaloisForLFunctions.Bottcher.ProperLocalHomeoCovering
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Endpoints under proper maps with finite fibers

A preconnected filter basis selects one of the disjoint neighborhoods of a finite
limiting fiber. Properness makes every subordinate ultrafilter converge in that fiber,
so all select the same limit. Continuous interval curves inherit this endpoint property.
-/

open Set Filter Topology
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- A convergent image under a proper map with finite limiting fiber forces convergence of
any nontrivial filter with a preconnected basis. -/
theorem exists_limit_of_proper_finite_fiber_connected_basis
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    {f : X → Y} (hf : IsProperMap f) {F : Filter X} [NeBot F]
    {ι : Type*} {p : ι → Prop} {s : ι → Set X} (hbasis : F.HasBasis p s)
    (hconn : ∀ i, p i → IsPreconnected (s i)) {y : Y}
    (hlim : Tendsto f F (𝓝 y)) (hfin : (f ⁻¹' {y}).Finite) :
    ∃ x, f x = y ∧ F ≤ 𝓝 x := by
  classical
  let S := hfin.toFinset
  obtain ⟨O, hO, hdisj⟩ := exists_pairwise_disjoint_nhds S
  have hcover : f ⁻¹' {y} ⊆ ⋃ a ∈ S, O a := by
    intro a ha
    have haS : a ∈ S := hfin.mem_toFinset.mpr ha
    exact mem_iUnion₂.mpr ⟨a, haS, (hO a haS).2⟩
  have hopen : IsOpen (⋃ a ∈ S, O a) := isOpen_biUnion fun a ha => (hO a ha).1
  obtain ⟨W, hW, hpre⟩ := Bottcher.exists_nhds_preimage_subset hf.isClosedMap hopen hcover
  have hmem : (⋃ a ∈ S, O a) ∈ F := mem_of_superset (hlim hW) hpre
  obtain ⟨i, hi, hsub⟩ := hbasis.mem_iff.mp hmem
  obtain ⟨z, hz⟩ := Filter.nonempty_of_mem (hbasis.mem_of_mem hi)
  obtain ⟨a, haS, hza⟩ := mem_iUnion₂.mp (hsub hz)
  let V : Set X := ⋃ b ∈ S.erase a, O b
  have hVopen : IsOpen V := isOpen_biUnion fun b hb => (hO b (Finset.mem_of_mem_erase hb)).1
  have hOV : Disjoint (O a) V := by
    apply disjoint_iUnion_right.mpr
    intro b
    apply disjoint_iUnion_right.mpr
    intro hb
    exact hdisj haS (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm
  have hsOV : s i ⊆ O a ∪ V := by
    intro w hw
    obtain ⟨b, hbS, hwb⟩ := mem_iUnion₂.mp (hsub hw)
    by_cases hba : b = a
    · exact Or.inl (hba ▸ hwb)
    · exact Or.inr (mem_iUnion₂.mpr ⟨b, Finset.mem_erase.mpr ⟨hba, hbS⟩, hwb⟩)
  have hsO : s i ⊆ O a := (hconn i hi).subset_left_of_subset_union
    (hO a haS).1 hVopen hOV hsOV ⟨z, hz, hza⟩
  have hOF : O a ∈ F := mem_of_superset (hbasis.mem_of_mem hi) hsO
  refine ⟨a, hfin.mem_toFinset.mp haS, ?_⟩
  apply le_iff_ultrafilter.mpr
  intro U hUF
  obtain ⟨b, hfb, hUb⟩ := hf.ultrafilter_le_nhds_of_tendsto (hlim.mono_left hUF)
  have hbS : b ∈ S := hfin.mem_toFinset.mpr hfb
  have hba : b = a := by
    by_contra hba
    have hUa : O a ∈ (U : Filter X) := hUF hOF
    have hUb' : O b ∈ (U : Filter X) := hUb ((hO b hbS).1.mem_nhds (hO b hbS).2)
    obtain ⟨w, hwa, hwb⟩ := Filter.nonempty_of_mem (inter_mem hUa hUb')
    exact Set.disjoint_left.mp (hdisj haS hbS (fun hab => hba hab.symm)) hwa hwb
  simpa only [hba] using hUb

/-- A continuous curve has a right endpoint whenever its image under a proper map approaches
a point with finite fiber. No metric or compact-tail assumption is needed. -/
theorem exists_right_limit_of_proper_finite_fiber
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    {f : X → Y} (hf : IsProperMap f) {v : ℝ → X} {a : ℝ} (ha : 0 < a)
    (hv : ContinuousOn v (Ioo 0 a)) {y : Y}
    (hlim : Tendsto (f ∘ v) (𝓝[>] 0) (𝓝 y)) (hfin : (f ⁻¹' {y}).Finite) :
    ∃ x, f x = y ∧ Tendsto v (𝓝[>] 0) (𝓝 x) := by
  have hb := ((nhdsGT_basis (0 : ℝ)).restrict_subset
    ((nhdsGT_basis (0 : ℝ)).mem_of_mem ha)).map v
  apply exists_limit_of_proper_finite_fiber_connected_basis hf hb ?_ ?_ hfin
  · intro b hb
    exact isPreconnected_Ioo.image v (hv.mono hb.2)
  · change Filter.map f (Filter.map v (𝓝[>] (0 : ℝ))) ≤ 𝓝 y
    rw [Filter.map_map]
    exact hlim

end
end GaloisForLFunctions.HTGeometry
