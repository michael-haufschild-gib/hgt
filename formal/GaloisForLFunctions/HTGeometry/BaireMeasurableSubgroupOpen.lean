import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Nonmeagre subgroups with the Baire property are open

**Pettis' theorem, subgroup form.**  In a topological additive group that is a Baire space, an
additive subgroup `A` with the Baire property that is not meagre is open.  Write `A =ᵇ U` with `U`
open; `U` is nonempty because `A` is not meagre.  Fix `x₀ ∈ U`.  For every `h` with `x₀ + h ∈ U`,
the open set `U ∩ (U + h)` is nonempty, and on a residual set both `y ∈ A ↔ y ∈ U` and
`y - h ∈ A ↔ y - h ∈ U` hold, so some `y` has `y ∈ A` and `y - h ∈ A`, whence
`h = -(y - h) + y ∈ A`.  Thus `A` is a neighbourhood of `0`.

A linear subspace of a topological vector space over a nontrivially normed field that is open is
the whole space, so a nonmeagre linear subspace with the Baire property of a Banach space is
everything.
-/

open Topology Filter

namespace GaloisForLFunctions.HTGeometry

section Group

variable {G : Type*} [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G] [BaireSpace G]

/-- **Pettis' theorem, subgroup form.**  A nonmeagre additive subgroup with the Baire property of a
Baire topological group contains a neighbourhood of zero. -/
theorem addSubgroup_mem_nhds_zero_of_baireMeasurableSet_of_not_isMeagre (A : AddSubgroup G)
    (hA : BaireMeasurableSet (A : Set G)) (hnm : ¬ IsMeagre (A : Set G)) :
    (A : Set G) ∈ 𝓝 (0 : G) := by
  obtain ⟨U, hU, hAU⟩ := hA.residualEq_isOpen
  have hres1 : ∀ᶠ y in residual G, (y ∈ (A : Set G) ↔ y ∈ U) :=
    Filter.eventuallyEq_set.1 hAU
  have hUne : U.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    apply hnm
    change (A : Set G)ᶜ ∈ residual G
    filter_upwards [hres1] with y hy
    simpa using hy
  obtain ⟨x₀, hx₀⟩ := hUne
  have hN : (fun h : G => x₀ + h) ⁻¹' U ∈ 𝓝 (0 : G) :=
    (hU.preimage (continuous_const.add continuous_id)).mem_nhds (by simpa using hx₀)
  refine Filter.mem_of_superset hN fun h hh => ?_
  have hres2 : ∀ᶠ y in residual G, (y - h ∈ (A : Set G) ↔ y - h ∈ U) :=
    (tendsto_residual_of_isOpenMap (continuous_sub_right h)
      (Homeomorph.subRight h).isOpenMap).eventually hres1
  have hdense : Dense {y | (y ∈ (A : Set G) ↔ y ∈ U) ∧ (y - h ∈ (A : Set G) ↔ y - h ∈ U)} :=
    dense_of_mem_residual (hres1.and hres2)
  have hVopen : IsOpen (U ∩ (fun y => y - h) ⁻¹' U) :=
    hU.inter (hU.preimage (continuous_sub_right h))
  have hVne : (U ∩ (fun y => y - h) ⁻¹' U).Nonempty :=
    ⟨x₀ + h, hh, by simpa using hx₀⟩
  obtain ⟨y, ⟨hyU, hyhU⟩, hyA, hyhA⟩ := hdense.inter_open_nonempty _ hVopen hVne
  have hy : y ∈ A := hyA.2 hyU
  have hyh : y - h ∈ A := hyhA.2 hyhU
  have hmem := A.add_mem (A.neg_mem hyh) hy
  rwa [neg_sub, sub_add_cancel] at hmem

/-- **Pettis' theorem, subgroup form.**  A nonmeagre additive subgroup with the Baire property of a
Baire topological group is open. -/
theorem addSubgroup_isOpen_of_baireMeasurableSet_of_not_isMeagre (A : AddSubgroup G)
    (hA : BaireMeasurableSet (A : Set G)) (hnm : ¬ IsMeagre (A : Set G)) :
    IsOpen (A : Set G) :=
  A.isOpen_of_mem_nhds (addSubgroup_mem_nhds_zero_of_baireMeasurableSet_of_not_isMeagre A hA hnm)

/-- In a connected Baire topological group, a nonmeagre additive subgroup with the Baire property
is the whole group: it is open, hence clopen. -/
theorem addSubgroup_eq_top_of_baireMeasurableSet_of_not_isMeagre [ConnectedSpace G]
    (A : AddSubgroup G) (hA : BaireMeasurableSet (A : Set G)) (hnm : ¬ IsMeagre (A : Set G)) :
    A = ⊤ := by
  have hopen := addSubgroup_isOpen_of_baireMeasurableSet_of_not_isMeagre A hA hnm
  have huniv : (A : Set G) = Set.univ :=
    IsClopen.eq_univ ⟨A.isClosed_of_isOpen hopen, hopen⟩ ⟨0, A.zero_mem⟩
  exact AddSubgroup.coe_eq_univ.1 huniv

end Group

section Module

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] [BaireSpace E]

/-- **Second-category linear domains are everything.**  A linear subspace with the Baire
property that is not meagre is the whole space. -/
theorem submodule_eq_top_of_baireMeasurableSet_of_not_isMeagre (A : Submodule 𝕜 E)
    (hA : BaireMeasurableSet (A : Set E)) (hnm : ¬ IsMeagre (A : Set E)) : A = ⊤ := by
  have hopen : IsOpen (A : Set E) :=
    addSubgroup_isOpen_of_baireMeasurableSet_of_not_isMeagre A.toAddSubgroup hA hnm
  refine A.eq_top_of_nonempty_interior' ⟨0, ?_⟩
  rw [hopen.interior_eq]
  exact A.zero_mem

/-- A proper linear subspace with the Baire property is meagre. -/
theorem isMeagre_of_baireMeasurableSet_of_ne_top (A : Submodule 𝕜 E)
    (hA : BaireMeasurableSet (A : Set E)) (hne : A ≠ ⊤) : IsMeagre (A : Set E) := by
  by_contra hnm
  exact hne (submodule_eq_top_of_baireMeasurableSet_of_not_isMeagre A hA hnm)

end Module

end GaloisForLFunctions.HTGeometry
