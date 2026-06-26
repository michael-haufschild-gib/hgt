/-
# Finite sheaf-gluing of analytic branches (hDisc lift, cover-assembly step)

The dyadic-cover lift `hliftF`/`hliftG` (`Q62Assembly.noRelation_of_disconnected_lifts`) is assembled by
gluing the local Böttcher branches (`CoverConstruction.exists_local_bottcherBranch_basin`) around the cover
annulus. The two-patch glues (`CoverConstruction.analyticOnNhd_glue{,_cocycle,_unit}`) are the atoms; the
final assembly needs the **finite** glue: once the multiplicative cocycle is trivialized (`∏ uᵢ = 1`
around the loop, from `CoverConstruction.no_singlevalued_branch_of_dyadic_period`), the adjusted branches
agree pairwise, and a finite family of pairwise-agreeing analytic branches glues to one global analytic
function on the union. This file supplies that step.

This is a *cover-assembly* lemma, not the loop-cocycle closure itself (which trivializes the cocycle); it
consumes the trivialized data.
-/
import GaloisForLFunctions.Bottcher.CoverConstruction

open Set

namespace Bottcher

/-- **Finite sheaf-gluing of analytic branches.** A finite family of analytic branches `f i` on opens
`U i` (`i ∈ s`) that agree pairwise on overlaps (`EqOn (f i) (f j) (U i ∩ U j)`) glues to a single analytic
`F` on `⋃ i ∈ s, U i`, with `F = f i` on each `U i`. The global `F` is `z ↦ f i z` for any patch `i ∋ z`
(well-defined by pairwise agreement); analyticity is local (`F =ᶠ f i` near any `z ∈ U i`). The final
assembly step of the dyadic-cover lift, consuming the cocycle-trivialized branches. -/
theorem analyticOnNhd_glue_finite {ι : Type*} (s : Finset ι) (U : ι → Set ℂ) (f : ι → ℂ → ℂ)
    (hUo : ∀ i ∈ s, IsOpen (U i)) (hf : ∀ i ∈ s, AnalyticOnNhd ℂ (f i) (U i))
    (hagree : ∀ i ∈ s, ∀ j ∈ s, EqOn (f i) (f j) (U i ∩ U j)) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (⋃ i ∈ s, U i) ∧ ∀ i ∈ s, EqOn F (f i) (U i) := by
  classical
  refine ⟨fun z => if h : ∃ i ∈ s, z ∈ U i then f h.choose z else 0, ?_, ?_⟩
  · intro z hz
    simp only [Set.mem_iUnion, exists_prop] at hz
    obtain ⟨i, hi, hzi⟩ := hz
    have hcongr : (fun z => if h : ∃ i ∈ s, z ∈ U i then f h.choose z else 0) =ᶠ[nhds z] f i := by
      filter_upwards [(hUo i hi).mem_nhds hzi] with w hw
      have hex : ∃ i ∈ s, w ∈ U i := ⟨i, hi, hw⟩
      rw [dif_pos hex]
      obtain ⟨hjs, hwj⟩ := hex.choose_spec
      exact hagree hex.choose hjs i hi ⟨hwj, hw⟩
    exact (hf i hi z hzi).congr hcongr.symm
  · intro i hi z hzi
    have hex : ∃ i ∈ s, z ∈ U i := ⟨i, hi, hzi⟩
    show (if h : ∃ i ∈ s, z ∈ U i then f h.choose z else 0) = f i z
    rw [dif_pos hex]
    obtain ⟨hjs, hzj⟩ := hex.choose_spec
    exact hagree hex.choose hjs i hi ⟨hzj, hzi⟩

end Bottcher
