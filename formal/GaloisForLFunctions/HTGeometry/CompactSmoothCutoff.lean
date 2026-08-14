import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# A smooth cutoff equal to one near a plane compact

Between a compact set and an open set containing it there is always room for two nested metric
thickenings.  A smooth partition of unity separates the closed complement of the wider thickening
from the closed narrower one, producing a smooth function that is `1` on an open neighbourhood of
the compact set and has compact support inside the open set.

* `HTGeometry.exists_smooth_cutoff`.
-/

open Set Metric
open scoped Manifold ContDiff

namespace HTGeometry

/-- **A smooth cutoff for a compact set inside an open set.**  There is a smooth function equal to
`1` on an open neighbourhood of the compact set whose support is compact and contained in the open
set. -/
theorem exists_smooth_cutoff {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (chi : ℂ → ℝ) (W : Set ℂ), IsOpen W ∧ K ⊆ W ∧ ContDiff ℝ (⊤ : ℕ∞) chi ∧
      HasCompactSupport chi ∧ tsupport chi ⊆ U ∧ ∀ x ∈ W, chi x = 1 := by
  classical
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  set s : Set ℂ := (Metric.thickening (δ / 2) K)ᶜ with hs
  set t : Set ℂ := Metric.cthickening (δ / 4) K with ht
  have hsclosed : IsClosed s := Metric.isOpen_thickening.isClosed_compl
  have htclosed : IsClosed t := Metric.isClosed_cthickening
  have hd : Disjoint s t := by
    rw [Set.disjoint_left]
    intro x hx hxt
    exact hx (Metric.cthickening_subset_thickening' (by positivity) (by linarith) K hxt)
  obtain ⟨f, hf0, hf1, -⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed (I := 𝓘(ℝ, ℂ)) (M := ℂ) (n := (⊤ : ℕ∞))
      hsclosed htclosed hd
  have hsupp : Function.support (f : ℂ → ℝ) ⊆ Metric.thickening (δ / 2) K := by
    intro x hx
    by_contra hcon
    exact hx (hf0 hcon)
  have htsupp : tsupport (f : ℂ → ℝ) ⊆ Metric.cthickening (δ / 2) K :=
    (closure_mono hsupp).trans (Metric.closure_thickening_subset_cthickening _ _)
  refine ⟨f, Metric.thickening (δ / 4) K, Metric.isOpen_thickening,
    Metric.self_subset_thickening (by positivity) K, ?_, ?_, ?_, ?_⟩
  · rw [← contMDiff_iff_contDiff]
    exact f.contMDiff
  · exact IsCompact.of_isClosed_subset (hK.cthickening (r := δ / 2)) isClosed_closure htsupp
  · exact htsupp.trans ((Metric.cthickening_mono (by linarith) K).trans hsub)
  · intro x hx
    exact hf1 (Metric.thickening_subset_cthickening _ _ hx)

end HTGeometry
