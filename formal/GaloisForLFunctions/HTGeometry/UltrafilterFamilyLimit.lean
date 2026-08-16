import Mathlib

/-!
# Simultaneous limits of a finite family along an ultrafilter

A bounded real family converges along any ultrafilter, because a closed bounded interval is
compact.  Refining a filter to an ultrafilter therefore makes *every* member of a finite — indeed
of an arbitrary — family of bounded functions converge at once, with no diagonal extraction and no
countability hypothesis.

This replaces the repeated Bolzano–Weierstrass step of a subsequence argument.
-/

open Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

/-- **Simultaneous limits.**  Refining to an ultrafilter makes every member of a family of
eventually bounded real functions converge. -/
theorem exists_ultrafilter_tendsto_of_eventually_bounded {ι : Type*} {κ : Type*}
    {L : Filter ι} [L.NeBot] (a : κ → ι → ℝ) {lo hi : ℝ}
    (hb : ∀ k, ∀ᶠ i in L, a k i ∈ Icc lo hi) :
    ∃ U : Ultrafilter ι, ↑U ≤ L ∧ ∃ m : κ → ℝ,
      (∀ k, m k ∈ Icc lo hi) ∧ ∀ k, Tendsto (a k) (U : Filter ι) (𝓝 (m k)) := by
  classical
  refine ⟨Ultrafilter.of L, Ultrafilter.of_le L, ?_⟩
  have hstep : ∀ k : κ, ∃ x ∈ Icc lo hi,
      Tendsto (a k) ((Ultrafilter.of L : Filter ι)) (𝓝 x) := by
    intro k
    have hmem : ∀ᶠ i in (Ultrafilter.of L : Filter ι), a k i ∈ Icc lo hi :=
      Filter.Eventually.filter_mono (Ultrafilter.of_le L) (hb k)
    have hle : ((Ultrafilter.map (a k) (Ultrafilter.of L)) : Filter ℝ) ≤ 𝓟 (Icc lo hi) := by
      rw [le_principal_iff]
      exact hmem
    obtain ⟨x, hx, hxle⟩ :=
      (isCompact_Icc (a := lo) (b := hi)).ultrafilter_le_nhds
        (Ultrafilter.map (a k) (Ultrafilter.of L)) hle
    exact ⟨x, hx, hxle⟩
  choose m hmem hlim using hstep
  exact ⟨m, hmem, hlim⟩

end GaloisForLFunctions.HTGeometry
