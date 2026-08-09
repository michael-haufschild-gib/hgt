import GaloisForLFunctions.HTGeometry.LatticeFundamentalCover
import GaloisForLFunctions.HTGeometry.PeriodicCoverVanishing

/-!
# The vanishing criterion of a Siegel-type count

Assembling the geometry: a subgroup with compact quotient supplies a compact fundamental set and,
for any prescribed radius, a finite set of centres covering it.  Once the Schwarz gain
`(r/R)^N/(1−r/R)` is below one, *any* periodic function whose jets of order below `N` vanish at
every one of those centres is identically zero.

This is exactly the shape a dimension count consumes: the count produces the jet vanishing at a
finite prescribed set of points, and this theorem converts it into a global identity.

* **`exists_finite_centres_forcing_vanishing`**.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- **Finitely many centres whose jet vanishing forces a periodic function to vanish.** -/
theorem exists_finite_centres_forcing_vanishing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℝ E]
    {P : AddSubgroup E} (hcpt : CompactSpace (E ⧸ P))
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : 0 < R) {N : ℕ}
    (hθ : (r / R) ^ N / (1 - r / R) < 1) :
    ∃ s : Set E, s.Finite ∧ ∀ F : E → ℂ, ContDiff ℂ (⊤ : ℕ∞) F →
      (∀ p ∈ P, ∀ z : E, F (z + p) = F z) →
      (∀ c ∈ s, ∀ k, k < N → iteratedFDeriv ℂ k F c = 0) → ∀ z, F z = 0 := by
  obtain ⟨K, s, hKcomp, hKne, hfund, hsfin, hcov⟩ :=
    exists_finite_centres_of_compactSpace_quotient hcpt hr
  refine ⟨s, hsfin, ?_⟩
  intro F hF hper hvan
  refine eqOn_zero_of_periodic_cover hF hper hKcomp hKne hfund
    (fun i : s => (i : E)) hr.le hrR hR ?_ ?_ hθ
  · intro i k hk
    exact hvan (i : E) i.2 k hk
  · intro z hz
    obtain ⟨c, hc, hzc⟩ := hcov z hz
    exact ⟨⟨c, hc⟩, hzc⟩

end GaloisForLFunctions.HTGeometry
