import GaloisForLFunctions.HTGeometry.ObserverTemporalBirthValuationLaw

/-!
# Active analytic sectors exist

The temporal birth laws assume that a scalar response does not vanish identically near the origin.
The condition is exactly frequent nonvanishing there, and it is realized by every response with a
nonzero value at the origin — in particular by every nonzero constant, and by the identity, whose
zero at the origin is isolated.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Activity is frequent nonvanishing at the origin. -/
theorem analyticSectorActive_iff_frequently {f : ℂ → ℂ} :
    AnalyticSectorActive f ↔ ∃ᶠ z in nhds (0 : ℂ), f z ≠ 0 := by
  rw [AnalyticSectorActive, Filter.EventuallyEq, Filter.not_eventually]

/-- A response that does not vanish at the origin is active. -/
theorem analyticSectorActive_of_apply_ne_zero {f : ℂ → ℂ} (h : f 0 ≠ 0) :
    AnalyticSectorActive f := fun hev => h hev.self_of_nhds

/-- Every nonzero constant response is active. -/
theorem analyticSectorActive_const {c : ℂ} (hc : c ≠ 0) :
    AnalyticSectorActive (fun _ : ℂ => c) :=
  analyticSectorActive_of_apply_ne_zero hc

/-- The identity response is active even though it vanishes at the origin: its zero is isolated. -/
theorem analyticSectorActive_id : AnalyticSectorActive (fun z : ℂ => z) := by
  intro hev
  have hpunct : ∀ᶠ z : ℂ in nhdsWithin 0 {(0 : ℂ)}ᶜ, z = 0 :=
    hev.filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ z : ℂ in nhdsWithin 0 {(0 : ℂ)}ᶜ, z ≠ 0 := self_mem_nhdsWithin
  obtain ⟨z, hz0, hzne⟩ := (hpunct.and hne).exists
  exact hzne hz0

/-- Activity is preserved by nonzero scaling. -/
theorem AnalyticSectorActive.const_smul {f : ℂ → ℂ} (hf : AnalyticSectorActive f) {c : ℂ}
    (hc : c ≠ 0) : AnalyticSectorActive (fun z => c * f z) := by
  intro hev
  refine hf ?_
  filter_upwards [hev] with z hz
  exact (mul_eq_zero.mp hz).resolve_left hc

end GaloisForLFunctions.HTGeometry
