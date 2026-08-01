import GaloisForLFunctions.HTGeometry.NormalizedRatioLaw

/-!
# The coefficient data of a normalized family

A finite family presented by shapes and limits, normalized by one member, produces exactly the data
the recurrence collapse consumes: the normalizing member is eventually nonzero, its own ratio is
`1`, and every ratio converges to an explicit constant — zero on the strictly dominated members.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

/-- A function with a nonzero normalized limit is eventually nonzero. -/
theorem eventually_ne_zero_of_normalized {F shape : ℝ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hF : Tendsto (fun t : ℝ => F t / shape t) atTop (nhds c)) :
    ∀ᶠ t : ℝ in atTop, F t ≠ 0 := by
  filter_upwards [hF.eventually_ne hc] with t ht
  intro h
  rw [h, zero_div] at ht
  exact ht rfl

/-- **The normalized family data.**  Normalizing a family by one member whose limit is nonzero: the
member is eventually nonzero, its shape ratio is `1`, and every ratio converges. -/
theorem tendsto_family_ratio_of_normalized {ι : Type*} {F shape : ι → ℝ → ℂ} {c r : ι → ℂ}
    (β : ι) (hcβ : c β ≠ 0) (hs : ∀ α, ∀ᶠ t : ℝ in atTop, shape α t ≠ 0)
    (hF : ∀ α, Tendsto (fun t : ℝ => F α t / shape α t) atTop (nhds (c α)))
    (hr : ∀ α, Tendsto (fun t : ℝ => shape α t / shape β t) atTop (nhds (r α))) :
    (∀ᶠ t : ℝ in atTop, F β t ≠ 0) ∧ r β = 1
      ∧ ∀ α, Tendsto (fun t : ℝ => F α t / F β t) atTop (nhds (c α * r α / c β)) := by
  have hone : Tendsto (fun t : ℝ => shape β t / shape β t) atTop (nhds 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hs β] with t ht
    rw [div_self ht]
  have hrβ : r β = 1 := tendsto_nhds_unique (hr β) hone
  refine ⟨eventually_ne_zero_of_normalized hcβ (hF β), hrβ, fun α => ?_⟩
  exact tendsto_ratio_of_normalized hcβ (hs α) (hs β) (hF α) (hF β) (hr α)

/-- The normalizing member has ratio `1`. -/
theorem self_ratio_eq_one {ι : Type*} {c r : ι → ℂ} (β : ι) (hcβ : c β ≠ 0) (hrβ : r β = 1) :
    c β * r β / c β = 1 := by
  rw [hrβ, mul_one, div_self hcβ]

end GaloisForLFunctions
