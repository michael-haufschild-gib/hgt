import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Extracting the principal part of a double pole

A holomorphic `f` factors as `f s = f p + f'(p)(s - p) + (s - p)² G s` with `G` holomorphic, by
applying the slope extension twice: the difference quotient of a holomorphic function extends
holomorphically across the point, with value the derivative.  No second derivative and no power
series manipulation is needed — only the removable singularity theorem and the definition of the
derivative as a limit of slopes.

Consequently a function with a double pole splits as

```text
f s / (s - p)² = f p · (s - p)^{-2} + (f'(p) · (s - p)^{-1} + G s),
```

which is exactly the hypothesis of the rectangle residue theorem for a second-order pole.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The difference quotient of `f` at `p`, extended by the derivative. -/
def slopeExt (f : ℂ → ℂ) (p : ℂ) : ℂ → ℂ :=
  Function.update (fun s => (f s - f p) / (s - p)) p (deriv f p)

theorem slopeExt_of_ne {f : ℂ → ℂ} {p s : ℂ} (h : s ≠ p) :
    slopeExt f p s = (f s - f p) / (s - p) :=
  Function.update_of_ne h _ _

theorem slopeExt_self (f : ℂ → ℂ) (p : ℂ) : slopeExt f p p = deriv f p :=
  Function.update_self _ _ _

/-- The defining factorization, away from the point. -/
theorem eq_add_mul_slopeExt {f : ℂ → ℂ} {p s : ℂ} (h : s ≠ p) :
    f s = f p + (s - p) * slopeExt f p s := by
  rw [slopeExt_of_ne h, mul_div_cancel₀ _ (sub_ne_zero.mpr h)]
  ring

/-- **The slope extension is holomorphic.** -/
theorem differentiableOn_slopeExt {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {p : ℂ} (hp : p ∈ U) :
    DifferentiableOn ℂ (slopeExt f p) U := by
  have hUp : U ∈ 𝓝 p := hU.mem_nhds hp
  refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hUp).mp ⟨?_, ?_⟩
  · refine DifferentiableOn.congr (f := fun s => (f s - f p) / (s - p)) ?_ ?_
    · refine DifferentiableOn.div ?_ ?_ ?_
      · exact (hf.mono Set.sdiff_subset).sub_const _
      · exact (differentiable_id.sub_const p).differentiableOn
      · intro s hs
        exact sub_ne_zero.mpr (by simpa using hs.2)
    · intro s hs
      exact slopeExt_of_ne (by simpa using hs.2)
  · have hd : DifferentiableAt ℂ f p := hf.differentiableAt hUp
    have hslope : Tendsto (slope f p) (𝓝[≠] p) (𝓝 (deriv f p)) :=
      hasDerivAt_iff_tendsto_slope.mp hd.hasDerivAt
    rw [continuousAt_iff_punctured_nhds, slopeExt_self]
    refine hslope.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [slopeExt_of_ne hs, slope_def_field]

/-- **The second-order Taylor factorization.** -/
theorem exists_doublePole_split {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {p : ℂ} (hp : p ∈ U) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧
      ∀ s, s ≠ p → f s = f p + deriv f p * (s - p) + (s - p) ^ 2 * G s := by
  refine ⟨slopeExt (slopeExt f p) p, differentiableOn_slopeExt hU
    (differentiableOn_slopeExt hU hf hp) hp, fun s hs => ?_⟩
  have h1 := eq_add_mul_slopeExt (f := f) hs
  have h2 := eq_add_mul_slopeExt (f := slopeExt f p) hs
  rw [slopeExt_self] at h2
  rw [h1, h2]
  ring

/-- **The principal part of a double pole.**  Exactly the hypothesis shape of the rectangle
residue theorem for a second-order pole. -/
theorem exists_doublePole_principalPart {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {p : ℂ} (hp : p ∈ U) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧
      ∀ s, s ≠ p → f s / (s - p) ^ 2
        = f p * ((s - p) ^ 2)⁻¹ + (deriv f p * (s - p)⁻¹ + G s) := by
  obtain ⟨G, hG, hsplit⟩ := exists_doublePole_split hU hf hp
  refine ⟨G, hG, fun s hs => ?_⟩
  have hne : s - p ≠ 0 := sub_ne_zero.mpr hs
  rw [hsplit s hs]
  field_simp
  ring

end

end RHTower
