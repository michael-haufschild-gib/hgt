import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The central average of a primitive

For a continuous integrand `g`, the average `(∫₀ˢ g) / s` tends to `g 0` as `s → 0`: the primitive
vanishes at the origin, so the average is its slope there, and the fundamental theorem of calculus
identifies that slope with `g 0`.

The consequence used downstream is the vanishing case: if `g 0 = 0`, the aperture average over
`[0, 2a]` tends to zero as the aperture shrinks.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- **The central average of a primitive.**  The average of a continuous function over `[0, s]`
tends to its value at the origin. -/
theorem tendsto_primitive_div_nhdsNE_zero {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (fun s : ℝ => (∫ t in (0 : ℝ)..s, g t) / s) (𝓝[≠] (0 : ℝ)) (𝓝 (g 0)) := by
  have hderiv : HasDerivAt (fun s : ℝ => ∫ t in (0 : ℝ)..s, g t) (g 0) 0 :=
    (hg.integral_hasStrictDerivAt 0 0).hasDerivAt
  have hzero : (fun s : ℝ => ∫ t in (0 : ℝ)..s, g t) 0 = 0 := by simp
  have hslope := hasDerivAt_iff_tendsto_slope.mp hderiv
  refine hslope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [slope_def_field, hzero, sub_zero, div_eq_inv_mul]

/-- **Vanishing aperture average.**  For a continuous integrand vanishing at the origin, the
average over `[0, 2a]` tends to zero as the aperture shrinks to zero from above. -/
theorem tendsto_primitive_div_two_mul_nhdsGT_zero {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : g 0 = 0) :
    Tendsto (fun a : ℝ => (∫ t in (0 : ℝ)..(2 * a), g t) / (2 * a)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hbase := tendsto_primitive_div_nhdsNE_zero hg
  rw [hg0] at hbase
  have hmap : Tendsto (fun a : ℝ => 2 * a) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun a : ℝ => 2 * a) 0 := by fun_prop
      have hlim := hc.tendsto
      simp only [mul_zero] at hlim
      exact hlim.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with a ha
      simp only [Set.mem_Ioi] at ha
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      positivity
  exact hbase.comp hmap

end

end GaloisForLFunctions.HTGeometry
