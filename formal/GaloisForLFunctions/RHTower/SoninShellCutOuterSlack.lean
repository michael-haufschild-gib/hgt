import GaloisForLFunctions.RHTower.SoninShellCutMiddleSlack

/-!
# The outer slack term and the refining cut

At the band whose radius is the shell's own outer aperture, the half-width again moves inside the
root, leaving the majorant at the gap times the root of half-width against that fixed radius.  Here
the majorant need not be small: the root carries the whole decay, because the half-width shrinks as
the cut refines.

Refinement is what drives this term, and the half-width of a cut into `N` equal annuli vanishes as
`N` grows.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open Filter
open scoped Topology

/-- **The cut refines.**  Cutting a shell into more annuli shrinks the half-width to zero. -/
theorem tendsto_soninShellCutWidth_atTop (b c : ℝ) :
    Tendsto (fun N : ℕ => soninShellCutWidth b c N) atTop (𝓝 0) := by
  have hcast : Tendsto (fun N : ℕ => 2 * (N : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_natCast_atTop_atTop
  have := Filter.Tendsto.const_div_atTop hcast (c - b)
  exact this.congr fun N => rfl

/-- **The outer slack term.**  The majorant at the gap, times the root of half-width against the
fixed radius. -/
theorem sqrt_soninShellCutSharpBandBoundAt_div_floor_outer
    (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) (w : ℝ) (hb : 0 ≤ b) :
    Real.sqrt (soninShellCutSharpBandBoundAt b c N w b) / soninShellCutNormFloor b c N =
      2 * (2 * (1 + 2 * soninRefTailSup 0 / (∫ y : ℝ, soninUnitBumpData y))) *
        (soninRefTailSup (soninShellCutWidth b c N * (w - b)) *
          Real.sqrt (soninShellCutWidth b c N * b / ∫ y : ℝ, soninUnitBumpSq y)) := by
  have hδ := soninShellCutWidth_pos b c hbc hN
  have hI : (0 : ℝ) < ∫ y : ℝ, soninUnitBumpSq y := integral_soninUnitBumpSq_pos
  rw [sqrt_soninShellCutSharpBandBoundAt_div_floor b c hbc hN w b hb]
  set δ : ℝ := soninShellCutWidth b c N with hδdef
  set C : ℝ := 1 + 2 * soninRefTailSup 0 / (∫ y : ℝ, soninUnitBumpData y) with hCdef
  set S : ℝ := soninRefTailSup (δ * (w - b)) with hSdef
  have hmove : δ * Real.sqrt (b / (δ * ∫ y : ℝ, soninUnitBumpSq y)) =
      Real.sqrt (δ * b / ∫ y : ℝ, soninUnitBumpSq y) :=
    mul_sqrt_div_eq_sqrt_mul_div δ b _ hδ hI
  calc 2 * (2 * δ * S * C) * Real.sqrt (b / (δ * ∫ y : ℝ, soninUnitBumpSq y))
      = 2 * (2 * C) * S * (δ * Real.sqrt (b / (δ * ∫ y : ℝ, soninUnitBumpSq y))) := by ring
    _ = 2 * (2 * C) * S * Real.sqrt (δ * b / ∫ y : ℝ, soninUnitBumpSq y) := by rw [hmove]
    _ = 2 * (2 * C) * (S * Real.sqrt (δ * b / ∫ y : ℝ, soninUnitBumpSq y)) := by ring

/-- The outer term's root factor vanishes as the cut refines. -/
theorem tendsto_sqrt_soninShellCutWidth_mul_atTop (b c : ℝ) (t : ℝ) :
    Tendsto (fun N : ℕ =>
      Real.sqrt (soninShellCutWidth b c N * t / ∫ y : ℝ, soninUnitBumpSq y)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun N : ℕ =>
      soninShellCutWidth b c N * t / ∫ y : ℝ, soninUnitBumpSq y) atTop (𝓝 0) := by
    have h := (tendsto_soninShellCutWidth_atTop b c).mul_const t
    have h2 := h.div_const (∫ y : ℝ, soninUnitBumpSq y)
    simpa using h2
  have := (Real.continuous_sqrt.tendsto 0).comp hbase
  simpa [Function.comp_def, Real.sqrt_zero] using this

end RHTower
