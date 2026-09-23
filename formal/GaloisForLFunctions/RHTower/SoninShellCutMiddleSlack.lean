import GaloisForLFunctions.RHTower.SoninRefTailWeightedVanishing
import GaloisForLFunctions.RHTower.SoninShellCutSlackClosedForm

/-!
# The middle slack term is a weighted majorant

Pulling the half-width inside the root turns a band term of the slack into the root of half-width
times radius, over the reference square's mass.  At the band whose radius grows with the scale, that
product is the gap's own argument scaled by a ratio of the shell's radii, so the term is a constant
times the majorant at the gap weighted by the root of the gap.

That is precisely the shape the weighted vanishing covers, so the term is small exactly when the gap
is large — by the schedule constant, not by refinement.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open Filter
open scoped Topology

/-- The half-width moves inside the root. -/
theorem mul_sqrt_div_eq_sqrt_mul_div (δ t I : ℝ) (hδ : 0 < δ) (hI : 0 < I) :
    δ * Real.sqrt (t / (δ * I)) = Real.sqrt (δ * t / I) := by
  have hδ2 : δ = Real.sqrt (δ ^ (2 : ℕ)) := (Real.sqrt_sq hδ.le).symm
  rw [hδ2, ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ δ ^ (2 : ℕ)), Real.sqrt_sq hδ.le]
  congr 1
  field_simp

/-- **A scaled root weight is absorbed.**  The majorant at the gap, weighted by the root of a fixed
multiple of the gap, still vanishes. -/
theorem tendsto_sqrt_const_mul_soninRefTailSup_atTop {κ : ℝ} (hκ : 0 ≤ κ) :
    Tendsto (fun u : ℝ => Real.sqrt (κ * u) * soninRefTailSup u) atTop (𝓝 0) := by
  have hbase := tendsto_sqrt_mul_soninRefTailSup_atTop
  have hconst := hbase.const_mul (Real.sqrt κ)
  rw [mul_zero] at hconst
  refine hconst.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  rw [Real.sqrt_mul hκ u]
  ring

/-- **The middle slack term.**  A constant of the shell times the majorant at the gap, weighted by
the root of the gap. -/
theorem sqrt_soninShellCutSharpBandBoundAt_div_floor_middle
    (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) (a q r : ℝ) (ha : 0 < a) (haq : a < q)
    (hr : 0 < r) :
    Real.sqrt (soninShellCutSharpBandBoundAt b c N (r * q) (r * a)) /
        soninShellCutNormFloor b c N =
      2 * (2 * (1 + 2 * soninRefTailSup 0 / (∫ y : ℝ, soninUnitBumpData y))) *
        (Real.sqrt (a / ((q - a) * ∫ y : ℝ, soninUnitBumpSq y) *
            (soninShellCutWidth b c N * (r * (q - a)))) *
          soninRefTailSup (soninShellCutWidth b c N * (r * (q - a)))) := by
  have hδ := soninShellCutWidth_pos b c hbc hN
  have hI : (0 : ℝ) < ∫ y : ℝ, soninUnitBumpSq y := integral_soninUnitBumpSq_pos
  have hgap : (0 : ℝ) < q - a := by linarith
  have harg : soninShellCutWidth b c N * (r * q - r * a) =
      soninShellCutWidth b c N * (r * (q - a)) := by ring
  rw [sqrt_soninShellCutSharpBandBoundAt_div_floor b c hbc hN (r * q) (r * a)
      (by positivity), harg]
  set δ : ℝ := soninShellCutWidth b c N with hδdef
  set C : ℝ := 1 + 2 * soninRefTailSup 0 / (∫ y : ℝ, soninUnitBumpData y) with hCdef
  set S : ℝ := soninRefTailSup (δ * (r * (q - a))) with hSdef
  have hmove : δ * Real.sqrt (r * a / (δ * ∫ y : ℝ, soninUnitBumpSq y)) =
      Real.sqrt (δ * (r * a) / ∫ y : ℝ, soninUnitBumpSq y) :=
    mul_sqrt_div_eq_sqrt_mul_div δ (r * a) _ hδ hI
  have hrad : δ * (r * a) / (∫ y : ℝ, soninUnitBumpSq y) =
      a / ((q - a) * ∫ y : ℝ, soninUnitBumpSq y) * (δ * (r * (q - a))) := by
    field_simp
  calc 2 * (2 * δ * S * C) * Real.sqrt (r * a / (δ * ∫ y : ℝ, soninUnitBumpSq y))
      = 2 * (2 * C) * S * (δ * Real.sqrt (r * a / (δ * ∫ y : ℝ, soninUnitBumpSq y))) := by ring
    _ = 2 * (2 * C) * S * Real.sqrt (δ * (r * a) / ∫ y : ℝ, soninUnitBumpSq y) := by rw [hmove]
    _ = 2 * (2 * C) * (Real.sqrt (a / ((q - a) * ∫ y : ℝ, soninUnitBumpSq y) *
          (δ * (r * (q - a)))) * S) := by rw [hrad]; ring

end RHTower
