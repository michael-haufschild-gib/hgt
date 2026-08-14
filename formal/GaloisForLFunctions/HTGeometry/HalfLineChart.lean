import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Order.Interval.Set.Basic

/-!
# The chart carrying the unit interval onto the half line

The map `x ↦ x / (1 - x)` is a bijection of `(0,1)` onto `(0,∞)`, with derivative `(1-x)⁻²`.  It is
the substitution that turns a Beta integral on the unit interval into a Mellin integral on the half
line: under it `x^{w-1}(1-x)^{-w} dx` becomes `y^{w-1}(1+y)^{-1} dy`.

The three geometric inputs of that change of variables — the image, the injectivity and the
derivative — are recorded here separately from the integral identity they feed.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- The chart `x ↦ x / (1 - x)` of the unit interval onto the half line. -/
noncomputable def halfLineChart (x : ℝ) : ℝ := x / (1 - x)

theorem halfLineChart_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < halfLineChart x := by
  obtain ⟨hx0, hx1⟩ := hx
  exact div_pos hx0 (by linarith)

/-- The inverse chart. -/
noncomputable def halfLineChartInv (y : ℝ) : ℝ := y / (1 + y)

theorem halfLineChartInv_mem {y : ℝ} (hy : 0 < y) : halfLineChartInv y ∈ Ioo (0 : ℝ) 1 := by
  rw [halfLineChartInv]
  constructor
  · exact div_pos hy (by linarith)
  · rw [div_lt_one (by linarith)]
    linarith

theorem halfLineChart_halfLineChartInv {y : ℝ} (hy : 0 < y) :
    halfLineChart (halfLineChartInv y) = y := by
  have hpos : (0 : ℝ) < 1 + y := by linarith
  rw [halfLineChart, halfLineChartInv]
  rw [show (1 : ℝ) - y / (1 + y) = 1 / (1 + y) by field_simp; ring]
  field_simp

/-- **The chart carries the unit interval onto the half line.** -/
theorem halfLineChart_image : halfLineChart '' Ioo (0 : ℝ) 1 = Ioi (0 : ℝ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact halfLineChart_pos hx
  · intro hy
    exact ⟨halfLineChartInv y, halfLineChartInv_mem hy, halfLineChart_halfLineChartInv hy⟩

/-- **The chart is injective on the unit interval.** -/
theorem halfLineChart_injOn : InjOn halfLineChart (Ioo (0 : ℝ) 1) := by
  intro x hx x' hx' hxx
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hx'0, hx'1⟩ := hx'
  have h1 : (1 : ℝ) - x ≠ 0 := by linarith
  have h2 : (1 : ℝ) - x' ≠ 0 := by linarith
  rw [halfLineChart, halfLineChart, div_eq_div_iff h1 h2] at hxx
  nlinarith [hxx]

/-- **The derivative of the chart.** -/
theorem hasDerivAt_halfLineChart {x : ℝ} (hx : x ≠ 1) :
    HasDerivAt halfLineChart ((1 - x) ^ 2)⁻¹ x := by
  have hne : (1 : ℝ) - x ≠ 0 := by
    intro h
    exact hx (by linarith)
  have hnum : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have hden : HasDerivAt (fun t : ℝ => 1 - t) (-1) x :=
    HasDerivAt.const_sub (1 : ℝ) (hasDerivAt_id x)
  have h := hnum.div hden hne
  have hval : (1 * (1 - x) - x * -1) / (1 - x) ^ 2 = ((1 - x) ^ 2)⁻¹ := by
    field_simp
    ring
  rw [hval] at h
  exact h

theorem hasDerivWithinAt_halfLineChart {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivWithinAt halfLineChart ((1 - x) ^ 2)⁻¹ (Ioo (0 : ℝ) 1) x := by
  refine (hasDerivAt_halfLineChart ?_).hasDerivWithinAt
  intro h
  exact absurd hx.2 (by rw [h]; exact lt_irrefl 1)

/-- The chart turns the Beta weight into the Mellin weight, pointwise. -/
theorem halfLineChart_weight {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ((1 - x) ^ 2)⁻¹ * (1 + halfLineChart x)⁻¹ = (1 - x)⁻¹ := by
  obtain ⟨hx0, hx1⟩ := hx
  have hne : (1 : ℝ) - x ≠ 0 := by linarith
  rw [halfLineChart]
  rw [show (1 : ℝ) + x / (1 - x) = 1 / (1 - x) by field_simp; ring]
  field_simp

end GaloisForLFunctions.HTGeometry
