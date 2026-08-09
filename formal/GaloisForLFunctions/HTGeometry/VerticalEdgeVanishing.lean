import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Vanishing of exponentially dominated vertical edges

A vertical-segment integral whose integrand is exponentially dominated in the horizontal
coordinate vanishes as the segment escapes to infinity, on either side.  This is the
boundary-vanishing engine for widening-rectangle contour arguments: the segment length is fixed,
the sup bound decays exponentially, and the squeeze closes the limit.
-/

namespace HTGeometry

open Filter intervalIntegral

/-- **Right vertical edge vanishing.**  If `‖G(X + yi)‖ ≤ C·e^{−δX}` for `X ≥ 0` and `|y| ≤ Y`,
then the right-edge segment integrals vanish as `X → ∞`. -/
theorem tendsto_vertical_edge_zero_right {G : ℂ → ℂ} {Y C δ : ℝ}
    (hY : 0 ≤ Y) (hδ : 0 < δ)
    (hbound : ∀ X y : ℝ, 0 ≤ X → |y| ≤ Y →
      ‖G ((X : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C * Real.exp (-(δ * X))) :
    Tendsto (fun X : ℝ => ∫ y in (-Y)..Y, G ((X : ℂ) + (y : ℂ) * Complex.I))
      atTop (nhds 0) := by
  refine squeeze_zero_norm'
    (a := fun X : ℝ => C * |Y - (-Y)| * Real.exp (-(δ * X))) ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
    have hseg : ∀ y ∈ Set.uIoc (-Y) Y,
        ‖G ((X : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C * Real.exp (-(δ * X)) := by
      intro y hy
      have hy' : |y| ≤ Y := by
        rcases Set.mem_uIoc.mp hy with h | h
        · rw [abs_le]; constructor <;> linarith [h.1, h.2]
        · rw [abs_le]; constructor <;> linarith [h.1, h.2]
      exact hbound X y hX hy'
    calc ‖∫ y in (-Y)..Y, G ((X : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ C * Real.exp (-(δ * X)) * |Y - (-Y)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hseg
      _ = C * |Y - (-Y)| * Real.exp (-(δ * X)) := by ring
  · have hexp : Tendsto (fun X : ℝ => Real.exp (-(δ * X))) atTop (nhds 0) := by
      have h1 : Tendsto (fun X : ℝ => δ * X) atTop atTop :=
        Tendsto.const_mul_atTop hδ tendsto_id
      have h2 : Tendsto (fun X : ℝ => -(δ * X)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp h1
      exact Real.tendsto_exp_atBot.comp h2
    simpa using hexp.const_mul (C * |Y - (-Y)|)

/-- **Left vertical edge vanishing.**  The mirror statement at `−X`. -/
theorem tendsto_vertical_edge_zero_left {G : ℂ → ℂ} {Y C δ : ℝ}
    (hY : 0 ≤ Y) (hδ : 0 < δ)
    (hbound : ∀ X y : ℝ, 0 ≤ X → |y| ≤ Y →
      ‖G ((-X : ℝ) + (y : ℂ) * Complex.I)‖ ≤ C * Real.exp (-(δ * X))) :
    Tendsto (fun X : ℝ => ∫ y in (-Y)..Y, G (((-X : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      atTop (nhds 0) := by
  exact tendsto_vertical_edge_zero_right (G := fun z => G (-(z.re) + z.im * Complex.I))
    hY hδ (by
      intro X y hX hy
      simpa using hbound X y hX hy) |>.congr (by
        intro X
        apply intervalIntegral.integral_congr
        intro y hy
        simp)

end HTGeometry
