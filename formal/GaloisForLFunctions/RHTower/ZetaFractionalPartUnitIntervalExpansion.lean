import GaloisForLFunctions.RHTower.ZetaFractionalPartTrigEquations
import GaloisForLFunctions.HTGeometry.FractionalPartPartialIntegration
import GaloisForLFunctions.HTGeometry.LogTrigPowerPrimitiveGrowth

/-!
# Unit-interval expansion of the fractional-part integrals for zeta

The two real integrals

`∫_1^∞ {x} x^(-a-1) cos (b log x) dx`,  `∫_1^∞ {x} x^(-a-1) sin (b log x) dx`

converge for `a > 0`, and their truncations at an integer are given exactly by the unit-interval
partial-integration formula: a sum of first-primitive values at the integers, minus the increment
of the second primitive.

The first-primitive sum cannot be omitted.  With the jump terms dropped, what remains is
`{N} P(N) - (W(N) - W(1))`, an expression that has no limit at `+∞` as soon as `0 < a < 1` and
`b ≠ 0`, because `W` carries the growing factor `N^(1-a)` in front of a nonvanishing logarithmic
harmonic.  So the convergent value of the integral can never be read off that expression.
-/

open Complex Real MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

variable {s : ℂ}

theorem zetaTrig_amplitude_ne_zero (h0 : 0 < s.re) : (-s.re) ^ 2 + s.im ^ 2 ≠ 0 := by
  have : (0 : ℝ) < (-s.re) ^ 2 + s.im ^ 2 := by positivity
  exact this.ne'

theorem zetaTrig_shifted_amplitude_ne_zero (h1 : s.re < 1) :
    (-s.re + 1) ^ 2 + s.im ^ 2 ≠ 0 := by
  have hne : -s.re + 1 ≠ 0 := by intro h; linarith
  have : (0 : ℝ) < (-s.re + 1) ^ 2 + s.im ^ 2 := by positivity
  exact this.ne'

/-- **Truncated cosine integral, expanded over unit intervals.** -/
theorem integral_one_to_succ_fract_rpow_cos (h0 : 0 < s.re) (h1 : s.re < 1) (m : ℕ) :
    (∫ x in (1 : ℝ)..((m : ℝ) + 1),
        Int.fract x * x ^ (-(s.re + 1)) * Real.cos (s.im * Real.log x))
      = (∑ k ∈ Finset.range m, cosLogPrimitive (-s.re) s.im ((k : ℝ) + 2))
        - (cosLogSecondPrimitive (-s.re) s.im ((m : ℝ) + 1)
            - cosLogSecondPrimitive (-s.re) s.im 1) := by
  have h := integral_one_to_succ_fract_mul_cos_log (c := -s.re) (b := s.im)
    (zetaTrig_amplitude_ne_zero h0) (zetaTrig_shifted_amplitude_ne_zero h1) m
  rw [← h]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [show -s.re - 1 = -(s.re + 1) by ring]
  ring

/-- **Truncated sine integral, expanded over unit intervals.** -/
theorem integral_one_to_succ_fract_rpow_sin (h0 : 0 < s.re) (h1 : s.re < 1) (m : ℕ) :
    (∫ x in (1 : ℝ)..((m : ℝ) + 1),
        Int.fract x * x ^ (-(s.re + 1)) * Real.sin (s.im * Real.log x))
      = (∑ k ∈ Finset.range m, sinLogPrimitive (-s.re) s.im ((k : ℝ) + 2))
        - (sinLogSecondPrimitive (-s.re) s.im ((m : ℝ) + 1)
            - sinLogSecondPrimitive (-s.re) s.im 1) := by
  have h := integral_one_to_succ_fract_mul_sin_log (c := -s.re) (b := s.im)
    (zetaTrig_amplitude_ne_zero h0) (zetaTrig_shifted_amplitude_ne_zero h1) m
  rw [← h]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [show -s.re - 1 = -(s.re + 1) by ring]
  ring

/-! ## The truncations converge -/

theorem tendsto_truncated_fract_rpow_cos (h0 : 0 < s.re) (hs1 : s ≠ 1) :
    Tendsto (fun m : ℕ => ∫ x in (1 : ℝ)..((m : ℝ) + 1),
        Int.fract x * x ^ (-(s.re + 1)) * Real.cos (s.im * Real.log x)) atTop
      (𝓝 (1 / (s - 1) - riemannZeta s / s).re) := by
  rw [← integral_Ioi_one_fract_rpow_cos h0 hs1]
  exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi 1
    (integrableOn_Ioi_one_fract_rpow_cos h0)
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

theorem tendsto_truncated_fract_rpow_sin (h0 : 0 < s.re) (hs1 : s ≠ 1) :
    Tendsto (fun m : ℕ => ∫ x in (1 : ℝ)..((m : ℝ) + 1),
        Int.fract x * x ^ (-(s.re + 1)) * Real.sin (s.im * Real.log x)) atTop
      (𝓝 (-(1 / (s - 1) - riemannZeta s / s).im)) := by
  rw [← integral_Ioi_one_fract_rpow_sin h0 hs1]
  exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi 1
    (integrableOn_Ioi_one_fract_rpow_sin h0)
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

/-! ## The jump terms are indispensable -/

/-- **The jump-free expression has no limit.**  Inside the open critical strip, off the real axis,
the expression `{N} P(N) - (W(N) - W(1))` obtained by ignoring the jumps of `{x}` converges to no
real number, although the integral it purports to evaluate converges. -/
theorem not_tendsto_jumpFree_cos (h0 : 0 < s.re) (h1 : s.re < 1) (hb : s.im ≠ 0) (L : ℝ) :
    ¬ Tendsto (fun N : ℝ => Int.fract N * cosLogPrimitive (-s.re) s.im N
        - (cosLogSecondPrimitive (-s.re) s.im N
            - cosLogSecondPrimitive (-s.re) s.im 1)) atTop (𝓝 L) :=
  not_tendsto_jumpFreeCos_atTop hb (by linarith) (by linarith)

/-- Sine version. -/
theorem not_tendsto_jumpFree_sin (h0 : 0 < s.re) (h1 : s.re < 1) (hb : s.im ≠ 0) (L : ℝ) :
    ¬ Tendsto (fun N : ℝ => Int.fract N * sinLogPrimitive (-s.re) s.im N
        - (sinLogSecondPrimitive (-s.re) s.im N
            - sinLogSecondPrimitive (-s.re) s.im 1)) atTop (𝓝 L) :=
  not_tendsto_jumpFreeSin_atTop hb (by linarith) (by linarith)

end RHTower
