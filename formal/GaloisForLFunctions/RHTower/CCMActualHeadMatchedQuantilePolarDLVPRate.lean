import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarCoordinateTransport
import GaloisForLFunctions.RHTower.SuzukiScrewGrowthBound
import GaloisForLFunctions.RHTower.XiMassCriticalOutgoingCurrent

/-!
# De la Vallee Poussin rate in matched polar mass coordinate

The rigid matched-to-quantile displacement is driven by the completed critical-Mellin error.
This module begins its unconditional arithmetic control at the exact Volterra input: the
normalized Chebyshev error. The corpus Littlewood/de la Vallee Poussin theorem gives the sharp
logarithmic-height rate

`|E_norm(h)| <= B exp(h/2 - c sqrt(h))`.

Consequently this driver vanishes after division by the polar mass scale `exp(h/2)`. These are
source theorems with no RH premise, numerical verification, or additional axiom.
-/

open Filter Topology Set MeasureTheory

noncomputable section

namespace RHTower

/-- The normalized Chebyshev driver of the completed critical-Mellin error has the
de la Vallee Poussin rate in logarithmic height. -/
theorem exists_abs_criticalMellinNormalizedChebyshevError_le_exp_half_sub_sqrt :
    ∃ c B : ℝ, 0 < c ∧ 0 ≤ B ∧ ∀ᶠ h : ℝ in atTop,
      |criticalMellinNormalizedChebyshevError h| ≤
        B * Real.exp (h / 2 - c * Real.sqrt h) := by
  obtain ⟨c, B, hc, hB, hrate⟩ :=
    exists_abs_suzukiChebyshevError_le_sqrtLog
  refine ⟨c, B, hc, hB, ?_⟩
  filter_upwards [Real.tendsto_exp_atTop.eventually hrate,
    eventually_ge_atTop (0 : ℝ)] with h hrateh hh
  have hexp : (0 : ℝ) < Real.exp h := Real.exp_pos h
  have hsqrt : Real.sqrt (Real.exp h) = Real.exp (h / 2) :=
    sqrt_exp_eq_exp_half h
  have hrateh' : |Chebyshev.psi (Real.exp h) - Real.exp h| ≤
      B * Real.exp h * Real.exp (-c * Real.sqrt h) := by
    simpa only [suzukiChebyshevError, Real.log_exp] using hrateh
  unfold criticalMellinNormalizedChebyshevError
  rw [criticalMellinError, criticalCumulative_vonMangoldt_eq_psi, abs_div,
    abs_of_pos (Real.sqrt_pos.mpr hexp)]
  calc
    |Chebyshev.psi (Real.exp h) - Real.exp h| / Real.sqrt (Real.exp h) ≤
        (B * Real.exp h * Real.exp (-c * Real.sqrt h)) /
          Real.sqrt (Real.exp h) :=
      div_le_div_of_nonneg_right hrateh' (Real.sqrt_nonneg _)
    _ = B * Real.exp (h / 2 - c * Real.sqrt h) := by
      rw [hsqrt, div_eq_iff (Real.exp_ne_zero (h / 2))]
      rw [show Real.exp h = Real.exp (h / 2) * Real.exp (h / 2) by
        rw [← Real.exp_add]
        congr 1
        ring]
      rw [show Real.exp (h / 2 - c * Real.sqrt h) =
          Real.exp (h / 2) * Real.exp (-c * Real.sqrt h) by
        rw [← Real.exp_add]
        congr 1
        ring]
      ring

/-- The PNT-scale driver is negligible relative to the polar mass coordinate. -/
theorem tendsto_exp_neg_half_mul_criticalMellinNormalizedChebyshevError_atTop_zero :
    Tendsto (fun h : ℝ => Real.exp (-h / 2) *
      criticalMellinNormalizedChebyshevError h) atTop (𝓝 0) := by
  obtain ⟨c, B, hc, hB, hrate⟩ :=
    exists_abs_criticalMellinNormalizedChebyshevError_le_exp_half_sub_sqrt
  have hmajor : Tendsto (fun h : ℝ =>
      B * Real.exp (-c * Real.sqrt h)) atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun h : ℝ => Real.sqrt h) atTop atTop :=
      Real.tendsto_sqrt_atTop
    have harg : Tendsto (fun h : ℝ => -c * Real.sqrt h) atTop atBot := by
      have hmul := hsqrt.const_mul_atTop hc
      have hneg := tendsto_neg_atBot_iff.2 hmul
      simpa [neg_mul] using hneg
    have hexp := Real.tendsto_exp_atBot.comp harg
    simpa using hexp.const_mul B
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [hrate] with h hh
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-h / 2) * |criticalMellinNormalizedChebyshevError h| ≤
        Real.exp (-h / 2) *
          (B * Real.exp (h / 2 - c * Real.sqrt h)) :=
      mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    _ = B * Real.exp (-c * Real.sqrt h) := by
      rw [show Real.exp (h / 2 - c * Real.sqrt h) =
          Real.exp (h / 2) * Real.exp (-c * Real.sqrt h) by
        rw [← Real.exp_add]
        congr 1
        ring]
      calc
        Real.exp (-h / 2) *
            (B * (Real.exp (h / 2) * Real.exp (-c * Real.sqrt h))) =
            B * (Real.exp (-h / 2) * Real.exp (h / 2)) *
              Real.exp (-c * Real.sqrt h) := by ring
        _ = B * Real.exp (-c * Real.sqrt h) := by
          rw [show Real.exp (-h / 2) * Real.exp (h / 2) = 1 by
            calc
              Real.exp (-h / 2) * Real.exp (h / 2) = Real.exp 0 := by
                rw [← Real.exp_add]
                congr 1
                ring
              _ = 1 := Real.exp_zero]
          ring

end RHTower
