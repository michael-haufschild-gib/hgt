import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilClockCommutator
import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilExponentialClockAbelTransport

/-!
# Linear envelope for the damped third-grade prime-minus-polar source

Fix a wall `b > 0`. The third-grade cumulative source `Q_b(H)` is, for `H ≥ b`, the finite
prime sum `∑_{2 ≤ k ≤ e^H, log k > b} 32 Λ(k) k^(-1/2) / (log k)³` minus the polar integral
`∫_b^H (32 / h³) · 2 cosh(h/2) dh`. This module defines the damped source
`e^(-h) Q_b(h)` (set to `0` for `h ≤ b`) and proves it is measurable and grows at most
linearly: `|e^(-h) Q_b(h)| ≤ (32/b² + 64/b³)(1 + h)` for all `h > 0`. The bound comes from
`|Q_b(h)| ≤ (32/b²) e^h + (64/b³) h e^(h/2)`.

## Main results

- `ccmThirdGradeDampedSource`: the damped source `h ↦ e^(-h) Q_b(h)` for `h > b`, else `0`.
- `measurable_ccmThirdGradeDampedSource`: it is measurable when `b > 0`.
- `ccmThirdGradeDampedSource_linearBound`: for `b > 0` and all `h > 0`,
  `|e^(-h) Q_b(h)| ≤ (32/b² + 64/b³)(1 + h)`.

## Hypotheses

Unconditional; the only premise is `0 < b`. The bound uses the elementary window estimates
for the prime and polar third-grade rates; it involves no information about zeta zeros.
-/

open Set MeasureTheory
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- The exponentially damped third-grade source: `e^(-h)` times the prime-minus-polar cumulative
window `Q_b(h)` for `h > b`, and `0` for `h ≤ b`. -/
def ccmThirdGradeDampedSource (b h : ℝ) : ℝ :=
  if b < h then Real.exp (-h) * ccmGuinandWeilThirdGradeCumulativeMeasurable b h else 0

/-- For `b > 0` the damped third-grade source is a measurable function of `h`. -/
theorem measurable_ccmThirdGradeDampedSource {b : ℝ} (hb : 0 < b) :
    Measurable (ccmThirdGradeDampedSource b) := by
  unfold ccmThirdGradeDampedSource
  exact Measurable.ite measurableSet_Ioi
    ((Real.measurable_exp.comp measurable_id.neg).mul
      (measurable_ccmGuinandWeilThirdGradeCumulativeMeasurable hb))
    measurable_const

/-- Assuming `b > 0`, the damped third-grade source has a linear envelope:
`|e^(-h) Q_b(h)| ≤ (32/b² + 64/b³)(1 + h)` for every `h > 0`. -/
theorem ccmThirdGradeDampedSource_linearBound {b : ℝ} (hb : 0 < b) :
    ∀ h : ℝ, 0 < h →
      |ccmThirdGradeDampedSource b h| ≤
        (32 / b ^ (2 : ℕ) + 64 / b ^ (3 : ℕ)) * (1 + h) := by
  intro h hh
  by_cases hbh : b < h
  · have hp0 := ccmGuinandWeilPrimeThirdGradeRateWindow_nonneg (b := b) (H := h)
    have hr0 := ccmGuinandWeilPolarThirdGradeRateWindow_nonneg hb hbh.le
    have hp := ccmGuinandWeilPrimeThirdGradeRateWindow_le hb h
    have hr := ccmGuinandWeilPolarThirdGradeRateWindow_le hb hbh.le
    have hq : |ccmGuinandWeilThirdGradeCumulativeMeasurable b h| ≤
        (32 / b ^ (2 : ℕ)) * Real.exp h +
          (64 / b ^ (3 : ℕ)) * h * Real.exp (h / 2) := by
      rw [ccmGuinandWeilThirdGradeCumulativeMeasurable_eq_primePolar hbh.le,
        ccmGuinandWeilPrimePolarWeightedWindow_thirdGrade_eq_prime_sub_polar]
      calc
        |_ - _| ≤ |ccmGuinandWeilPrimeThirdGradeRateWindow b h| +
          |ccmGuinandWeilPolarThirdGradeRateWindow b h| := abs_sub _ _
        _ = _ := by rw [abs_of_nonneg hp0, abs_of_nonneg hr0]
        _ ≤ _ := add_le_add hp hr
    have hehalf : Real.exp (h / 2) ≤ Real.exp h :=
      Real.exp_le_exp.mpr (by linarith)
    have hC2 : 0 ≤ 32 / b ^ (2 : ℕ) := by positivity
    have hC3 : 0 ≤ 64 / b ^ (3 : ℕ) := by positivity
    have hbound : |ccmGuinandWeilThirdGradeCumulativeMeasurable b h| ≤
        (32 / b ^ (2 : ℕ) + 64 / b ^ (3 : ℕ) * h) * Real.exp h := by
      calc
        _ ≤ (32 / b ^ (2 : ℕ)) * Real.exp h +
              (64 / b ^ (3 : ℕ)) * h * Real.exp (h / 2) := hq
        _ ≤ (32 / b ^ (2 : ℕ)) * Real.exp h +
              (64 / b ^ (3 : ℕ)) * h * Real.exp h := by
                gcongr
        _ = _ := by ring
    have hC : 0 ≤ 32 / b ^ (2 : ℕ) + 64 / b ^ (3 : ℕ) := by positivity
    have hlin : 32 / b ^ (2 : ℕ) + 64 / b ^ (3 : ℕ) * h ≤
        (32 / b ^ (2 : ℕ) + 64 / b ^ (3 : ℕ)) * (1 + h) := by
      nlinarith [mul_nonneg hC2 hh.le]
    unfold ccmThirdGradeDampedSource
    rw [if_pos hbh, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hmul := mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg (-h))
    calc
      Real.exp (-h) * |ccmGuinandWeilThirdGradeCumulativeMeasurable b h| ≤
          Real.exp (-h) *
            ((32 / b ^ (2 : ℕ) + 64 / b ^ (3 : ℕ) * h) * Real.exp h) := hmul
      _ = 32 / b ^ (2 : ℕ) + 64 / b ^ (3 : ℕ) * h := by
            rw [show Real.exp (-h) *
              ((32 / b ^ (2 : ℕ) + 64 / b ^ (3 : ℕ) * h) * Real.exp h) =
              (32 / b ^ (2 : ℕ) + 64 / b ^ (3 : ℕ) * h) *
                (Real.exp (-h) * Real.exp h) by ring, ← Real.exp_add]
            simp
      _ ≤ _ := hlin
  · simp [ccmThirdGradeDampedSource, hbh]
    positivity

end

end RHTower
