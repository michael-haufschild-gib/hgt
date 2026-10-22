import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilClockCommutator
import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilExponentialClockAbelTransport

open Set MeasureTheory
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

def ccmThirdGradeDampedSource (b h : ℝ) : ℝ :=
  if b < h then Real.exp (-h) * ccmGuinandWeilThirdGradeCumulativeMeasurable b h else 0

theorem measurable_ccmThirdGradeDampedSource {b : ℝ} (hb : 0 < b) :
    Measurable (ccmThirdGradeDampedSource b) := by
  unfold ccmThirdGradeDampedSource
  exact Measurable.ite measurableSet_Ioi
    ((Real.measurable_exp.comp measurable_id.neg).mul
      (measurable_ccmGuinandWeilThirdGradeCumulativeMeasurable hb))
    measurable_const

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
