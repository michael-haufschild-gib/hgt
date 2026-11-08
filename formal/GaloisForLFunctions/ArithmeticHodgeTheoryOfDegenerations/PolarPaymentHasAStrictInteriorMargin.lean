import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheLowPacketPaymentAtEveryRatioIsTheRiemannHypothesis

/-!
# Polar payment has a strict interior margin

Decreasing the critical ratio adds two positive diagonal reserves: the eighth
exponential mass of the window and the scalar pole coordinate square.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticDegenerationTheory
  RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis WindowTowerOfSpecZ

/-- The ratio-independent polar genus cancels when comparing two pole costs. -/
theorem criticalPoleWindowCost_sub_eq {R S : ℝ} (hR : R ≠ 0) (hS : S ≠ 0) :
    criticalPoleWindowCost R - criticalPoleWindowCost S =
      jordanCoefficient 1 * (1 / R - 1 / S) := by
  unfold criticalPoleWindowCost criticalGenusCoefficient
  field_simp [hR, hS]
  ring

/-- Polar capacity is exactly the nonnegativity of every scalar pole correction. -/
theorem charged_window_nonneg_of_polarPaymentAt {R A : ℝ} (hR : 0 < R)
    (hpay : PolarPaymentAt R A) {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (t : ℝ) :
    0 ≤ windowPencil R (halfWeight h) + 2 * t * generalTerminalPolarSource A h +
      t ^ 2 * criticalPoleWindowCost R := by
  have hD := criticalPoleWindowCost_pos hR
  have hp := hpay h hh hsupp
  calc
    0 ≤ (windowPencil R (halfWeight h) -
        generalTerminalPolarSource A h ^ 2 / criticalPoleWindowCost R) +
        (criticalPoleWindowCost R * t + generalTerminalPolarSource A h) ^ 2 /
          criticalPoleWindowCost R :=
      add_nonneg (sub_nonneg.mpr hp) (div_nonneg (sq_nonneg _) hD.le)
    _ = _ := by field_simp [hD.ne']; ring

/-- Payment at a larger ratio leaves explicit positive window and pole reserves at every smaller
positive ratio. -/
theorem charged_window_ge_ratio_gap {R S A : ℝ} (hR : 0 < R) (hRS : R < S)
    (hpay : PolarPaymentAt S A) {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (t : ℝ) :
    (1 / R - 1 / S) *
        (7 * tiltedJordanOne * exponentialMass 8 (halfWeight h) + jordanCoefficient 1 * t ^ 2) ≤
      windowPencil R (halfWeight h) + 2 * t * generalTerminalPolarSource A h +
        t ^ 2 * criticalPoleWindowCost R := by
  have hS := hR.trans hRS
  have hnonneg := charged_window_nonneg_of_polarPaymentAt hS hpay hh hsupp t
  have hcost := criticalPoleWindowCost_sub_eq hR.ne' hS.ne'
  have he : windowPencil R (halfWeight h) + 2 * t * generalTerminalPolarSource A h +
        t ^ 2 * criticalPoleWindowCost R =
      (windowPencil S (halfWeight h) + 2 * t * generalTerminalPolarSource A h +
        t ^ 2 * criticalPoleWindowCost S) +
      (1 / R - 1 / S) *
        (7 * tiltedJordanOne * exponentialMass 8 (halfWeight h) + jordanCoefficient 1 * t ^ 2) := by
    have hc : criticalPoleWindowCost R = criticalPoleWindowCost S +
        jordanCoefficient 1 * (1 / R - 1 / S) := by linarith only [hcost]
    rw [hc]
    unfold windowPencil
    ring
  rw [he]
  exact le_add_of_nonneg_left hnonneg

#print axioms charged_window_nonneg_of_polarPaymentAt
#print axioms charged_window_ge_ratio_gap
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
