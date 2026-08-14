import GaloisForLFunctions.RHTower.SuzukiPolynomialCarrierGammaDimensionWall
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# One-prime rough-primitive Hardy tail

After three integrations by parts, polynomial transport of degree `κ` leaves two squared
frequency-tail majorants.  The far-end term has exponent `2(κ-(1/2+σ))`; the near-diagonal
remainder has exponent `2(κ+1-N)`, where `N` is the integration-by-parts depth.  This module
proves their exact joint integrability window and certifies that the one-prime choice
`(κ, σ, N) = (2/3, 3/4, 3)` lies strictly inside it.
-/

open Filter MeasureTheory
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Squared far-end tail after polynomial transport meets the slow Gamma channel. -/
def suzukiPolynomialIBPFarTailNormSq (κ σ x : ℝ) : ℝ :=
  x ^ (2 * (κ - (1 / 2 + σ)))

/-- Squared near-diagonal remainder after `N` frequency integrations by parts. -/
def suzukiPolynomialIBPNearTailNormSq (κ N x : ℝ) : ℝ :=
  x ^ (2 * (κ + 1 - N))

/-- The far-end tail is integrable exactly below the Gamma height. -/
theorem integrableAtTop_suzukiPolynomialIBPFarTailNormSq_iff (κ σ : ℝ) :
    IntegrableAtFilter (suzukiPolynomialIBPFarTailNormSq κ σ) atTop volume ↔ κ < σ := by
  change IntegrableAtFilter (fun x : ℝ => x ^ (2 * (κ - (1 / 2 + σ)))) atTop volume ↔ κ < σ
  rw [integrableAtFilter_rpow_atTop_iff]
  constructor <;> intro h <;> linarith

/-- The near-diagonal remainder is integrable exactly past depth `κ + 3/2`. -/
theorem integrableAtTop_suzukiPolynomialIBPNearTailNormSq_iff (κ N : ℝ) :
    IntegrableAtFilter (suzukiPolynomialIBPNearTailNormSq κ N) atTop volume ↔
      κ + 3 / 2 < N := by
  change IntegrableAtFilter (fun x : ℝ => x ^ (2 * (κ + 1 - N))) atTop volume ↔
    κ + 3 / 2 < N
  rw [integrableAtFilter_rpow_atTop_iff]
  constructor <;> intro h <;> linarith

/-- Exact joint window for the two integration-by-parts tails. -/
theorem integrableAtTop_suzukiPolynomialIBPTails_iff (κ σ N : ℝ) :
    (IntegrableAtFilter (suzukiPolynomialIBPFarTailNormSq κ σ) atTop volume ∧
      IntegrableAtFilter (suzukiPolynomialIBPNearTailNormSq κ N) atTop volume) ↔
      κ < σ ∧ κ + 3 / 2 < N := by
  rw [integrableAtTop_suzukiPolynomialIBPFarTailNormSq_iff,
    integrableAtTop_suzukiPolynomialIBPNearTailNormSq_iff]

/-- The concrete one-prime carrier needs exactly three integrations by parts. -/
theorem suzukiOnePrimeThirdIBPTails :
    IntegrableAtFilter (suzukiPolynomialIBPFarTailNormSq (2 / 3) (3 / 4)) atTop volume ∧
    IntegrableAtFilter (suzukiPolynomialIBPNearTailNormSq (2 / 3) 3) atTop volume := by
  rw [integrableAtTop_suzukiPolynomialIBPTails_iff]
  norm_num

/-- Backward geometric convolution of a nonnegative block envelope.  This is the discrete
primitive operator produced by integrating a terminally supported exponential block tail. -/
def suzukiBackwardGeometricBlockEnvelope
    (q : ℝ≥0∞) (h : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑' j : ℕ, q ^ j * h (n + j)

/-- Sharp global mass bound for the backward block primitive.  No summability assumption is
needed: the statement remains valid in `ℝ≥0∞` at infinite mass. -/
theorem tsum_suzukiBackwardGeometricBlockEnvelope_le
    (q : ℝ≥0∞) (h : ℕ → ℝ≥0∞) :
    ∑' n : ℕ, suzukiBackwardGeometricBlockEnvelope q h n ≤
      (1 - q)⁻¹ * ∑' n : ℕ, h n := by
  unfold suzukiBackwardGeometricBlockEnvelope
  rw [ENNReal.tsum_comm]
  calc
    (∑' j : ℕ, ∑' n : ℕ, q ^ j * h (n + j)) =
        ∑' j : ℕ, q ^ j * ∑' n : ℕ, h (n + j) := by
      congr 1
      funext j
      exact ENNReal.tsum_mul_left
    _ ≤ ∑' j : ℕ, q ^ j * ∑' n : ℕ, h n := by
      apply ENNReal.tsum_le_tsum
      intro j
      have htail : (∑' n : ℕ, h (n + j)) ≤ ∑' n : ℕ, h n :=
        ENNReal.tsum_comp_le_tsum_of_injective (f := fun n : ℕ => n + j)
          (fun _ _ hEq => Nat.add_right_cancel hEq) h
      simpa [mul_comm] using mul_le_mul_right htail (q ^ j)
    _ = (1 - q)⁻¹ * ∑' n : ℕ, h n := by
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]

/-- A finite block envelope remains finite under every strict backward geometric contraction. -/
theorem tsum_suzukiBackwardGeometricBlockEnvelope_lt_top
    (q : ℝ≥0∞) (h : ℕ → ℝ≥0∞) (hq : q < 1) (hh : ∑' n : ℕ, h n < ⊤) :
    ∑' n : ℕ, suzukiBackwardGeometricBlockEnvelope q h n < ⊤ :=
  lt_of_le_of_lt (tsum_suzukiBackwardGeometricBlockEnvelope_le q h)
    (ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (tsub_pos_iff_lt.2 hq)) hh)

end GaloisForLFunctions.RHTower
