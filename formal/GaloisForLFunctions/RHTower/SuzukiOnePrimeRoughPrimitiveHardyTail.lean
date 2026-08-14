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

end GaloisForLFunctions.RHTower
