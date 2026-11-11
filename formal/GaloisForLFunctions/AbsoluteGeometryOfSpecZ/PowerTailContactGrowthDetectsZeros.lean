import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailReferenceRemainder

/-!
# Growth of centered power contacts detects the zero half-plane

The contact convolution splits into the weighted prime error and an
elementary reference term. Weighted Möbius inversion preserves its strict
growth exponent, and removal of the coefficient power recovers the
Chebyshev error. The resulting half-plane criterion is an equivalence.
-/

noncomputable section

open ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- Arithmetic contact coefficient with its leading pole removed. -/
def powerTailCenteredContact (a : ℝ) : ArithmeticFunction ℝ :=
  powerTailZeta (2 * a) * powerTailTwist a ArithmeticFunction.vonMangoldt -
    powerTailPole a • powerTailZeta a

/-- The weighted prime error, with value zero at the arithmetic zero index. -/
def powerTailPrimeDeviation (a : ℝ) : ArithmeticFunction ℝ :=
  powerTailTwist a (ArithmeticFunction.vonMangoldt - (ζ : ArithmeticFunction ℝ))

theorem powerTailCenteredContact_apply (a : ℝ) {n : ℕ} (hn : n ≠ 0) :
    powerTailCenteredContact a n =
      powerTailContactCoefficient a n - powerTailPole a * powerTailWeight a n := by
  change (powerTailZeta (2 * a) * powerTailTwist a ArithmeticFunction.vonMangoldt) n -
    powerTailPole a * powerTailZeta a n = _
  rw [← powerTailContactCoefficient_eq_convolution, powerTailZeta_apply hn]

/-- The reference term carries precisely the difference between pole subtraction
and convolution with the constant arithmetic coefficient. -/
theorem powerTailCenteredContact_eq (a : ℝ) :
    powerTailCenteredContact a =
      powerTailZeta (2 * a) * powerTailPrimeDeviation a + powerTailReference a := by
  rw [powerTailCenteredContact, powerTailPrimeDeviation, map_sub, mul_sub,
    powerTailReference]
  change _ = _ - powerTailZeta (2 * a) * powerTailZeta a + _
  abel

/-- Centered contacts and weighted prime error have exactly the same strict
growth threshold above the reference exponent. -/
theorem partialSumPowerBound_centeredContact_iff_primeDeviation {a σ : ℝ}
    (ha : 0 < a) (ha2 : a < 1 / 2) (hσ : 0 ≤ σ) :
    RHTower.PartialSumPowerBound (fun n => powerTailCenteredContact a (n + 1)) (1 - 2 * a + σ) ↔
      RHTower.PartialSumPowerBound (fun n => powerTailPrimeDeviation a (n + 1)) (1 - 2 * a + σ) := by
  have hθ : 0 ≤ 1 - 2 * a + σ := by linarith only [ha2, hσ]
  have href := (partialSumPowerBound_powerTailReference ha ha2).mono
    (show 1 - 2 * a ≤ 1 - 2 * a + σ by linarith only [hσ])
  have hc := partialSumPowerBound_powerTailZeta_mul_iff (2 * a) (1 - 2 * a + σ)
    hθ (by linarith only [hσ]) (powerTailPrimeDeviation a)
  have he : (fun n => powerTailCenteredContact a (n + 1) - powerTailReference a (n + 1)) =
      (fun n => (powerTailZeta (2 * a) * powerTailPrimeDeviation a) (n + 1)) := by
    funext n
    rw [powerTailCenteredContact_eq, ArithmeticFunction.add_apply, add_sub_cancel_right]
  constructor
  · intro h
    apply hc.mp
    simpa only [he] using h.sub href
  · intro h
    have hh := (hc.mpr h).add href
    simpa only [powerTailCenteredContact_eq, ArithmeticFunction.add_apply] using hh

/-- Removing the weight gives the ordinary Chebyshev growth exponent. -/
theorem partialSumPowerBound_centeredContact_iff_primeError {a σ : ℝ}
    (ha : 0 < a) (ha2 : a < 1 / 2) (hσ : 0 ≤ σ) :
    RHTower.PartialSumPowerBound (fun n => powerTailCenteredContact a (n + 1)) (1 - 2 * a + σ) ↔
      RHTower.PartialSumPowerBound RHTower.vonMangoldtMinusOne (1 - a + σ) := by
  rw [partialSumPowerBound_centeredContact_iff_primeDeviation ha ha2 hσ]
  have h := partialSumPowerBound_powerTailTwist_iff
    (ArithmeticFunction.vonMangoldt - (ζ : ArithmeticFunction ℝ)) a (1 - a + σ)
    (by linarith only [ha2, hσ]) (by linarith only [ha2, hσ])
  have he : (fun n => (ArithmeticFunction.vonMangoldt - (ζ : ArithmeticFunction ℝ)) (n + 1)) =
      RHTower.vonMangoldtMinusOne := by
    funext n
    change ArithmeticFunction.vonMangoldt (n + 1) - (ζ : ArithmeticFunction ℝ) (n + 1) =
      ArithmeticFunction.vonMangoldt (n + 1) - 1
    simp
  simpa only [show 1 - a + σ - a = 1 - 2 * a + σ by ring,
    powerTailPrimeDeviation, he] using h

/-- The centered contact growth exponent detects exactly the rightmost zero
half-plane, without any zero-free hypothesis. -/
theorem partialSumPowerBound_centeredContact_iff_zeroHalfPlane {a σ : ℝ}
    (ha : 0 < a) (ha2 : a < 1 / 2) (hσ : 0 ≤ σ) :
    RHTower.PartialSumPowerBound (fun n => powerTailCenteredContact a (n + 1)) (1 - 2 * a + σ) ↔
      RHTower.XiZeroHalfPlaneBound (1 / 2 - a + σ) := by
  rw [partialSumPowerBound_centeredContact_iff_primeError ha ha2 hσ,
    RHTower.partialSumPowerBound_iff_convergesRightOf _ (by linarith only [ha2, hσ])]
  have h := RHTower.xiZeroHalfPlaneBound_iff_vonMangoldtMinusOne_converges
    (show 0 ≤ 1 / 2 - a + σ by linarith only [ha2, hσ])
  simpa only [RHTower.ConvergesRightOf,
    show 1 / 2 + (1 / 2 - a + σ) = 1 - a + σ by ring] using h.symm

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
