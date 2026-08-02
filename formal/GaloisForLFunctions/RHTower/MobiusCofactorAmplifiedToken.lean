import GaloisForLFunctions.RHTower.MobiusMultiplicativeRectangleCubature

/-!
# Cofactor-amplified opposite-parity Möbius tokens

A squarefree cofactor family can amplify one balanced exact-three-prime token family without
losing the near-square-root displacement exponent.  This file proves the exact parity and
gap-scaling consumers.  The analytic supply and local Hall expansion remain separate arithmetic
inputs.
-/

namespace RHTower

/-- If a coprime cofactor has the source block's Möbius parity and the supplied exact-almost-prime
token has coefficient `-1`, their product reverses the source parity. -/
theorem mobiusCofactorToken_reverses
    {u t m : ℕ}
    (htm : t.Coprime m)
    (ht : mobiusComplexCoefficient t = mobiusComplexCoefficient u)
    (hm : mobiusComplexCoefficient m = -(1 : ℂ)) :
    mobiusComplexCoefficient (t * m) = -mobiusComplexCoefficient u := by
  rw [mobiusComplexCoefficient_mul_of_coprime htm, ht, hm]
  ring

/-- Multiplying a token interval by a nonnegative cofactor scales its displacement by exactly that
cofactor.  Applied at center `y = u/t`, this turns a square-root gap into `sqrt (u*t)`. -/
theorem abs_cofactor_scaled_gap_le
    {t y m h : ℝ} (ht : 0 ≤ t) (hm : |m - y| ≤ h) :
    |t * m - t * y| ≤ t * h := by
  rw [← mul_sub, abs_mul, abs_of_nonneg ht]
  exact mul_le_mul_of_nonneg_left hm ht

/-- Pairing an odd cofactor `s` with `2 * s` gives the opposite Möbius parity.  This supplies
both cofactor parity classes in the multiband construction without assuming cancellation in a
signed cofactor sum. -/
theorem mobiusCofactorPair_two_reverses
    {s : ℕ} (hs : Nat.Coprime 2 s) :
    mobiusComplexCoefficient (2 * s) = -mobiusComplexCoefficient s := by
  rw [mobiusComplexCoefficient_mul_of_coprime hs,
    mobiusComplexCoefficient_prime Nat.prime_two]
  ring

end RHTower
