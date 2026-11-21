import GaloisForLFunctions.RHTower.EulerUnitTangent
import GaloisForLFunctions.RHTower.VisibleCoprimeDirichletZeroJet
import GaloisForLFunctions.WindowedLandauTheory.LandauZeroFreeBounds.NoZeroComplexOf

/-! The principal character's Euler factors and the conjugation law for real characters. -/

open Complex DirichletCharacter

namespace WindowedLandauTheory.ZeroFreeDirichlet

theorem trivialCharZerosOfZeta : TrivZeros := by
  intro q _ s h₀ h₁ hz
  change LFunctionTrivChar q s = 0 at hz
  rw [LFunctionTrivChar_eq_mul_riemannZeta h₁] at hz
  exact (mul_eq_zero.mp hz).resolve_left (Finset.prod_ne_zero_iff.mpr fun p hp =>
    RHTower.one_sub_prime_cpow_neg_ne_zero (Nat.prime_of_mem_primeFactors hp).two_le h₀)

theorem realCharConj : RealConj := by
  intro q _ χ hsq hχ s
  have hinv : χ⁻¹ = χ := inv_eq_of_mul_eq_one_right (by rwa [← pow_two])
  simpa only [hinv] using RHTower.LFunction_inv_conj χ hχ s

end WindowedLandauTheory.ZeroFreeDirichlet
