import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.TwistPrim
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

/-! The Kronecker character of a negative prime discriminant. -/

open WindowedLandauTheory.HC WindowedLandauTheory.MainNotions

namespace QH

private theorem kron2_neg (d : ℕ) (hd : d % 4 = 3) :
    GlobalTheoryTheory.kron2 (-(d : ℤ)) = jacobiSym 2 d := by
  rw [jacobiSym.at_two (Nat.odd_iff.mpr (by omega)), ZMod.χ₈_nat_eq_if_mod_eight]
  unfold GlobalTheoryTheory.kron2
  split_ifs <;> omega

/-- Quadratic reciprocity, including the factor at two. -/
theorem chDir_eq_J (d n : ℕ) (hd : d % 4 = 3) (hn : 0 < n) :
    GlobalTheoryTheory.chDir d n = J d n := by
  unfold GlobalTheoryTheory.chDir GlobalTheoryTheory.kron GlobalTheoryTheory.kronSym J
  have hodd : n / 2 ^ n.factorization 2 % 2 = 1 := by
    have h := Nat.not_dvd_ordCompl Nat.prime_two hn.ne'
    omega
  rw [jacobi_neg_recip hd hodd, kron2_neg d hd, ← jacobiSym.pow_left, ← jacobiSym.mul_left]
  have hmul : ((n / 2 ^ n.factorization 2 : ℕ) : ℤ) * (2 : ℤ) ^ n.factorization 2 = n := by
    rw [mul_comm]
    exact_mod_cast Nat.ordProj_mul_ordCompl_eq_self n 2
  rw [hmul]

theorem oddPrimeQuadraticCharacter_induces_chDir (d : RHTower.OddPrime) (hd : d.1 % 4 = 3)
    (M : ℕ) (hM : M ≠ 1) :
    GlobalTheoryTheory.Induces (RHTower.oddPrimeQuadraticCharacter d) (GlobalTheoryTheory.chDir d.1) M := by
  refine ⟨RHTower.oddPrimeQuadraticCharacter_isPrimitive d, fun n hn => ?_⟩
  have hn₀ : 0 < n := by
    by_contra! h
    have hn' : n = 0 := by omega
    exact hM (Nat.coprime_zero_left.mp (hn' ▸ hn))
  rw [quadraticCharacter_eq_J, chDir_eq_J d.1 n hd hn₀]

end QH
