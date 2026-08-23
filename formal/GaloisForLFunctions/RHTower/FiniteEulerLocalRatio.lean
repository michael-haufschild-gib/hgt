import GaloisForLFunctions.RHTower.FiniteEulerLocalQuartet

/-!
# Finite reflected Euler local ratios

The ordinary finite-place ratio is the quotient of a reflected Euler factor
by its original factor.  This file records its exact Euler-power formula,
reflection inverse law, and the fixed-point identity at `s = 1/2`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Complex

/-- The reflected ratio of one finite zeta Euler factor. -/
def finiteEulerLocalRatio (p : Nat.Primes) (s : ℂ) : ℂ :=
  finiteEulerLocalFactor p (1 - s) / finiteEulerLocalFactor p s

/-- The finite local ratio has the classical Euler-power expression. -/
theorem finiteEulerLocalRatio_eq_cpow (p : Nat.Primes) (s : ℂ) :
    finiteEulerLocalRatio p s =
      (1 - ((p : ℕ) : ℂ) ^ (s - 1)) / (1 - ((p : ℕ) : ℂ) ^ (-s)) := by
  unfold finiteEulerLocalRatio
  rw [finiteEulerLocalFactor_eq_one_sub_natCast_cpow p (1 - s),
    finiteEulerLocalFactor_eq_one_sub_natCast_cpow p s]
  congr 3
  ring

/-- Reflection sends a local ratio to its multiplicative inverse. -/
theorem finiteEulerLocalRatio_reflection (p : Nat.Primes) (s : ℂ) :
    finiteEulerLocalRatio p (1 - s) = (finiteEulerLocalRatio p s)⁻¹ := by
  unfold finiteEulerLocalRatio
  rw [sub_sub_cancel]
  exact (inv_div _ _).symm

/-- At the unique reflection fixed point, every finite local ratio is one. -/
theorem finiteEulerLocalRatio_half (p : Nat.Primes) :
    finiteEulerLocalRatio p (1 / 2) = 1 := by
  unfold finiteEulerLocalRatio
  have hline : (1 - (1 / 2 : ℂ) : ℂ) = 1 / 2 := by norm_num
  rw [hline, div_self]
  convert finiteEulerLocalFactor_criticalLine_ne_zero p 0 using 1
  norm_num

end GaloisForLFunctions.RHTower

end
