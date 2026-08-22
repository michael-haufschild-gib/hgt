import GaloisForLFunctions.RHTower.FiniteEulerGammaReflectionWeld
import GaloisForLFunctions.RHTower.SemilocalDualPairEulerConnection

/-!
# Finite Euler--Gamma connection bridge

The entire Euler factor used in the reciprocal-Gamma weld is definitionally
the standard inverse local Euler factor.  Its logarithmic connection therefore
inherits the existing exact Euler source formula.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Complex

/-- The entire factor in the Gamma weld is the standard inverse local Euler factor. -/
theorem finiteEulerLocalFactor_eq_eulerLocalInverse (p : Nat.Primes) (s : ℂ) :
    finiteEulerLocalFactor p s = _root_.RHTower.eulerLocalInverse p s := by
  rw [finiteEulerLocalFactor_eq_one_sub_natCast_cpow]
  rfl

/-- The finite Euler factor is entire with the explicit prime-log exponential derivative. -/
theorem hasDerivAt_finiteEulerLocalFactor (p : Nat.Primes) (s : ℂ) :
    HasDerivAt (finiteEulerLocalFactor p)
      ((Real.log p : ℂ) * Complex.exp (-s * (Real.log p : ℂ))) s := by
  have hfun : finiteEulerLocalFactor (p : ℕ) = _root_.RHTower.eulerLocalInverse (p : ℕ) :=
    funext fun z => finiteEulerLocalFactor_eq_eulerLocalInverse p z
  rw [hfun]
  convert _root_.RHTower.hasDerivAt_eulerLocalInverse p.property.two_le s using 1
  rw [_root_.RHTower.primePow_eq_exp p.property.two_le, neg_mul]

/-- The ordinary derivative form of the finite Euler entire-factor identity. -/
theorem deriv_finiteEulerLocalFactor (p : Nat.Primes) (s : ℂ) :
    deriv (finiteEulerLocalFactor p) s =
      (Real.log p : ℂ) * Complex.exp (-s * (Real.log p : ℂ)) :=
  (hasDerivAt_finiteEulerLocalFactor p s).deriv

/-- The exact derivative of the functional-equation-symmetric finite Euler quartet. -/
theorem hasDerivAt_finiteEulerLocalQuartet (p : Nat.Primes) (s : ℂ) :
    HasDerivAt (finiteEulerLocalQuartet p)
      ((Real.log p : ℂ) * Complex.exp (-s * (Real.log p : ℂ)) *
          finiteEulerLocalFactor p (1 - s) -
        finiteEulerLocalFactor p s * (Real.log p : ℂ) *
          Complex.exp (-(1 - s) * (Real.log p : ℂ))) s := by
  have hfirst := hasDerivAt_finiteEulerLocalFactor p s
  have hshift : HasDerivAt (fun z : ℂ => 1 - z) (-1) s :=
    (hasDerivAt_id s).const_sub (1 : ℂ)
  have hsecond : HasDerivAt (fun z : ℂ => finiteEulerLocalFactor p (1 - z))
      ((Real.log p : ℂ) * Complex.exp (-(1 - s) * (Real.log p : ℂ)) * -1) s :=
    (hasDerivAt_finiteEulerLocalFactor p (1 - s)).comp s hshift
  have hval : (Real.log p : ℂ) * Complex.exp (-s * (Real.log p : ℂ)) *
        finiteEulerLocalFactor p (1 - s) -
      finiteEulerLocalFactor p s * (Real.log p : ℂ) *
        Complex.exp (-(1 - s) * (Real.log p : ℂ))
      = (Real.log p : ℂ) * Complex.exp (-s * (Real.log p : ℂ)) *
          finiteEulerLocalFactor p (1 - s) +
        finiteEulerLocalFactor p s *
          ((Real.log p : ℂ) * Complex.exp (-(1 - s) * (Real.log p : ℂ)) * -1) := by
    ring
  rw [hval]
  exact hfirst.mul hsecond

/-- The ordinary derivative form of the finite Euler quartet identity. -/
theorem deriv_finiteEulerLocalQuartet (p : Nat.Primes) (s : ℂ) :
    deriv (finiteEulerLocalQuartet p) s =
      (Real.log p : ℂ) * Complex.exp (-s * (Real.log p : ℂ)) *
          finiteEulerLocalFactor p (1 - s) -
        finiteEulerLocalFactor p s * (Real.log p : ℂ) *
          Complex.exp (-(1 - s) * (Real.log p : ℂ)) :=
  (hasDerivAt_finiteEulerLocalQuartet p s).deriv

/-- The logarithmic connection of the Gamma-welded Euler factor is the exact prime source. -/
theorem logDeriv_finiteEulerLocalFactor (p : Nat.Primes) (s : ℂ) :
    logDeriv (finiteEulerLocalFactor p) s = _root_.RHTower.primeLogSource p s := by
  have hfactor : finiteEulerLocalFactor p = _root_.RHTower.eulerLocalInverse p := by
    funext z
    exact finiteEulerLocalFactor_eq_eulerLocalInverse p z
  rw [hfactor]
  exact _root_.RHTower.logDeriv_eulerLocalInverse p.property.two_le s

end GaloisForLFunctions.RHTower

end
