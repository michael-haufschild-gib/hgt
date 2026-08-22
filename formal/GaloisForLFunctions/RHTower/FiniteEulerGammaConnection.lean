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
