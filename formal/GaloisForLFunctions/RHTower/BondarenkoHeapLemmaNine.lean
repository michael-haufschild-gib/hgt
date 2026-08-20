/-
# Bondarenko--Heap Lemma 9: prime-local exceptional factor

For a prime factor where the source character `ψ_p` equals the quadratic
character `χ_p`, Lemma 9 identifies the local generalized Jacobi sum with the
Ramanujan factor `p - 1` at zero and `-1` away from zero.  This module proves
that exact finite-field factor and transports its zero branch through the
source inverse-incidence shift `r m⁻¹`.
-/
import GaloisForLFunctions.RHTower.BondarenkoHeapLemmaSeven
import GaloisForLFunctions.RHTower.QuadraticJacobiSum

open scoped BigOperators

noncomputable section

namespace RHTower

/-- The exact prime-local exceptional factor in Lemma 9. -/
def oddPrimeQuadraticRamanujanLocalSum
    (p : OddPrime) (y : ZMod p.1) : ℂ :=
  ∑ u : ZMod p.1,
    oddPrimeQuadraticCharacter p (u + y) * oddPrimeQuadraticCharacter p u

/-- At a certified odd prime, the quadratic local factor is the prime
Ramanujan sum: `p - 1` at the zero residue and `-1` at every other residue. -/
theorem oddPrime_quadraticRamanujanLocalSum
    (p : OddPrime) (y : ZMod p.1) :
    oddPrimeQuadraticRamanujanLocalSum p y =
      if y = 0 then (p.1 : ℂ) - 1 else -1 := by
  simpa [oddPrimeQuadraticRamanujanLocalSum] using
    oddPrime_quadratic_shiftCorrelation p y 0

/-- The same local factor at the source shift `r m⁻¹`; its zero branch is
exactly the zero branch of `r`, because the denominator is explicit unit data. -/
theorem oddPrime_quadraticRamanujanLocalSum_unitInverse
    (p : OddPrime) (r : ZMod p.1) (m : (ZMod p.1)ˣ) :
    oddPrimeQuadraticRamanujanLocalSum p (unitInverseIncidenceClass p.1 r m) =
      if r = 0 then (p.1 : ℂ) - 1 else -1 := by
  rw [oddPrime_quadraticRamanujanLocalSum]
  simp only [unitInverseIncidenceClass_eq_zero_iff]

end RHTower
