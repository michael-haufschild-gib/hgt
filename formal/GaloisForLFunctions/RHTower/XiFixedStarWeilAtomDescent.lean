import GaloisForLFunctions.RHTower.XiWeilSameFiberAtomIsotropy
import GaloisForLFunctions.RHTower.XiSelectedBilateralPositiveSourceReceiver

/-!
# Same-fibre CCM atom energy and prime-Gamma fixed-star descent

The unconditional CCM/Weil form sees a single multiplicity-exact Xi coordinate as isotropic away
from the critical-reflection fixed locus.  The source-derived prime-Gamma character has literal
Hilbert-star equals source-inverse exactly on that same locus.  This file identifies the two local
conditions without discarding the Xi copy or prime label.

The equivalence is an exact cross-corpus reduction, not the missing producer: proving either side
for every retained Xi copy is RH-strength.
-/

open Complex

namespace RHTower

noncomputable section

/-- The prime-Gamma same-fibre fixed-star equation and unit CCM atom energy are the same local
critical-line condition.  Xi multiplicity-copy and ordinary-prime labels remain explicit. -/
theorem xiWeilCoordinateAtom_unitPairing_iff_primeGammaFixedStarDescends
    (q : XiZeroCopy) (p : Nat.Primes) :
    xiWeilCliffordPairing (xiWeilCoordinateAtom q 1)
        (xiWeilCoordinateAtom q 1) = 1 ↔
      DeningerMeyerXiPrimeGammaFixedStarDescendsAt q.1 p := by
  rw [xiWeilCliffordPairing_coordinateAtom_one_eq_one_iff_re_eq_half,
    deningerMeyerXiPrimeGammaFixedStarDescendsAt_iff_norm_eq_one,
    deningerMeyerXiPrimeGammaCharacter_eq_deltaS,
    norm_deltaS_eq_one_iff p.2.two_le]

end

end RHTower
