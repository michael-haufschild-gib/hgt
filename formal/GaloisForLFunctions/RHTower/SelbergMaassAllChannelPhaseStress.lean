import GaloisForLFunctions.RHTower.SelbergMaassAllChannelLoss
import GaloisForLFunctions.RHTower.SelbergMaassCharacterSeamFlux

/-!
# Full-channel collapse of the Maass phase stress

For an exceptional source, each selected phase channel has zero unweighted
mixed mean. Summing every input/output channel does not orient the remaining
coordinate-weighted term: it removes the finite transfer and leaves the
ordinary signed horizontal--vertical derivative pairing of the full congruence
vector. Thus an all-channel average cannot supply the missing sign in the
Selberg boundary identity.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open scoped BigOperators ContDiff
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage
open SelbergMaassCharacterSeamFlux SelbergMaassPhaseStress

noncomputable section

/-- Summing the physical mixed phase stress over every finite character channel
removes the inversion transfer and leaves the ordinary signed derivative
pairing of the complete congruence vector. -/
theorem allChannel_phaseStressXY_sum (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (z : ℍ) :
    (∑ r : ZMod (N + 1), ∑ s : ZMod (N + 1),
      phaseStressXY N r s f (z : ℂ)) =
      2 * (((N + 1 : ℕ) : ℝ) ^ (2 : ℕ) - 1) *
        (inner ℂ (sourceDerivative N f 1 z)
          (sourceDerivative N f Complex.I z)).re := by
  simp_rw [phaseStressXY_eq]
  calc
    _ = ∑ r : ZMod (N + 1), 2 * ∑ s : ZMod (N + 1),
        lossPair N r s (sourceDerivative N f 1 z)
          (sourceDerivative N f Complex.I z) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
    _ = 2 * ∑ r : ZMod (N + 1), ∑ s : ZMod (N + 1),
        lossPair N r s (sourceDerivative N f 1 z)
          (sourceDerivative N f Complex.I z) := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [allChannel_lossPair_sum]
      ring

end
end GaloisForLFunctions.RHTower
