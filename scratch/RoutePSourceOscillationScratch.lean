import GaloisForLFunctions.RHTower.CriticalChebyshevBoostChargeInjection
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem
import GaloisForLFunctions.RHTower.CCMUnitRieszCausalLaplaceBridge

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- Meromorphic continuation candidate for the literal unit-Riesz source transform. -/
def routePSourceLaplaceContinuation (z : ℂ) : ℂ :=
  (criticalNormalizedChebyshevErrorContinuation z - 2 / 3) / (z + 1)

private theorem boost_eq_sourceContinuation
    {z : ℂ} (hzhalf : z + 1 / 2 ≠ 0) (hzone : z + 1 ≠ 0) :
    criticalChebyshevBoostCurrent z =
      z * ((z + 1 / 2) *
        ((z + 1) * routePSourceLaplaceContinuation z + 2 / 3) + 1) := by
  rw [routePSourceLaplaceContinuation,
    criticalChebyshevBoostCurrent_eq_continuationAffine hzhalf]
  field_simp [hzone]
  ring

end RHTower
