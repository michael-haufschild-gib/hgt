import GaloisForLFunctions.RHTower.MobiusKMSCentralClockExternalCoordinate
import GaloisForLFunctions.RHTower.HedenmalmSquarefreeFirstTraceExponentialContinuation

/-!
# Reflected first-trace source on the KMS central clock

The positive KMS ray is not an Euler-safe Möbius ray.  Its negative-frequency
reflection, however, is the strict-right source parameter `1 / 2 + eta`.
This file records the resulting source-faithful signed readout.  It is an exact
identity, not a finite KMS realization or a coercivity claim.
-/

open Complex

namespace RHTower

noncomputable section

/-- The signed, source-faithful central-clock readout obtained by reflecting the
strict-right first-prime-trace continuation. -/
def mobiusKMSReflectedFirstTraceSource (eta : ℝ) : ℂ :=
  I *
    (squarefreeFirstTraceContinuedCurrent ((1 / 2 + eta : ℝ) : ℂ) +
      xiPrimeLogHigherValuation ((1 / 2 + eta : ℝ) : ℂ) -
      logDeriv archFactor ((1 / 2 + eta : ℝ) : ℂ))

private theorem source_kmsCentralClock_eq_completedFlux (eta : ℝ) :
    continuedPrimeArchSourceRelativeTrace (I * (eta : ℂ)) =
      -I * completedPrimeGammaFlux ((1 / 2 - eta : ℝ) : ℂ) := by
  rw [continuedPrimeArchSourceRelativeTrace]
  have hsource : (1 / 2 : ℂ) + (I * (eta : ℂ)) * I =
      ((1 / 2 - eta : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> push_cast <;> ring
  rw [hsource]
  rfl

/-- Every central KMS point below the first pole has an exact signed source
readout through the strict-right first-prime trace and its higher-valuation and
archimedean countercurrents. -/
theorem continuedPrimeArchSourceRelativeTrace_kmsCentralClock_eq_reflectedFirstTrace
    {eta : ℝ} (heta : 0 < eta) (hetaHalf : eta < 1 / 2) :
    continuedPrimeArchSourceRelativeTrace (I * (eta : ℂ)) =
      mobiusKMSReflectedFirstTraceSource eta := by
  have hleft : riemannZeta (((1 / 2 - eta : ℝ) : ℂ)) ≠ 0 :=
    riemannZeta_real_strip_ne_zero (σ := 1 / 2 - eta)
      (by linarith) (by linarith)
  have hright : riemannZeta (((1 / 2 + eta : ℝ) : ℂ)) ≠ 0 :=
    riemannZeta_real_strip_ne_zero (σ := 1 / 2 + eta)
      (by linarith) (by linarith)
  have hrightRef : riemannZeta (1 - ((1 / 2 - eta : ℝ) : ℂ)) ≠ 0 := by
    convert hright using 1 <;> push_cast <;> ring
  have hflux : completedPrimeGammaFlux ((1 / 2 + eta : ℝ) : ℂ) =
      -completedPrimeGammaFlux ((1 / 2 - eta : ℝ) : ℂ) := by
    convert completedPrimeGammaFlux_one_sub_eq_neg
      (s := ((1 / 2 - eta : ℝ) : ℂ))
      ⟨by simp; linarith, by simp; linarith⟩ hleft hrightRef using 1 <;>
      push_cast <;> ring
  calc
    continuedPrimeArchSourceRelativeTrace (I * (eta : ℂ)) =
        -I * completedPrimeGammaFlux ((1 / 2 - eta : ℝ) : ℂ) :=
      source_kmsCentralClock_eq_completedFlux eta
    _ = I * completedPrimeGammaFlux ((1 / 2 + eta : ℝ) : ℂ) := by
      rw [hflux]
      ring
    _ = mobiusKMSReflectedFirstTraceSource eta := by
      rw [mobiusKMSReflectedFirstTraceSource,
        completedPrimeGammaFlux_eq_firstTrace_add_regular]

end

end RHTower
