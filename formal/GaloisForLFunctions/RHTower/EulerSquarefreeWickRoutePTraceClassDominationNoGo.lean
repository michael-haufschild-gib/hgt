import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesCofinalChildTraceClass
import GaloisForLFunctions.RHTower.XiReflectionIncidenceTraceOneSourceConvergence

/-!
# EWQ versus Route-P trace-class domination

The literal Route-P cofinal child is positive and trace class at every positive aperture.  Its
prime diagonal therefore offers a tempting source envelope for the coefficient-faithful EWQ/Xi
trace-one residue mass.  This module proves the sharp obstruction: such a pointwise envelope can
exist only at neutral horizontal grade.

The reason is structural rather than a missing estimate.  Route-P aperture transport moves its
diagonal strictly inside the trace-class chamber, whereas the off-line Gamma Bockstein remains on
the wrong side of the first-trace wall.  The second theorem retains the actual Xi multiplicity,
first nonzero Xi jet, ordinary-prime label, and paracyclic source residue.  Thus a positive
Route-P-child domination cannot be the missing EWQ completed-Xi producer; any viable fusion must
use a signed/nonlocal comparison rather than a fixed positive trace-class majorant.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- A fixed positive-aperture Route-P trace-class diagonal cannot dominate the cofinal
Gamma Bockstein except at neutral horizontal grade. -/
theorem routePTraceClassWeight_dominates_bocksteinMagnitude_iff (t : ℝ) :
    (∃ d C : ℝ, 0 < d ∧ 0 ≤ C ∧ ∀ p : Nat.Primes,
      primeGammaCofinalBocksteinMagnitude t p ≤
        C * routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p) ↔
      t = 0 := by
  constructor
  · rintro ⟨d, C, hd, _hC, hdom⟩
    have hsumMajorant : Summable
        (fun p : Nat.Primes =>
          C * routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p) :=
      Summable.mul_left C
        (summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd)
    have hsum : Summable (primeGammaCofinalBocksteinMagnitude t) :=
      Summable.of_nonneg_of_le
        (fun p => abs_nonneg
          (primeActivationOccupancyFisherTwist (-t) p -
            primeActivationOccupancyFisherTwist t p))
        hdom hsumMajorant
    exact (summable_primeGammaCofinalBocksteinMagnitude_iff (t := t)).mp hsum
  · rintro rfl
    refine ⟨1, 0, by norm_num, by norm_num, ?_⟩
    intro p
    simp [primeGammaCofinalBocksteinMagnitude]

/-- The same incompatibility on the actual multiplicity-faithful Xi trace-one residue mass:
domination by one Route-P positive cofinal child is possible exactly on the critical line. -/
theorem routePTraceClassWeight_dominates_xiTraceOneSourceMass_iff
    (rho : XiDivisorSupport) :
    (∃ d C : ℝ, 0 < d ∧ 0 ≤ C ∧ ∀ p : Nat.Primes,
      xiReflectionIncidencePrimeTraceOneSourceMass rho p ≤
        C * routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p) ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · rintro ⟨d, C, hd, _hC, hdom⟩
    have hsumMajorant : Summable
        (fun p : Nat.Primes =>
          C * routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p) :=
      Summable.mul_left C
        (summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd)
    have hsum : Summable (xiReflectionIncidencePrimeTraceOneSourceMass rho) :=
      Summable.of_nonneg_of_le
        (xiReflectionIncidencePrimeTraceOneSourceMass_nonneg rho)
        hdom hsumMajorant
    exact (summable_xiReflectionIncidencePrimeTraceOneSourceMass_iff rho).mp hsum |>
      (summable_xiZeroCopyLineReflectionPrimeIncidenceSchattenMass_one_iff rho).mp
  · intro hrho
    refine ⟨1, 0, by norm_num, by norm_num, ?_⟩
    intro p
    rw [xiReflectionIncidencePrimeTraceOneSourceMass_eq]
    have hrate : primeDepthBVWoldXiCenteredRate rho = 0 :=
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).mpr hrho
    simp [xiZeroCopyLineReflectionPrimeIncidenceSchattenMass,
      primeGammaCofinalBocksteinSchattenMass,
      primeGammaCofinalBocksteinMagnitude, hrate]

end

end RHTower
