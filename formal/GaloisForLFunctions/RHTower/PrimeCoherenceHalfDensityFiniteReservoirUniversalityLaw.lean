import GaloisForLFunctions.RHTower.PrimeCoherenceFiniteReservoirUniversalityLaw
import GaloisForLFunctions.HTGeometry.InfiniteCoherenceHalfDensity

open scoped Differential

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-!
# Prime-coherence half-density finite-reservoir universality

The order-pointed continuum prime family has arbitrarily small square-summable half-density
differences between every member and pair, even when the individual unnormalized half-densities
need not be square summable.  Continuum differential rank, unique positive-definite pointing,
and finite-reservoir observation escape hold simultaneously.
-/

/-- Squared prime-coherence weight, viewed as an unnormalized half-density mass. -/
def primeCoherenceHalfDensityMass (sigma : ℝ) (p : Nat.Primes) : ℝ :=
  primeCoherenceWeight sigma p ^ 2

theorem sqrt_primeCoherenceHalfDensityMass (sigma : ℝ) (p : Nat.Primes) :
    Real.sqrt (primeCoherenceHalfDensityMass sigma p) =
      primeCoherenceWeight sigma p := by
  rw [primeCoherenceHalfDensityMass, Real.sqrt_sq_eq_abs]
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by
    exact_mod_cast p.2.pos
  exact abs_of_pos (Real.rpow_pos_of_pos hp _)

/-- **Half-density finite-reservoir universality law.**  Every coherence neighborhood of the
positive prime pointing contains a continuum-rank family with arbitrarily small pairwise
half-density differences and universal finite-reservoir hypertranscendental observations. -/
theorem exists_orderPointedContinuumPrimeHalfDensityFiniteReservoirUniversality
    (sigma eta x : ℝ) (hsigma : 0 < sigma) (heta : 0 < eta) (hx : 1 < x) :
    ∃ e : PrefixFunctionCoordinate ↪ Nat.Primes,
      DifferentialIndependent finitePrimeRationalCoefficientField
        (fun xa : (ℕ → Bool) × ℕ =>
          signedPrimeNaturalShiftPalette
            (continuumSparsePrimeOrientation (fun _ => false) e xa.1) xa.2) ∧
      Algebra.trdeg finitePrimeRationalCoefficientField
        (differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range fun z : ℕ → Bool =>
            signedPrimeNaturalShiftPalette
              (continuumSparsePrimeOrientation (fun _ => false) e z) 0)) =
        Cardinal.continuum ∧
      (∀ z, (∑' p,
        (booleanHalfDensity (primeCoherenceHalfDensityMass sigma)
            (continuumSparsePrimeOrientation (fun _ => false) e z) p -
          booleanHalfDensity (primeCoherenceHalfDensityMass sigma)
            (fun _ => false) p) ^ 2) < eta ^ 2) ∧
      (∀ z w, (∑' p,
        (booleanHalfDensity (primeCoherenceHalfDensityMass sigma)
            (continuumSparsePrimeOrientation (fun _ => false) e z) p -
          booleanHalfDensity (primeCoherenceHalfDensityMass sigma)
            (continuumSparsePrimeOrientation (fun _ => false) e w) p) ^ 2) < eta ^ 2) ∧
      (∀ epsilon : Nat.Primes → Bool,
        PositiveDefiniteOnReal (signedPrimeVerticalTrace epsilon x) ↔
          epsilon = fun _ => false) ∧
      ∀ z (S : IntermediateField ℂ arithmeticFunctionRationalCoordinateField),
        DerivationClosed S →
        Algebra.trdeg ℂ S < Cardinal.aleph0 →
        ∀ c : (Unit × ℕ) →₀ S, c ≠ 0 →
          HypertranscendentalOver ℂ
            (finsuppLinearDifferentialObservation S c
              (signedPrimeNaturalShiftPalette
                (continuumSparsePrimeOrientation (fun _ => false) e z) 0)) := by
  obtain ⟨e, hdiff, htrdeg, hbase, hpair, hpd, hfilter⟩ :=
    exists_orderPointedContinuumPrimeCoherenceFiniteReservoirUniversality
      sigma eta x hsigma heta hx
  refine ⟨e, hdiff, htrdeg, ?_, ?_, hpd, hfilter⟩
  · intro z
    rw [← weightedOrientationDistanceSq_sqrt_eq_halfDensity_sub_sq]
    simpa only [sqrt_primeCoherenceHalfDensityMass] using hbase z
  · intro z w
    rw [← weightedOrientationDistanceSq_sqrt_eq_halfDensity_sub_sq]
    simpa only [sqrt_primeCoherenceHalfDensityMass] using hpair z w

end

end RHTower
