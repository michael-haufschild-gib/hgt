import GaloisForLFunctions.HTGeometry.PrimeCoherenceOrderPointing
import GaloisForLFunctions.RHTower.PrimeSourceFiniteJetConstraintBoundary

open scoped Differential

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-!
# Prime-coherence finite-reservoir universality

Every coherence neighborhood of the unique positive-definite prime pointing contains a
continuum-rank differential family.  Moreover, every nonzero variable-coefficient finite filter
of every member remains hypertranscendental whenever its derivation-closed coefficient reservoir
has finite transcendence degree.
-/

/-- **Order-pointed finite-reservoir universality law.**  Arbitrarily tight metric coherence,
continuum differential rank, unique positive-definite pointing, and finite-observer
hypertranscendence hold simultaneously for one sparse prime family. -/
theorem exists_orderPointedContinuumPrimeCoherenceFiniteReservoirUniversality
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
      (∀ z, weightedOrientationDistanceSq (primeCoherenceWeight sigma)
        (continuumSparsePrimeOrientation (fun _ => false) e z)
        (fun _ => false) < eta ^ 2) ∧
      (∀ z w, weightedOrientationDistanceSq (primeCoherenceWeight sigma)
        (continuumSparsePrimeOrientation (fun _ => false) e z)
        (continuumSparsePrimeOrientation (fun _ => false) e w) < eta ^ 2) ∧
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
  obtain ⟨e, hdiff, htrdeg, hbase, hpair, hpd⟩ :=
    exists_orderPointedContinuumPrimeCoherenceSaturation
      sigma eta x hsigma heta hx
  refine ⟨e, hdiff, htrdeg, hbase, hpair, hpd, ?_⟩
  intro z S hSclosed hSfinite c hc
  exact signedPrimeSource_finsuppLinearDifferentialObservation_hypertranscendentalOver
    (continuumSparsePrimeOrientation (fun _ => false) e z)
    S hSclosed hSfinite c hc

end

end RHTower
