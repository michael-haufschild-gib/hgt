import GaloisForLFunctions.RepresentationLifting.ChainSelfExtension
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeAugmentedHomology
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeWeightedAugmentedHomology

/-!+# Self-extensions of prime-cutoff boundary complexes

The canonical square-zero extension applies to the actual prime-product boundary, its
augmented empty-face degree, and the integral prime-weighted boundary. Its projection lifts
the original total differential, independently of whether the cutoff homology vanishes.
-/

noncomputable section

namespace GaloisForLFunctions.EffectiveScalingGeometry

open RepresentationLifting

variable (R : Type*) [CommRing R]

/-- Every adjacent triple of prime-cutoff modules has an exact square-zero self-extension. -/
theorem primeCutoff_detector_exact (k N : ℕ) :
    Function.Injective (detectorInclusion (primeCutoffShortComplex R k N)) ∧
      LinearMap.range (detectorInclusion (primeCutoffShortComplex R k N)) =
        LinearMap.ker (detectorProjection (primeCutoffShortComplex R k N)) ∧
      Function.Surjective (detectorProjection (primeCutoffShortComplex R k N)) :=
  detector_exact _

/-- The extension lifts the literal deletion boundary in both adjacent degrees. -/
theorem primeCutoff_detector_lifts (k N : ℕ)
    (v : ChainTotal (primeCutoffShortComplex R k N)) :
    detectorProjection (primeCutoffShortComplex R k N)
        (detectorLift (primeCutoffShortComplex R k N) v) =
      (0, primeCutoffDifferential R (RHTower.primeChainAugmentation R) (k + 1) N v.1,
        primeCutoffDifferential R (RHTower.primeChainAugmentation R) k N v.2.1) :=
  detectorProjection_lift _ v

/-- The augmented empty-face degree is included in the same exact construction. -/
theorem primeAugmented_detector_exact (N : ℕ) :
    Function.Injective (detectorInclusion (primeZeroShortComplex R N)) ∧
      LinearMap.range (detectorInclusion (primeZeroShortComplex R N)) =
        LinearMap.ker (detectorProjection (primeZeroShortComplex R N)) ∧
      Function.Surjective (detectorProjection (primeZeroShortComplex R N)) :=
  detector_exact _

/-- Integral prime-weighted chains admit the extension before reduction modulo two. -/
theorem primeWeighted_detector_exact (N : ℕ) :
    Function.Injective (detectorInclusion (primeValueZeroShortComplex N)) ∧
      LinearMap.range (detectorInclusion (primeValueZeroShortComplex N)) =
        LinearMap.ker (detectorProjection (primeValueZeroShortComplex N)) ∧
      Function.Surjective (detectorProjection (primeValueZeroShortComplex N)) :=
  detector_exact _

/-- The lifted integral boundary retains its original prime weights. -/
theorem primeWeighted_detector_lifts (N : ℕ)
    (v : ChainTotal (primeValueZeroShortComplex N)) :
    detectorProjection (primeValueZeroShortComplex N)
        (detectorLift (primeValueZeroShortComplex N) v) =
      chainDifferential (primeValueZeroShortComplex N) v :=
  detectorProjection_lift _ v

end GaloisForLFunctions.EffectiveScalingGeometry

#print axioms GaloisForLFunctions.EffectiveScalingGeometry.primeCutoff_detector_exact
#print axioms GaloisForLFunctions.EffectiveScalingGeometry.primeCutoff_detector_lifts
#print axioms GaloisForLFunctions.EffectiveScalingGeometry.primeAugmented_detector_exact
#print axioms GaloisForLFunctions.EffectiveScalingGeometry.primeWeighted_detector_exact
#print axioms GaloisForLFunctions.EffectiveScalingGeometry.primeWeighted_detector_lifts
