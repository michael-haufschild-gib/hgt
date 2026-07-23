import GaloisForLFunctions.RHTower.XiRootDeletedCanonicalReconstructionGraphicConnector
import GaloisForLFunctions.RHTower.XiTransverseValuationGaussianCurvatureHilbertPhase
import GaloisForLFunctions.RHTower.XiTransverseValuationGaussianIntrinsicDimensionUniversalityLaw

/-!
# Root-deleted Xi Gaussian curvature and graphic universality

Deleting a distinguished zero root leaves a canonically enumerated packet of nonroot shifts.
Existing results identify exact first-valuation recovery on that packet with full Gaussian
collision separation and with the complete differential graphic-network matroid of every edge
family.

The transverse HilbertMetric curvature law adds the missing rank-two endpoint.  Canonical
root-deleted recovery together with two nonroot vertices is exactly strict Gaussian log-volume
curvature and nonnormality of the associated square-root similarity.  The result is independent of
the prime used for canonical recovery and is uniform in the metric prime, jet depth, and
nonnegative scale.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HilbertMetric
open scoped ComplexOrder Differential

local instance xiRootDeletedCurvatureUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiRootDeletedCurvatureUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiRootDeletedCurvatureUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiRootDeletedCurvatureUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiRootDeletedCurvatureCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiRootDeletedCurvatureCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

local instance xiRootDeletedCurvatureAllValuationDifferential :
    Differential analyticScalarValuationLayerDifferentialField :=
  derivationClosedDifferential _
    (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
      (Set.range analyticScalarValuationLayerCarrier))

local instance xiRootDeletedCurvatureAllValuationDifferentialAlgebra :
    DifferentialAlgebra analyticScalarValuationLayerDifferentialField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ =
      ((c′ : analyticScalarValuationLayerDifferentialField) : upperEndMeroField)
    rfl

/-- Canonically enumerated packet obtained by deleting one distinguished vertex. -/
def xiTransverseRootDeletedShift
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ) :
    Fin N → ℕ :=
  fun j => shift (root.succAbove j)

/-- Complete differential graphic-network package of a rooted finite Xi shift packet. -/
def XiTransverseRootDeletedGraphicNetworkUniversality
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (tail head : E → Fin (N + 1)) : Prop :=
  Function.Injective shift ∧
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) =
      rootedIncidenceMatroid
        (C := upperEndRationalCoordinateField) root tail head ∧
    differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) =
      rootedIncidenceMatroid
        (C := analyticScalarValuationLayerDifferentialField) root tail head ∧
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) =
      differentialFamilyMatroid
        (F := analyticScalarValuationLayerDifferentialField)
        (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head)

/-- Minimal curvature-enhanced root-deleted reconstruction and graphic-network certificate.
Root-zero canonical recovery and one strict-curvature fact derive full Gaussian positivity,
cofinite recovery, graphic universality, rank two, and operator nonnormality below. -/
structure XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (tail head : E → Fin (N + 1))
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) : Prop where
  rootIsZero : shift root = 0
  canonicalReconstruction :
    XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
      root shift sourcePrime
  strictNonrootGaussianCurvature :
    deriv (deriv (fun s =>
      Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram
          (xiTransverseRootDeletedShift root shift) metricPrime s).det)) t < 0

namespace XiTransverseRootDeletedGaussianCurvatureGraphicCertificate

/-- Root-zero canonical recovery supplies full Gaussian collision separation at the stored metric
prime. -/
theorem fullGaussianGram
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
        root shift tail head sourcePrime metricPrime m t) :
    (xiTransversePrimeFirstValuationGaussianGramMatrix shift metricPrime).PosDef :=
  (xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_fullGaussianGram_posDef
    root shift hcertificate.rootIsZero sourcePrime metricPrime).1
      hcertificate.canonicalReconstruction

/-- Root-zero canonical recovery supplies complete differential graphic-network universality. -/
theorem graphicNetworkUniversality
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
        root shift tail head sourcePrime metricPrime m t) :
    XiTransverseRootDeletedGraphicNetworkUniversality root shift tail head :=
  (xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_graphicNetworkUniversality
    root shift hcertificate.rootIsZero tail head sourcePrime).1
      hcertificate.canonicalReconstruction

/-- Canonical recovery discharges cofinite nonroot recovery at every independently chosen jet
depth, not only the depth carried by the certificate. -/
theorem cofiniteNonrootExactRecoveryAt
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
        root shift tail head sourcePrime metricPrime m t)
    (jetDepth : ℕ) :
    XiTransversePrimeJetApertureCofiniteHilbertReconstruction
      (xiTransverseRootDeletedShift root shift) jetDepth := by
  apply
    (xiTransversePrimeValuationCanonicalReconstruction_iff_cofiniteApertureHilbertReconstruction
      (xiTransverseRootDeletedShift root shift) sourcePrime jetDepth).1
  exact hcertificate.canonicalReconstruction

/-- Stored-depth cofinite recovery remains available as a derived dot API. -/
theorem cofiniteNonrootExactRecovery
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
        root shift tail head sourcePrime metricPrime m t) :
    XiTransversePrimeJetApertureCofiniteHilbertReconstruction
      (xiTransverseRootDeletedShift root shift) m :=
  hcertificate.cofiniteNonrootExactRecoveryAt m

/-- Canonical nonroot recovery discharges injectivity and exclusion of zero. -/
theorem nonrootShiftInjectiveAndNeZero
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
        root shift tail head sourcePrime metricPrime m t) :
    Function.Injective (xiTransverseRootDeletedShift root shift) ∧
      ∀ j, xiTransverseRootDeletedShift root shift j ≠ 0 :=
  (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
    (xiTransverseRootDeletedShift root shift) m).1
      hcertificate.cofiniteNonrootExactRecovery

/-- Strict stored curvature discharges the former explicit nonroot rank-two premise. -/
theorem rankTwo
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
        root shift tail head sourcePrime metricPrime m t)
    (ht : 0 ≤ t) :
    2 ≤ N :=
  (xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_lt_zero_iff_of_cofiniteHilbertReconstruction
    (xiTransverseRootDeletedShift root shift) m metricPrime
    hcertificate.cofiniteNonrootExactRecovery t ht).1
      hcertificate.strictNonrootGaussianCurvature

/-- Cofinite recovery and derived rank two force operator nonnormality at the stored target. -/
theorem nonrootGaussianSimilarityNonnormal
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
        root shift tail head sourcePrime metricPrime m t)
    (ht : 0 ≤ t) :
    matrixSelfCommutator
      (xiTransversePrimeValuationRankOneGaussianSimilarity
        (xiTransverseRootDeletedShift root shift) metricPrime t) ≠ 0 :=
  (xiTransversePrimeValuationRankOneGaussianSimilarity_selfCommutator_ne_zero_iff_of_cofiniteHilbertReconstruction
    (xiTransverseRootDeletedShift root shift) m metricPrime
    hcertificate.cofiniteNonrootExactRecovery t ht).2
      (hcertificate.rankTwo ht)

/-- At a nonnegative stored scale, the root-deleted certificate supplies intrinsic
one-dimensional Gaussian geometry at every independently chosen prime. -/
theorem nonrootIntrinsicDimensionCertificate
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
        root shift tail head sourcePrime metricPrime m t)
    (ht : 0 ≤ t) (intrinsicPrime : Nat.Primes) :
    XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate
      (xiTransverseRootDeletedShift root shift) intrinsicPrime :=
  (xiTransversePrimeValuationGaussianIntrinsicDimensionCertificate_iff
    (xiTransverseRootDeletedShift root shift) intrinsicPrime).1
      ⟨hcertificate.nonrootShiftInjectiveAndNeZero.1,
        hcertificate.rankTwo ht⟩

/-- **Root-deleted full sign-duality discharge.**  Canonical recovery and one stored strict
curvature certificate force reconstruction sign duality at every independently chosen jet depth,
valuation prime, and nonnegative scale. -/
theorem nonrootCurvatureSignDualityCertificate
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
        root shift tail head sourcePrime metricPrime m t)
    (ht : 0 ≤ t) (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
      (xiTransverseRootDeletedShift root shift)
      jetDepth valuationPrime valuationScale :=
  (xiTransversePrimeValuationGaussianCurvatureSignDualityCertificate_iff
    (xiTransverseRootDeletedShift root shift)
    jetDepth valuationPrime valuationScale hvaluationScale).1
      ⟨hcertificate.cofiniteNonrootExactRecoveryAt jetDepth,
        hcertificate.rankTwo ht⟩

/-- **Root-deleted valuation universality connector.**  Canonical recovery alone supplies enough
collision freedom for the full curvature, nonnormality, intrinsic-dimension, and
differential-rank equivalence chain at independently chosen primes and nonnegative scales. -/
theorem nonrootValuationUniversalityPhase
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    {root : Fin (N + 1)} {shift : Fin (N + 1) → ℕ}
    {tail head : E → Fin (N + 1)}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
        root shift tail head sourcePrime metricPrime m t)
    (valuationCurvaturePrime operatorPrime intrinsicPrime : Nat.Primes)
    (valuationCurvatureScale operatorScale : ℝ)
    (hvaluationCurvatureScale : 0 ≤ valuationCurvatureScale)
    (hoperatorScale : 0 ≤ operatorScale) :
    XiTransversePrimeValuationGaussianCurvatureIntrinsicDifferentialUniversalityPhase
      (xiTransverseRootDeletedShift root shift)
      valuationCurvaturePrime operatorPrime intrinsicPrime
      valuationCurvatureScale operatorScale :=
  xiTransversePrimeValuationGaussian_curvature_nonnormal_intrinsicDimension_differentialRank_universality_of_injective
    (xiTransverseRootDeletedShift root shift)
    valuationCurvaturePrime operatorPrime intrinsicPrime
    valuationCurvatureScale operatorScale
    hvaluationCurvatureScale hoperatorScale
    hcertificate.nonrootShiftInjectiveAndNeZero.1

end XiTransverseRootDeletedGaussianCurvatureGraphicCertificate

/-- **Canonical root-deletion/curvature connector.**  Exact recovery on the canonically
enumerated nonroot packet, together with two retained vertices, is exactly its Gaussian curvature
phase at any other prime and any nonnegative scale. -/
theorem
    xiTransverseRootDeletedCanonicalReconstruction_and_two_le_iff_gaussianCurvaturePhase
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
        root shift sourcePrime ∧
      2 ≤ N) ↔
      XiTransversePrimeJetApertureGaussianCurvaturePhase
        (xiTransverseRootDeletedShift root shift) m metricPrime t := by
  change
    (XiTransversePrimeValuationCanonicalReconstruction
        (xiTransverseRootDeletedShift root shift) sourcePrime ∧
      2 ≤ N) ↔ _
  calc
    _ ↔ XiTransversePrimeJetApertureCofiniteHilbertReconstruction
          (xiTransverseRootDeletedShift root shift) m ∧
        2 ≤ N :=
      and_congr
        (xiTransversePrimeValuationCanonicalReconstruction_iff_cofiniteApertureHilbertReconstruction
          (xiTransverseRootDeletedShift root shift) sourcePrime m)
        Iff.rfl
    _ ↔ _ :=
      (xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_reconstruction_and_two_le
        (xiTransverseRootDeletedShift root shift) m metricPrime t ht).symm

/-- **Full-Gaussian/root-deleted curvature connector.**  When the distinguished root is zero,
strict positivity of one full collision Gram and the sharp nonroot rank condition are equivalent
to strict curvature after deleting the root. -/
theorem
    xiTransverseRootDeletedFullGaussian_posDef_and_two_le_iff_gaussianCurvaturePhase
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (sourcePrime metricPrime : Nat.Primes)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ((xiTransversePrimeFirstValuationGaussianGramMatrix shift metricPrime).PosDef ∧
        2 ≤ N) ↔
      XiTransversePrimeJetApertureGaussianCurvaturePhase
        (xiTransverseRootDeletedShift root shift) m metricPrime t := by
  calc
    _ ↔ XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
          root shift sourcePrime ∧
        2 ≤ N :=
      and_congr
        (xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_fullGaussianGram_posDef
          root shift hroot sourcePrime metricPrime).symm
        Iff.rfl
    _ ↔ _ :=
      xiTransverseRootDeletedCanonicalReconstruction_and_two_le_iff_gaussianCurvaturePhase
        root shift sourcePrime metricPrime m t ht

/-- **Unconditional curvature-enhanced root-deleted graphic universality law.**  The root
equation, canonical nonroot recovery, and rank-two threshold are exactly the minimal certificate;
full Gaussian separation, cofinite recovery, differential graphic universality, and nonnormality
are derived consequences. -/
theorem
    xiTransverseRootDeleted_zeroRoot_and_canonical_and_two_le_iff_gaussianCurvatureGraphicCertificate
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (tail head : E → Fin (N + 1))
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (shift root = 0 ∧
      XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
        root shift sourcePrime ∧
      2 ≤ N) ↔
      XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
        root shift tail head sourcePrime metricPrime m t := by
  constructor
  · rintro ⟨hroot, hcanonical, htwo⟩
    have hphase :=
      (xiTransverseRootDeletedCanonicalReconstruction_and_two_le_iff_gaussianCurvaturePhase
        root shift sourcePrime metricPrime m t ht).1
          ⟨hcanonical, htwo⟩
    exact {
      rootIsZero := hroot
      canonicalReconstruction := hcanonical
      strictNonrootGaussianCurvature := hphase.2 }
  · intro h
    exact ⟨h.rootIsZero, h.canonicalReconstruction, h.rankTwo ht⟩

/-- Root-zero specialization preserving the original two-conjunct interface. -/
theorem xiTransverseRootDeleted_gaussianCurvatureGraphicCertificate_iff
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (tail head : E → Fin (N + 1))
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
        root shift sourcePrime ∧
      2 ≤ N) ↔
      XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
        root shift tail head sourcePrime metricPrime m t := by
  constructor
  · rintro ⟨hcanonical, htwo⟩
    exact
      (xiTransverseRootDeleted_zeroRoot_and_canonical_and_two_le_iff_gaussianCurvatureGraphicCertificate
        root shift tail head sourcePrime metricPrime m t ht).1
          ⟨hroot, hcanonical, htwo⟩
  · intro h
    exact ⟨h.canonicalReconstruction, h.rankTwo ht⟩

/-- **Exact root-deleted graphic/sign-duality connector.**  At nonnegative stored and target
scales, the complete root-deleted curvature/graphic certificate is exactly the root equation
together with reconstruction sign duality at any independently chosen depth and valuation
prime. -/
theorem
    xiTransverseRootDeleted_gaussianCurvatureGraphicCertificate_iff_zeroRoot_and_curvatureSignDuality
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (tail head : E → Fin (N + 1))
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
        root shift tail head sourcePrime metricPrime m t ↔
      shift root = 0 ∧
        XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
          (xiTransverseRootDeletedShift root shift)
          jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        shift root = 0 ∧
          XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
              root shift sourcePrime ∧
            2 ≤ N :=
      (xiTransverseRootDeleted_zeroRoot_and_canonical_and_two_le_iff_gaussianCurvatureGraphicCertificate
        root shift tail head sourcePrime metricPrime m t ht).symm
    _ ↔
        shift root = 0 ∧
          XiTransversePrimeJetApertureCofiniteHilbertReconstruction
              (xiTransverseRootDeletedShift root shift) jetDepth ∧
            2 ≤ N :=
      and_congr Iff.rfl
        (and_congr
          (xiTransversePrimeValuationCanonicalReconstruction_iff_cofiniteApertureHilbertReconstruction
            (xiTransverseRootDeletedShift root shift) sourcePrime jetDepth)
          Iff.rfl)
    _ ↔ _ :=
      and_congr Iff.rfl
        (xiTransversePrimeValuationGaussianCurvatureSignDualityCertificate_iff
          (xiTransverseRootDeletedShift root shift)
          jetDepth valuationPrime valuationScale hvaluationScale)

/-- **Universal root-deleted graphic/sign-duality law.**  One root-deleted graphic certificate
at one metric target is exactly the zero-root phase carrying reconstruction sign duality at every
jet depth, valuation prime, and nonnegative scale. -/
theorem
    xiTransverseRootDeleted_gaussianCurvatureGraphicCertificate_iff_zeroRoot_and_every_curvatureSignDuality
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (tail head : E → Fin (N + 1))
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
        root shift tail head sourcePrime metricPrime m t ↔
      shift root = 0 ∧
        ∀ (jetDepth : ℕ) (valuationPrime : Nat.Primes)
          (valuationScale : ℝ), 0 ≤ valuationScale →
            XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
              (xiTransverseRootDeletedShift root shift)
              jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        shift root = 0 ∧
          XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
              root shift sourcePrime ∧
            2 ≤ N :=
      (xiTransverseRootDeleted_zeroRoot_and_canonical_and_two_le_iff_gaussianCurvatureGraphicCertificate
        root shift tail head sourcePrime metricPrime m t ht).symm
    _ ↔
        shift root = 0 ∧
          XiTransversePrimeJetApertureCofiniteHilbertReconstruction
              (xiTransverseRootDeletedShift root shift) m ∧
            2 ≤ N :=
      and_congr Iff.rfl
        (and_congr
          (xiTransversePrimeValuationCanonicalReconstruction_iff_cofiniteApertureHilbertReconstruction
            (xiTransverseRootDeletedShift root shift) sourcePrime m)
          Iff.rfl)
    _ ↔ _ :=
      and_congr Iff.rfl
        (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_and_two_le_iff_every_gaussianCurvatureSignDualityCertificate
          (xiTransverseRootDeletedShift root shift) m)

/-- **Universal root-deleted curvature law.**  One canonical reconstruction phase and the
rank-two condition hold exactly when every metric prime, jet depth, and nonnegative scale lies in
the strict Gaussian curvature phase. -/
theorem
    xiTransverseRootDeletedCanonicalReconstruction_and_two_le_iff_every_gaussianCurvaturePhase
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (sourcePrime : Nat.Primes) :
    (XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
        root shift sourcePrime ∧
      2 ≤ N) ↔
      ∀ (metricPrime : Nat.Primes) (m : ℕ) (t : ℝ), 0 ≤ t →
        XiTransversePrimeJetApertureGaussianCurvaturePhase
          (xiTransverseRootDeletedShift root shift) m metricPrime t := by
  constructor
  · intro h metricPrime m t ht
    exact
      (xiTransverseRootDeletedCanonicalReconstruction_and_two_le_iff_gaussianCurvaturePhase
        root shift sourcePrime metricPrime m t ht).1 h
  · intro hall
    let metricPrime : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hphase := hall metricPrime 0 0 (by norm_num)
    exact
      (xiTransverseRootDeletedCanonicalReconstruction_and_two_le_iff_gaussianCurvaturePhase
        root shift sourcePrime metricPrime 0 0 (by norm_num)).2 hphase

/-- The universal law can expose the complete graphic and operator certificate simultaneously
at every target prime, depth, and nonnegative scale. -/
theorem
    xiTransverseRootDeletedCanonicalReconstruction_and_two_le_iff_every_curvatureGraphicCertificate
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (tail head : E → Fin (N + 1))
    (sourcePrime : Nat.Primes) :
    (XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
        root shift sourcePrime ∧
      2 ≤ N) ↔
      ∀ (metricPrime : Nat.Primes) (m : ℕ) (t : ℝ), 0 ≤ t →
        XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
          root shift tail head sourcePrime metricPrime m t := by
  constructor
  · intro h metricPrime m t ht
    exact
      (xiTransverseRootDeleted_gaussianCurvatureGraphicCertificate_iff
        root shift hroot tail head sourcePrime metricPrime m t ht).1 h
  · intro hall
    let metricPrime : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hcertificate := hall metricPrime 0 0 (by norm_num)
    exact
      (xiTransverseRootDeleted_gaussianCurvatureGraphicCertificate_iff
        root shift hroot tail head sourcePrime metricPrime 0 0 (by norm_num)).2
          hcertificate

end

end RHTower
