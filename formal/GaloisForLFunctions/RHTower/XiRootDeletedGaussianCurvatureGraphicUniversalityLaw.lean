import GaloisForLFunctions.RHTower.XiRootDeletedCanonicalReconstructionGraphicConnector
import GaloisForLFunctions.RHTower.XiTransverseValuationGaussianCurvatureHilbertPhase

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

/-- Curvature-enhanced root-deleted reconstruction and graphic-network certificate. -/
structure XiTransverseRootDeletedGaussianCurvatureGraphicCertificate
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (tail head : E → Fin (N + 1))
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) : Prop where
  canonicalReconstruction :
    XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
      root shift sourcePrime
  cofiniteNonrootExactRecovery :
    XiTransversePrimeJetApertureCofiniteHilbertReconstruction
      (xiTransverseRootDeletedShift root shift) m
  fullGaussianGram :
    (xiTransversePrimeFirstValuationGaussianGramMatrix shift metricPrime).PosDef
  graphicNetworkUniversality :
    XiTransverseRootDeletedGraphicNetworkUniversality root shift tail head
  strictNonrootGaussianCurvature :
    deriv (deriv (fun s =>
      Real.log
        (xiTransversePrimeValuationRankOneGaussianMetricGram
          (xiTransverseRootDeletedShift root shift) metricPrime s).det)) t < 0
  nonrootGaussianSimilarityNonnormal :
    matrixSelfCommutator
      (xiTransversePrimeValuationRankOneGaussianSimilarity
        (xiTransverseRootDeletedShift root shift) metricPrime t) ≠ 0

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

/-- **Curvature-enhanced root-deleted graphic universality law.**  Canonical nonroot recovery and
the rank-two threshold are equivalent to simultaneous full Gaussian separation, exact cofinite
recovery, differential graphic-network universality, strict curvature, and operator
nonnormality. -/
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
    have hphase :=
      (xiTransverseRootDeletedCanonicalReconstruction_and_two_le_iff_gaussianCurvaturePhase
        root shift sourcePrime metricPrime m t ht).1
          ⟨hcanonical, htwo⟩
    have hnonnormal :=
      (xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_reconstruction_and_nonnormal
        (xiTransverseRootDeletedShift root shift) m metricPrime t ht).1 hphase
    exact {
      canonicalReconstruction := hcanonical
      cofiniteNonrootExactRecovery := hphase.1
      fullGaussianGram :=
        (xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_fullGaussianGram_posDef
          root shift hroot sourcePrime metricPrime).1 hcanonical
      graphicNetworkUniversality :=
        (xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_graphicNetworkUniversality
          root shift hroot tail head sourcePrime).1 hcanonical
      strictNonrootGaussianCurvature := hphase.2
      nonrootGaussianSimilarityNonnormal := hnonnormal.2 }
  · intro h
    have htwo :=
      (xiTransversePrimeValuationRankOneGaussianMetric_logDet_secondDerivative_lt_zero_iff_of_cofiniteHilbertReconstruction
        (xiTransverseRootDeletedShift root shift) m metricPrime
        h.cofiniteNonrootExactRecovery t ht).1
          h.strictNonrootGaussianCurvature
    exact ⟨h.canonicalReconstruction, htwo⟩

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
