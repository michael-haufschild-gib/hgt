import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureDyadicCofiniteHilbertReconstruction
import GaloisForLFunctions.RHTower.XiRootDeletedCanonicalPairHilbertPhase
import GaloisForLFunctions.RHTower.XiRootedStarIncidenceValuationMetricFusionUniversalityLaw

/-!
# Root-deleted dyadic cofinite Hilbert universality

For an integral aperture packet with a distinguished zero root, deleting that root from one
prime's dyadic-depth feature family turns cofinite tail recovery into an exact classifier for
injectivity of the full packet.

This closes the remaining interface gap between the dyadic-depth realization and the existing
root-deleted theory: one dyadic cofinite reconstruction is equivalent to prescribed valuation
reconstruction, cofinite prime-jet reconstruction, full Gaussian positivity at every positive
bandwidth, and rooted graphic-network universality over both differential bases.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder Differential

local instance xiRootDeletedDyadicUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiRootDeletedDyadicUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiRootDeletedDyadicUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiRootDeletedDyadicUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiRootDeletedDyadicCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiRootDeletedDyadicCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

local instance xiRootDeletedDyadicAllValuationDifferential :
    Differential analyticScalarValuationLayerDifferentialField :=
  derivationClosedDifferential _
    (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
      (Set.range analyticScalarValuationLayerCarrier))

local instance xiRootDeletedDyadicAllValuationDifferentialAlgebra :
    DifferentialAlgebra analyticScalarValuationLayerDifferentialField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ =
      ((c′ : analyticScalarValuationLayerDifferentialField) : upperEndMeroField)
    rfl

/-- Root-deleted dyadic-depth cofinite reconstruction is independent of the prime used to encode
the remaining integral apertures. -/
theorem
    xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_prime_invariant
    {N : ℕ} (root : Fin N) (shift : Fin N → ℕ) (hroot : shift root = 0)
    (p r : Nat.Primes) :
    XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift p ↔
      XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift r := by
  rw [
    xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_injective
      root shift hroot p,
    xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_injective
      root shift hroot r]

/-- **Dyadic/canonical reconstruction connector.** Cofinite recovery from the nonroot dyadic-depth
features at one prime is equivalent to exact dual recovery from the fixed square valuation sampler
at any other prime. -/
theorem
    xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_canonicalValuationReconstruction
    {N : ℕ} (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p r : Nat.Primes) :
    XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift p ↔
      XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
        root shift r := by
  rw [
    xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_injective
      root shift hroot p,
    xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_injective
      root shift hroot r]

/-- **Dyadic/prime-jet reconstruction connector.** One deletion-robust dyadic-depth realization is
equivalent to exact prime-source jet recovery after every finite prime deletion and at every fixed
jet depth. -/
theorem
    xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_primeJetCofiniteHilbertReconstruction
    {N : ℕ} (root : Fin N) (shift : Fin N → ℕ)
    (hroot : shift root = 0) (p : Nat.Primes) (m : ℕ) :
    XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift p ↔
      XiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction
        root shift m := by
  rw [
    xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_injective
      root shift hroot p,
    xiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction_iff_injective
      root shift hroot m]

/-- **Dyadic/full-Gaussian connector.** At every positive bandwidth and independently chosen prime,
cofinite recovery from all nonroot dyadic depths is equivalent to strict positivity of the full
Gaussian collision Gram with the zero root retained. -/
theorem
    xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_fullGaussianGramAt_posDef
    {N : ℕ} (root : Fin N) (shift : Fin N → ℕ)
    (hroot : shift root = 0) (p r : Nat.Primes)
    {t : ℝ} (ht : 0 < t) :
    XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift p ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift r t).PosDef := by
  rw [
    xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_injective
      root shift hroot p,
    xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_iff_injective
      shift r ht]

/-- Unit-bandwidth form of the root-deleted dyadic/full-Gaussian equivalence. -/
theorem
    xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_fullGaussianGram_posDef
    {N : ℕ} (root : Fin N) (shift : Fin N → ℕ)
    (hroot : shift root = 0) (p r : Nat.Primes) :
    XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift p ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrix shift r).PosDef := by
  simpa only [xiTransversePrimeFirstValuationGaussianGramMatrix] using
    xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_fullGaussianGramAt_posDef
      root shift hroot p r (by norm_num : (0 : ℝ) < 1)

/-- **Root-deleted dyadic Hilbert/graphic universality law.** One cofinite dyadic-depth
reconstruction is equivalent to complete rooted-incidence realization of every chosen edge family
over both differential bases, together with valuation-base invariance. No separate injectivity,
Gram, canonical-reconstruction, or differential-independence premise remains. -/
theorem
    xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_graphicNetworkUniversality
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (tail head : E → Fin (N + 1))
    (p r : Nat.Primes) :
    XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift p ↔
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
            (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) := by
  calc
    _ ↔
        XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
          root shift r :=
      xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_canonicalValuationReconstruction
        root shift hroot p r
    _ ↔ _ :=
      xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_graphicNetworkUniversality
        root shift hroot tail head r

/-- **Joint dyadic vertex/edge Hilbert phase.** Root-deleted dyadic-depth recovery together with
corrected Xi edge recovery is equivalent to distinct vertex labels and ordinary rooted graphic
independence of the chosen edge packet. -/
theorem
    xiMobiusRootDeletedDyadicPairDifferenceCofiniteHilbertPhase_iff_rootedIncidence
    {N d : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p r : Nat.Primes)
    (tail head : Fin d → Fin (N + 1)) :
    XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
          root shift p ∧
        XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
          shift tail head ↔
      Function.Injective shift ∧
        (rootedIncidenceMatroid (C := ℂ) root tail head).Indep Set.univ := by
  calc
    _ ↔
        XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
            root shift r ∧
          XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
            shift tail head :=
      and_congr
        (xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_canonicalValuationReconstruction
          root shift hroot p r)
        Iff.rfl
    _ ↔ _ :=
      xiTransverseRootDeletedCanonicalPairDifferenceCofiniteHilbertPhase_iff_rootedIncidence
        root shift hroot r tail head

/-- The joint raw even-Xi edge phase has the same exact dyadic/rooted-graphic classification. -/
theorem
    xiMobiusRootDeletedDyadicRawPairDifferenceCofiniteHilbertPhase_iff_rootedIncidence
    {N d : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p r : Nat.Primes)
    (tail head : Fin d → Fin (N + 1)) :
    XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
          root shift p ∧
        XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction
          shift tail head ↔
      Function.Injective shift ∧
        (rootedIncidenceMatroid (C := ℂ) root tail head).Indep Set.univ := by
  calc
    _ ↔
        XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
            root shift r ∧
          XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction
            shift tail head :=
      and_congr
        (xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_canonicalValuationReconstruction
          root shift hroot p r)
        Iff.rfl
    _ ↔ _ :=
      xiTransverseRootDeletedCanonicalRawPairDifferenceCofiniteHilbertPhase_iff_rootedIncidence
        root shift hroot r tail head

/-- **Dyadic/Kirchhoff universality law.** Root-deleted dyadic vertex recovery and corrected Xi
edge recovery hold together exactly when vertex labels are distinct and every complex circulation
conserved at all vertices vanishes. -/
theorem
    xiMobiusRootDeletedDyadicPairDifferenceCofiniteHilbertPhase_iff_vertexConservation
    {N d : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p r : Nat.Primes)
    (tail head : Fin d → Fin (N + 1)) :
    XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
          root shift p ∧
        XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
          shift tail head ↔
      Function.Injective shift ∧
        ∀ weight : Fin d → ℂ,
          (∀ v : Fin (N + 1),
            (∑ e, if head e = v then weight e else 0) =
              ∑ e, if tail e = v then weight e else 0) →
            ∀ e, weight e = 0 := by
  calc
    _ ↔
        XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
            root shift r ∧
          XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
            shift tail head :=
      and_congr
        (xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_canonicalValuationReconstruction
          root shift hroot p r)
        Iff.rfl
    _ ↔ _ :=
      xiTransverseRootDeletedCanonicalPairDifferenceCofiniteHilbertPhase_iff_vertexConservation
        root shift hroot r tail head

/-- **Universal root-deleted dyadic/canonical-incidence Hilbert phase.** Root-deleted dyadic
vertex recovery together with one injectively reparametrized corrected Xi edge reconstruction
simultaneously detects full vertex injectivity, raw edge recovery, positivity and positive volume
of the fixed canonical incidence Gram, exact incidence-coordinate dual recovery, and real
Kirchhoff rigidity. -/
theorem
    xiMobiusRootDeletedDyadicCanonicalIncidenceGramCofiniteHilbertPhase_reparam_iff
    {N d : ℕ}
    (root : Fin N) (shift : Fin N → ℕ) (hroot : shift root = 0)
    (p : Nat.Primes) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0)
    (tail head : Fin d → Fin N) :
    XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
          root shift p ∧
        XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
          (embed ∘ shift) tail head ↔
      Function.Injective shift ∧
        XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction
            shift tail head ∧
          (pointedCollisionIncidenceGram shift 0 tail head).PosDef ∧
          0 < (pointedCollisionIncidenceGram shift 0 tail head).det ∧
          PointedCollisionIncidenceCoordinateReconstruction
            shift 0 tail head ∧
          (∀ weight : Fin d → ℝ,
            (∀ q : pointedCollisionIncidenceVertex shift 0,
              (∑ e, if pointedCollisionIncidenceVertexOf shift 0
                  (head e) = q then weight e else 0) =
                ∑ e, if pointedCollisionIncidenceVertexOf shift 0
                  (tail e) = q then weight e else 0) →
              ∀ e, weight e = 0) := by
  exact and_congr
    (xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_injective
      root shift hroot p)
    (xiPairDifferenceCanonicalIncidenceGramCofiniteHilbertPhase_reparam_iff
      shift embed hinj hzero tail head)

/-- Root-deleted dyadic-depth recovery is exactly raw even-Xi single-defect recovery on the
canonical `root.succAbove` enumeration of the nonroot apertures. -/
theorem
    xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_rawRootedStarCofiniteHilbertReconstruction
    {N : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p : Nat.Primes) :
    XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift p ↔
      XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction
        (fun j : Fin N => shift (root.succAbove j)) := by
  calc
    _ ↔
        XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
          root shift p :=
      xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_canonicalValuationReconstruction
        root shift hroot p p
    _ ↔
        Function.Injective (fun j : Fin N => shift (root.succAbove j)) ∧
          ∀ j, shift (root.succAbove j) ≠ 0 := by
      rw [XiTransverseRootDeletedPrimeValuationCanonicalReconstruction,
        xiTransversePrimeValuationCanonicalReconstruction_iff_injective_ne_zero]
    _ ↔ _ :=
      (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff
        (fun j : Fin N => shift (root.succAbove j))).symm

/-- **Exact rooted-star matrix certificate.** Root-deleted dyadic cofinite recovery holds exactly
when the fixed canonical incidence Gram of the nonroot raw-Xi star is literally the identity. -/
theorem
    xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_rootedStarIncidenceGram_eq_one
    {N : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p : Nat.Primes) :
    XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift p ↔
      pointedCollisionIncidenceGram
          (xiShiftRootedStarLabel
            (fun j : Fin N => shift (root.succAbove j)))
          0 xiShiftRootedStarTail xiShiftRootedStarHead =
        (1 : Matrix (Fin N) (Fin N) ℝ) := by
  calc
    _ ↔
        XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction
          (fun j : Fin N => shift (root.succAbove j)) :=
      xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_rawRootedStarCofiniteHilbertReconstruction
        root shift hroot p
    _ ↔ _ :=
      xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_rootedStarIncidenceGram_eq_one
        (fun j : Fin N => shift (root.succAbove j))

/-- The canonical nonroot rooted-star incidence volume is exactly one in the root-deleted dyadic
recovery phase. -/
theorem
    xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_rootedStarIncidenceGram_det_eq_one
    {N : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p : Nat.Primes) :
    XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift p ↔
      (pointedCollisionIncidenceGram
          (xiShiftRootedStarLabel
            (fun j : Fin N => shift (root.succAbove j)))
          0 xiShiftRootedStarTail xiShiftRootedStarHead).det = 1 := by
  calc
    _ ↔
        XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction
          (fun j : Fin N => shift (root.succAbove j)) :=
      xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_rawRootedStarCofiniteHilbertReconstruction
        root shift hroot p
    _ ↔ _ := by
      simpa [Function.comp_def] using
        (xiRootedStarCanonicalIncidenceGram_reparam_det_eq_one_iff_rawReconstruction
          (fun j : Fin N => shift (root.succAbove j)) id
          Function.injective_id rfl).symm

/-- **Exact singular complement.** Failure of root-deleted dyadic recovery is equivalent to zero
canonical incidence volume of the nonroot rooted star. -/
theorem
    not_xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_rootedStarIncidenceGram_det_eq_zero
    {N : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p : Nat.Primes) :
    ¬XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift p ↔
      (pointedCollisionIncidenceGram
          (xiShiftRootedStarLabel
            (fun j : Fin N => shift (root.succAbove j)))
          0 xiShiftRootedStarTail xiShiftRootedStarHead).det = 0 := by
  calc
    _ ↔
        ¬XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction
          (fun j : Fin N => shift (root.succAbove j)) :=
      not_congr
        (xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_rawRootedStarCofiniteHilbertReconstruction
          root shift hroot p)
    _ ↔ _ := by
      simpa [Function.comp_def] using
        (xiRootedStarCanonicalIncidenceGram_reparam_det_eq_zero_iff_not_rawReconstruction
          (fun j : Fin N => shift (root.succAbove j)) id
          Function.injective_id rfl).symm

/-- **Root-deleted dyadic exact metric-fusion law.** One prime's cofinite dyadic-depth recovery on
the nonroot apertures is equivalent, at every independently chosen prime and under every
injective zero-preserving reparametrization, to the complete rooted-star incidence/valuation
certificate: corrected reconstruction, canonical valuation recovery, finite and completed
strict Grams, Gaussian separation, all cofinite prime-jet Gram realizations, exact cofinite
prime-jet dual recovery, positive incidence volume, coordinate reconstruction, and Kirchhoff
rigidity. -/
theorem
    xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_incidenceValuationExactMetricFusion
    {N : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p r : Nat.Primes)
    (embed : ℕ → ℕ) (hinj : Function.Injective embed)
    (hzero : embed 0 = 0) (m : ℕ) :
    XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift p ↔
      XiRootedStarIncidenceValuationExactMetricFusionCertificate
        (fun j : Fin N => shift (root.succAbove j)) embed r m := by
  calc
    _ ↔
        XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction
          (fun j : Fin N => shift (root.succAbove j)) :=
      xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_rawRootedStarCofiniteHilbertReconstruction
        root shift hroot p
    _ ↔ _ :=
      xiRootedStar_incidenceValuationExactMetricFusion_reparam_iff
        (fun j : Fin N => shift (root.succAbove j))
        embed hinj hzero r m

end

end RHTower
