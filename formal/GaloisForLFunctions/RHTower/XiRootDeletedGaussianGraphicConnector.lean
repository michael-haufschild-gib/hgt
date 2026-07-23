import GaloisForLFunctions.RHTower.XiRootDeletedGaussianMetricConnector
import GaloisForLFunctions.RHTower.XiRootDeletedMetricGraphicNetworkUniversalityLaw

/-!
# One-Gaussian-certificate Xi graphic-network universality

The root-deleted prime-source theorem formerly consumed cofinite positive Gram realizations as a
hypothesis.  The exact metric connector identifies that interface with one full Gaussian Gram.
Thus a literal finite Hilbert matrix at one prime and one positive bandwidth already forces the
complete corrected edge network to realize the rooted incidence matroid over both differential
bases.  Conversely the resulting package records vertex injectivity, so the certificate is exact.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder Differential

local instance xiRootGaussianGraphicUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiRootGaussianGraphicUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiRootGaussianGraphicUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiRootGaussianGraphicUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiRootGaussianGraphicCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiRootGaussianGraphicCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

local instance xiRootGaussianGraphicAllValuationDifferential :
    Differential analyticScalarValuationLayerDifferentialField :=
  derivationClosedDifferential _
    (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
      (Set.range analyticScalarValuationLayerCarrier))

local instance xiRootGaussianGraphicAllValuationDifferentialAlgebra :
    DifferentialAlgebra analyticScalarValuationLayerDifferentialField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ =
      ((c′ : analyticScalarValuationLayerDifferentialField) : upperEndMeroField)
    rfl

/-- **Gaussian discharge of the root-deleted metric hypothesis.**  One positive full Gaussian
Gram supplies every cofinite nonroot prime-jet certificate needed by the graphic-network theorem,
and hence both rooted-incidence realizations plus valuation-base invariance. -/
theorem xiTransverse_fullGaussianGramAt_graphicNetworkUniversality
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin N) (shift : Fin N → ℕ) (hroot : shift root = 0)
    (tail head : E → Fin N) (m : ℕ) (p : Nat.Primes)
    {t : ℝ} (ht : 0 < t)
    (hgaussian :
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p t).PosDef) :
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
  apply xiTransverse_rootDeletedMetric_graphicNetworkUniversality
    root shift hroot tail head m
  exact
    (xiTransverse_rootDeletedCofiniteApertureGram_iff_fullGaussianGramAt_posDef
      root shift hroot m p ht).2 hgaussian

/-- **Exact one-matrix graphic-network classification.**  At any positive bandwidth, strict
positivity of one full Gaussian Gram is equivalent to the complete root-injective graphic
universality package over both differential bases. -/
theorem xiTransverse_fullGaussianGramAt_posDef_iff_graphicNetworkUniversality
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin N) (shift : Fin N → ℕ) (hroot : shift root = 0)
    (tail head : E → Fin N) (p : Nat.Primes) {t : ℝ} (ht : 0 < t) :
    (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p t).PosDef ↔
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
  constructor
  · exact xiTransverse_fullGaussianGramAt_graphicNetworkUniversality
      root shift hroot tail head 0 p ht
  · rintro ⟨hinjective, _hbase, _hall, _hinvariant⟩
    exact
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_iff_injective
        shift p ht).2 hinjective

/-- **Exact discharge of the cofinite metric interface.**  The original family of nonroot
prime-jet positivity certificates is equivalent to, rather than merely sufficient for, the full
root-injective graphic-network package over both coefficient fields. -/
theorem xiTransverse_rootDeletedCofiniteApertureGram_iff_graphicNetworkUniversality
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin N) (shift : Fin N → ℕ) (hroot : shift root = 0)
    (tail head : E → Fin N) (m : ℕ) (p : Nat.Primes) :
    (∀ forbidden : Set Nat.Primes, forbidden.Finite →
      ∃ points : {v : Fin N // v ≠ root} × Fin (m + 1) →
          {r : Nat.Primes // r ∉ forbidden},
        (xiTransversePrimeJetApertureGram
          (fun v : {v : Fin N // v ≠ root} => shift v) m forbidden points).PosDef) ↔
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
    _ ↔ (xiTransversePrimeFirstValuationGaussianGramMatrix shift p).PosDef :=
      xiTransverse_rootDeletedCofiniteApertureGram_iff_fullGaussianGram_posDef
        root shift hroot m p
    _ ↔ _ := by
      simpa only [xiTransversePrimeFirstValuationGaussianGramMatrix] using
        xiTransverse_fullGaussianGramAt_posDef_iff_graphicNetworkUniversality
          root shift hroot tail head p (by norm_num : (0 : ℝ) < 1)

/-- Unit-bandwidth form of the exact one-matrix graphic-network classification. -/
theorem xiTransverse_fullGaussianGram_posDef_iff_graphicNetworkUniversality
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin N) (shift : Fin N → ℕ) (hroot : shift root = 0)
    (tail head : E → Fin N) (p : Nat.Primes) :
    (xiTransversePrimeFirstValuationGaussianGramMatrix shift p).PosDef ↔
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
  simpa only [xiTransversePrimeFirstValuationGaussianGramMatrix] using
    xiTransverse_fullGaussianGramAt_posDef_iff_graphicNetworkUniversality
      root shift hroot tail head p (by norm_num : (0 : ℝ) < 1)

/-- **Exact-reconstruction discharge of graphic universality.**  Deletion-robust dual recovery
of all nonroot prime-jet coefficients is equivalent to the complete rooted-incidence matroid
package over both differential bases.  No separate Gram, injectivity, or independence hypothesis
remains in the interface. -/
theorem
    xiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction_iff_graphicNetworkUniversality
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin N) (shift : Fin N → ℕ) (hroot : shift root = 0)
    (tail head : E → Fin N) (m : ℕ) (p : Nat.Primes) :
    XiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction
        root shift m ↔
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
    _ ↔ (xiTransversePrimeFirstValuationGaussianGramMatrix shift p).PosDef :=
      xiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction_iff_fullGaussianGram_posDef
        root shift hroot m p
    _ ↔ _ :=
      xiTransverse_fullGaussianGram_posDef_iff_graphicNetworkUniversality
        root shift hroot tail head p

end

end RHTower
