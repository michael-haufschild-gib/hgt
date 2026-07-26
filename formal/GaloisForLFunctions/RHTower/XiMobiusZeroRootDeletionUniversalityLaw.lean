import GaloisForLFunctions.RHTower.XiMobiusDyadicTransverseMatroidUniversalityLaw
import GaloisForLFunctions.RHTower.XiRootDeletedGaussianGraphicConnector
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialInstances

/-!
# Zero-root deletion boundary for Xi--Möbius transverse observations

The full dyadic innovation treats the zero shift as a loop, whereas the rooted Xi network deletes
that distinguished vertex before testing its prime-jet metric.  For an injective packet with one
zero root this creates a sharp boundary: the full dyadic Gram is singular, but deletion of exactly
the root restores every cofinite metric certificate, one-matrix Gaussian positivity, and the
rooted incidence matroid over both differential bases.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder Differential

open scoped UpperEndDifferentialInstances

/-- **Xi--Möbius zero-root deletion universality law.**  A single distinguished zero shift is an
unavoidable loop for the full dyadic innovation, while its deletion leaves a complete positive
and graphic transverse network whenever the full shift packet is injective. -/
theorem xiMobius_zeroRootDeletion_dyadicSingular_gaussianGraphic
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin N) (shift : Fin N → ℕ) (hroot : shift root = 0)
    (hinjective : Function.Injective shift)
    (tail head : E → Fin N) (m : ℕ) (p : Nat.Primes)
    {t : ℝ} (ht : 0 < t) :
    ¬ (xiMobiusContinuousApertureDyadicInnovationGram 2
        (fun j => (shift j : ℝ))).PosDef ∧
      (∀ forbidden : Set Nat.Primes, forbidden.Finite →
        ∃ points : {v : Fin N // v ≠ root} × Fin (m + 1) →
            {r : Nat.Primes // r ∉ forbidden},
          (xiTransversePrimeJetApertureGram
            (fun v : {v : Fin N // v ≠ root} => shift v) m forbidden points).PosDef) ∧
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p t).PosDef ∧
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
  have hdyadic : ¬ (xiMobiusContinuousApertureDyadicInnovationGram 2
      (fun j => (shift j : ℝ))).PosDef := by
    intro hpos
    have hnonzero :=
      (xiMobiusIntegralApertureDyadicInnovationGram_posDef_iff_injective_ne_zero
        shift).1 hpos |>.2
    exact hnonzero root hroot
  have hgaussian :
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p t).PosDef :=
    (xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_iff_injective
      shift p ht).2 hinjective
  have hgraphic := xiTransverse_fullGaussianGramAt_graphicNetworkUniversality
    root shift hroot tail head m p ht hgaussian
  have hcofinite :=
    (xiTransverse_rootDeletedCofiniteApertureGram_iff_graphicNetworkUniversality
      root shift hroot tail head m p).2 hgraphic
  exact ⟨hdyadic, hcofinite, hgaussian,
    hgraphic.2.1, hgraphic.2.2.1, hgraphic.2.2.2⟩

/-- **Exact Xi--Möbius zero-root deletion boundary.** The zero root forces singularity of the
full dyadic innovation, cofinite dyadic-depth recovery, and both finite canonical recovery
interfaces. Deleting it restores both cofinite dyadic-depth and exact prime-jet dual recovery,
full Gaussian positivity, both rooted differential matroids, and valuation-base invariance. -/
theorem xiMobius_zeroRootDeletion_dyadicSingular_exactHilbert_gaussianGraphic
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin N) (shift : Fin N → ℕ) (hroot : shift root = 0)
    (hinjective : Function.Injective shift)
    (tail head : E → Fin N) (m : ℕ) (p : Nat.Primes)
    {t : ℝ} (ht : 0 < t) :
    ¬ (xiMobiusContinuousApertureDyadicInnovationGram 2
        (fun j => (shift j : ℝ))).PosDef ∧
      ¬ XiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction
        2 (fun j => (shift j : ℝ)) p ∧
      ¬ XiMobiusPrimeIntegralApertureCanonicalReconstruction shift p ∧
      ¬ XiTransversePrimeValuationCanonicalReconstruction shift p ∧
      XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift p ∧
      XiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction
        root shift m ∧
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p t).PosDef ∧
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
  have hbase :=
    xiMobius_zeroRootDeletion_dyadicSingular_gaussianGraphic
      root shift hroot hinjective tail head m p ht
  have hexact :
      XiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction
        root shift m :=
    (xiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction_iff_injective
      root shift hroot m).2 hinjective
  have hcontinuousFail :
      ¬ XiMobiusPrimeIntegralApertureCanonicalReconstruction shift p := by
    intro hreconstruct
    have hnonzero :=
      (xiMobiusPrimeIntegralApertureCanonicalReconstruction_iff_injective_ne_zero
        shift p).1 hreconstruct |>.2
    exact hnonzero root hroot
  have htransverseFail :
      ¬ XiTransversePrimeValuationCanonicalReconstruction shift p := by
    intro hreconstruct
    exact hcontinuousFail
      ((xiMobiusPrimeIntegralApertureCanonicalReconstruction_iff_transverseValuationCanonicalReconstruction
        shift p).2 hreconstruct)
  have hdyadicFail :
      ¬ XiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction
        2 (fun j => (shift j : ℝ)) p := by
    intro hreconstruct
    have hnonzero :=
      (xiMobiusPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_injective_ne_zero
        shift p).1 hreconstruct |>.2
    exact hnonzero root hroot
  have hdyadicDeleted :
      XiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction
        root shift p :=
    (xiMobiusRootDeletedPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_injective
      root shift hroot p).2 hinjective
  exact ⟨hbase.1, hdyadicFail, hcontinuousFail, htransverseFail,
    hdyadicDeleted, hexact, hbase.2.2.1, hbase.2.2.2.1,
    hbase.2.2.2.2.1, hbase.2.2.2.2.2⟩

end

end RHTower
