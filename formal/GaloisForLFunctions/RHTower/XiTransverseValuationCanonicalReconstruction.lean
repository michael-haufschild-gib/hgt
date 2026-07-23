import GaloisForLFunctions.HilbertMetric.PrescribedEvaluationReconstruction
import GaloisForLFunctions.RHTower.XiTransversePrimeSourceHilbertMetric

/-!
# Canonical finite-depth reconstruction of transverse Xi apertures

For an `N`-aperture packet, the first `N` valuation increments are not merely a witness of linear
independence.  Their fixed square sampling matrix has exact dual weights recovering every aperture
coefficient vector.  Such canonical recovery exists exactly away from zero shifts and collisions.

The resulting reconstruction phase is therefore identical to the finite and completed one-prime
Hilbert metrics, every cofinite prime-jet realization, and differential independence of the actual
upper-end Xi shift carriers over both coefficient fields.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HilbertMetric
open scoped BigOperators ComplexOrder Differential

local instance xiValuationReconstructionUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiValuationReconstructionUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiValuationReconstructionUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiValuationReconstructionUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiValuationReconstructionCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiValuationReconstructionCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

local instance xiValuationReconstructionAllValuationDifferential :
    Differential analyticScalarValuationLayerDifferentialField :=
  derivationClosedDifferential _
    (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
      (Set.range analyticScalarValuationLayerCarrier))

local instance xiValuationReconstructionAllValuationDifferentialAlgebra :
    DifferentialAlgebra analyticScalarValuationLayerDifferentialField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ =
      ((c′ : analyticScalarValuationLayerDifferentialField) : upperEndMeroField)
    rfl

/-- Real feature family formed from the canonical first `N` valuation increments. -/
def xiTransversePrimeValuationCanonicalFeature
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) : Fin N → Fin N → ℝ :=
  fun j e => xiTransversePrimeValuationIncrement (shift j) e p

/-- Exact dual isolation and coefficient recovery from the canonical first `N` valuation depths. -/
def XiTransversePrimeValuationCanonicalReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) : Prop :=
  PrescribedEvaluationDualReconstruction
    (xiTransversePrimeValuationCanonicalFeature shift p) id

/-- The prescribed real evaluation matrix is literally the existing arithmetic Schur sampling
matrix on the actual aperture disk nodes and boundary amplitudes. -/
theorem xiTransversePrimeValuationCanonicalEvaluationMatrix_eq_arithmeticSchurSamplingMatrix
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    evaluationMatrix (xiTransversePrimeValuationCanonicalFeature shift p) id =
      arithmeticSchurSamplingMatrix
        (fun j => xiTransversePrimeApertureDiskNode (shift j) p)
        (fun j => 1 - xiTransversePrimeApertureDiskNode (shift j) p) := by
  rfl

/-- **Exact canonical reconstruction classification.**  The fixed first `N` valuation depths
recover every aperture coefficient vector exactly iff the integral shifts have no collision and no
zero.  No chosen sampling nodes, linear-independence certificate, or Gram hypothesis remains. -/
theorem xiTransversePrimeValuationCanonicalReconstruction_iff_injective_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    XiTransversePrimeValuationCanonicalReconstruction shift p ↔
      Function.Injective shift ∧ ∀ j, shift j ≠ 0 := by
  constructor
  · intro hrec
    rw [XiTransversePrimeValuationCanonicalReconstruction,
      PrescribedEvaluationDualReconstruction] at hrec
    obtain ⟨dual, hdelta, _hrecovery⟩ := hrec
    constructor
    · intro i j hshift
      by_contra hij
      have hii :
          (∑ e, dual i e * xiTransversePrimeValuationIncrement (shift i) e p) = 1 := by
        simpa [xiTransversePrimeValuationCanonicalFeature] using hdelta i i
      have hij0 :
          (∑ e, dual i e * xiTransversePrimeValuationIncrement (shift j) e p) = 0 := by
        simpa [xiTransversePrimeValuationCanonicalFeature, hij] using hdelta i j
      have heq :
          (∑ e, dual i e * xiTransversePrimeValuationIncrement (shift i) e p) =
            ∑ e, dual i e * xiTransversePrimeValuationIncrement (shift j) e p := by
        apply Finset.sum_congr rfl
        intro e _
        rw [hshift]
      exact one_ne_zero (hii.symm.trans (heq.trans hij0))
    · intro j hzero
      have hjj :
          (∑ e, dual j e * xiTransversePrimeValuationIncrement (shift j) e p) = 1 := by
        simpa [xiTransversePrimeValuationCanonicalFeature] using hdelta j j
      have hsumZero :
          (∑ e, dual j e * xiTransversePrimeValuationIncrement (shift j) e p) = 0 := by
        simp [hzero, xiTransversePrimeValuationIncrement,
          xiTransversePrimeApertureDiskNode]
      exact one_ne_zero (hjj.symm.trans hsumZero)
  · rintro ⟨hinjective, hnonzero⟩
    apply (prescribedEvaluationDualReconstruction_iff_det_ne_zero
      (xiTransversePrimeValuationCanonicalFeature shift p) id).2
    rw [xiTransversePrimeValuationCanonicalEvaluationMatrix_eq_arithmeticSchurSamplingMatrix]
    apply arithmeticSchurSamplingMatrix_det_ne_zero
    · exact (xiTransversePrimeApertureDiskNode_injective p).comp hinjective
    · intro j
      apply sub_ne_zero.mpr
      exact ne_of_gt
        (xiTransversePrimeApertureDiskNode_lt_one
          (Nat.pos_of_ne_zero (hnonzero j)) p)

/-- Canonical coefficient reconstruction and the finite first-`N` valuation Gram have exactly the
same strict phase. -/
theorem xiTransversePrimeValuationCanonicalReconstruction_iff_valuationGram_posDef
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    XiTransversePrimeValuationCanonicalReconstruction shift p ↔
      (xiTransversePrimeValuationGramMatrix shift p).PosDef := by
  rw [xiTransversePrimeValuationCanonicalReconstruction_iff_injective_ne_zero,
    xiTransversePrimeValuationGramMatrix_posDef_iff_injective_ne_zero]

/-- Canonical coefficient reconstruction is also exactly the strict phase of the completed Hardy
valuation--Szegő metric. -/
theorem xiTransversePrimeValuationCanonicalReconstruction_iff_completedSzegoGram_posDef
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    XiTransversePrimeValuationCanonicalReconstruction shift p ↔
      (xiTransversePrimeValuationSzegoGramMatrix shift p).PosDef := by
  rw [xiTransversePrimeValuationCanonicalReconstruction_iff_injective_ne_zero,
    xiTransversePrimeValuationSzegoGramMatrix_posDef_iff_injective_ne_zero]

/-- Canonical recovery at one prime is equivalent to positive square realization of every
prime-jet packet after every finite deletion. -/
theorem xiTransversePrimeValuationCanonicalReconstruction_iff_cofiniteApertureGram
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) (m : ℕ) :
    XiTransversePrimeValuationCanonicalReconstruction shift p ↔
      ∀ forbidden : Set Nat.Primes, forbidden.Finite →
        ∃ points : Fin N × Fin (m + 1) → {r : Nat.Primes // r ∉ forbidden},
          (xiTransversePrimeJetApertureGram shift m forbidden points).PosDef := by
  rw [xiTransversePrimeValuationCanonicalReconstruction_iff_injective_ne_zero,
    xiTransversePrimeJetApertureGram_cofinite_posDef_iff_injective_ne_zero]

/-- Canonical recovery from one prime is equivalent to deletion-robust exact recovery of every
prime-source jet coefficient, not merely to existence of positive aperture Grams. -/
theorem
    xiTransversePrimeValuationCanonicalReconstruction_iff_cofiniteApertureHilbertReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) (m : ℕ) :
    XiTransversePrimeValuationCanonicalReconstruction shift p ↔
      XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m := by
  rw [xiTransversePrimeValuationCanonicalReconstruction_iff_injective_ne_zero,
    xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero]

/-- Differential independence of the actual Xi shift carriers over the rational-coordinate field
is exactly canonical finite-depth coefficient recoverability at one prime. -/
theorem
    xiTransverseShiftUpperEndCarrier_differentialIndependent_iff_canonicalValuationReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ↔
      XiTransversePrimeValuationCanonicalReconstruction shift p := by
  calc
    _ ↔ (xiTransversePrimeValuationGramMatrix shift p).PosDef :=
      xiTransverseShiftUpperEndCarrier_differentialIndependent_iff_onePrimeValuationGram_posDef
        shift p
    _ ↔ _ :=
      (xiTransversePrimeValuationCanonicalReconstruction_iff_valuationGram_posDef
        shift p).symm

/-- The same exact reconstruction criterion detects differential independence after adjoining all
scalar prime-valuation layers. -/
theorem
    xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_canonicalValuationReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ↔
      XiTransversePrimeValuationCanonicalReconstruction shift p := by
  calc
    _ ↔ (xiTransversePrimeValuationGramMatrix shift p).PosDef :=
      xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_onePrimeValuationGram_posDef
        shift p
    _ ↔ _ :=
      (xiTransversePrimeValuationCanonicalReconstruction_iff_valuationGram_posDef
        shift p).symm

end

end RHTower
