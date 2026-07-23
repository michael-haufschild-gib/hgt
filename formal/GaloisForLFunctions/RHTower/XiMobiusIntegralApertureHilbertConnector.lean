import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureSzegoMetric
import GaloisForLFunctions.RHTower.XiTransversePrimeSourceHilbertMetric

/-!
# Integral slice of the continuous Möbius aperture Hilbert metric

The continuous Möbius--Szegő source and the integral transverse valuation source use the same disk
nodes on positive integral apertures. Their completed local metrics differ only by the fixed
positive critical Möbius damping at the chosen prime.

Consequently the continuous real-aperture Gram, restricted to integral shifts, detects exactly the
same collision matroid as the finite valuation Gram, the cofinite prime-jet Gram supplied by
HTGeometry, and differential independence of the actual Xi upper-end shift carriers. This closes
the local continuous/integral/global Hilbert connector without adding a comparison hypothesis.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open Matrix
open scoped ComplexOrder Differential

local instance xiMobiusIntegralUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiMobiusIntegralUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiMobiusIntegralUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiMobiusIntegralUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiMobiusIntegralCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiMobiusIntegralCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

local instance xiMobiusIntegralAllValuationFieldDifferential :
    Differential analyticScalarValuationLayerDifferentialField :=
  derivationClosedDifferential _
    (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
      (Set.range analyticScalarValuationLayerCarrier))

local instance xiMobiusIntegralAllValuationFieldDifferentialAlgebra :
    DifferentialAlgebra analyticScalarValuationLayerDifferentialField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ =
      ((c′ : analyticScalarValuationLayerDifferentialField) : upperEndMeroField)
    rfl

/-- The continuous disk node restricts exactly to the transverse integral disk node. -/
theorem xiMobiusContinuousApertureDiskNode_nat_eq_transverse
    (a : ℕ) (p : Nat.Primes) :
    xiMobiusContinuousApertureDiskNode (a : ℝ) p =
      xiTransversePrimeApertureDiskNode a p := by
  unfold xiMobiusContinuousApertureDiskNode xiTransversePrimeApertureDiskNode
  norm_num

/-- **Pointwise integral-slice law.** On integral apertures, the continuous Möbius--Szegő metric
is the transverse valuation--Szegő metric multiplied by one prime-dependent critical damping. -/
theorem xiMobiusPrimeContinuousApertureSzegoMetric_nat_eq_damped_valuation
    (a b : ℕ) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureSzegoMetric (a : ℝ) (b : ℝ) p =
      (xiTransversePrimeApertureDiskNode 1 p /
          (1 + xiTransversePrimeApertureDiskNode 1 p)) ^ 2 *
        xiTransversePrimeValuationSzegoMetric a b p := by
  rw [xiMobiusPrimeContinuousApertureSzegoMetric,
    xiTransversePrimeValuationSzegoMetric,
    xiMobiusContinuousApertureDiskNode_nat_eq_transverse,
    xiMobiusContinuousApertureDiskNode_nat_eq_transverse]
  ring

/-- Continuous Möbius--Szegő Gram restricted to a finite integral aperture packet. -/
def xiMobiusPrimeIntegralApertureSzegoGramMatrix
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    Matrix (Fin N) (Fin N) ℝ :=
  xiMobiusPrimeContinuousApertureSzegoGramMatrix
    (fun j => (shift j : ℝ)) p

/-- **Exact continuous/transverse Gram connector.** The entire integral continuous-aperture Gram
is a fixed positive scalar multiple of the completed transverse valuation Gram. -/
theorem xiMobiusPrimeIntegralApertureSzegoGramMatrix_eq_smul_transverse
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    xiMobiusPrimeIntegralApertureSzegoGramMatrix shift p =
      (xiTransversePrimeApertureDiskNode 1 p /
          (1 + xiTransversePrimeApertureDiskNode 1 p)) ^ 2 •
        xiTransversePrimeValuationSzegoGramMatrix shift p := by
  ext i j
  simp only [xiMobiusPrimeIntegralApertureSzegoGramMatrix,
    xiMobiusPrimeContinuousApertureSzegoGramMatrix,
    xiTransversePrimeValuationSzegoGramMatrix, Matrix.smul_apply, smul_eq_mul]
  exact xiMobiusPrimeContinuousApertureSzegoMetric_nat_eq_damped_valuation
    (shift i) (shift j) p

/-- The integral slice of the continuous Gram is strictly positive exactly away from the literal
zero and collision strata. -/
theorem xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_injective_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    (xiMobiusPrimeIntegralApertureSzegoGramMatrix shift p).PosDef ↔
      Function.Injective shift ∧ ∀ j, shift j ≠ 0 := by
  rw [xiMobiusPrimeIntegralApertureSzegoGramMatrix,
    xiMobiusPrimeContinuousApertureSzegoGramMatrix_posDef_iff_injective_pos]
  constructor
  · rintro ⟨hinj, hpos⟩
    constructor
    · intro i j hij
      apply hinj
      exact congrArg (fun a : ℕ => (a : ℝ)) hij
    · intro j hzero
      have hj := hpos j
      simp [hzero] at hj
  · rintro ⟨hinj, hne⟩
    constructor
    · intro i j hij
      apply hinj
      exact Nat.cast_injective hij
    · intro j
      exact_mod_cast Nat.pos_of_ne_zero (hne j)

/-- Continuous integral and completed transverse valuation Grams have the same strict-positive
phase at every chosen prime. -/
theorem
    xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_transverseValuationSzegoGram_posDef
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    (xiMobiusPrimeIntegralApertureSzegoGramMatrix shift p).PosDef ↔
      (xiTransversePrimeValuationSzegoGramMatrix shift p).PosDef := by
  rw [xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_injective_ne_zero,
    xiTransversePrimeValuationSzegoGramMatrix_posDef_iff_injective_ne_zero]

/-- **Continuous/cofinite HTGeometry connector.** At every jet depth, strict positivity of the
continuous metric on the integral slice is equivalent to positive square realizability after every
finite deletion of prime rays. -/
theorem xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_cofiniteApertureGram
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes) :
    (xiMobiusPrimeIntegralApertureSzegoGramMatrix shift p).PosDef ↔
      ∀ forbidden : Set Nat.Primes, forbidden.Finite →
        ∃ points : Fin N × Fin (m + 1) → {r : Nat.Primes // r ∉ forbidden},
          (xiTransversePrimeJetApertureGram shift m forbidden points).PosDef := by
  calc
    (xiMobiusPrimeIntegralApertureSzegoGramMatrix shift p).PosDef ↔
        (xiTransversePrimeValuationSzegoGramMatrix shift p).PosDef :=
      xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_transverseValuationSzegoGram_posDef
        shift p
    _ ↔ _ :=
      xiTransversePrimeValuationSzegoGramMatrix_posDef_iff_cofiniteApertureGram
        shift m p

/-- **Continuous/exact-cofinite Hilbert connector.** Strict positivity of the continuous
Möbius--Szegő metric on the integral aperture slice is equivalent to deletion-robust exact
prime-source shift-jet reconstruction. -/
theorem
    xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_cofiniteApertureHilbertReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes) :
    (xiMobiusPrimeIntegralApertureSzegoGramMatrix shift p).PosDef ↔
      XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m := by
  calc
    _ ↔ (xiTransversePrimeValuationSzegoGramMatrix shift p).PosDef :=
      xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_transverseValuationSzegoGram_posDef
        shift p
    _ ↔ _ :=
      xiTransversePrimeValuationSzegoGramMatrix_posDef_iff_cofiniteApertureHilbertReconstruction
        shift m p

/-- **Continuous/global analytic connector.** Differential independence of the actual Xi shift
carriers is equivalent to strict positivity of their continuous Möbius--Szegő Gram restricted to
the integral aperture slice. -/
theorem
    xiTransverseShiftUpperEndCarrier_differentialIndependent_iff_mobiusIntegralApertureSzegoGram_posDef
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ↔
      (xiMobiusPrimeIntegralApertureSzegoGramMatrix shift p).PosDef := by
  calc
    DifferentialIndependent upperEndRationalCoordinateField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ↔
        (xiTransversePrimeValuationSzegoGramMatrix shift p).PosDef :=
      xiTransverseShiftUpperEndCarrier_differentialIndependent_iff_onePrimeValuationSzegoGram_posDef
        shift p
    _ ↔ (xiMobiusPrimeIntegralApertureSzegoGramMatrix shift p).PosDef :=
      (xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_transverseValuationSzegoGram_posDef
        shift p).symm

/-- The same continuous integral-aperture Gram detects independence after adjoining every scalar
prime-valuation layer to the differential base field. -/
theorem
    xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_mobiusIntegralApertureSzegoGram_posDef
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ↔
      (xiMobiusPrimeIntegralApertureSzegoGramMatrix shift p).PosDef := by
  calc
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ↔
        (xiTransversePrimeValuationSzegoGramMatrix shift p).PosDef :=
      xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_onePrimeValuationSzegoGram_posDef
        shift p
    _ ↔ (xiMobiusPrimeIntegralApertureSzegoGramMatrix shift p).PosDef :=
      (xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_transverseValuationSzegoGram_posDef
        shift p).symm

end


end RHTower
