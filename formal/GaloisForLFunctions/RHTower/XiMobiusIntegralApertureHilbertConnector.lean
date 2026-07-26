import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureSzegoMetric
import GaloisForLFunctions.RHTower.XiTransversePrimeSourceHilbertMetric
import GaloisForLFunctions.RHTower.XiTransverseValuationCanonicalReconstruction
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialInstances

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

open scoped UpperEndDifferentialInstances

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

/-- Exact continuous canonical recovery restricted to a finite integral aperture packet. -/
def XiMobiusPrimeIntegralApertureCanonicalReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) : Prop :=
  XiMobiusPrimeContinuousApertureCanonicalReconstruction
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

/-- Exact continuous canonical recovery on the integral slice occurs precisely away from zero
shifts and collisions. -/
theorem
    xiMobiusPrimeIntegralApertureCanonicalReconstruction_iff_injective_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    XiMobiusPrimeIntegralApertureCanonicalReconstruction shift p ↔
      Function.Injective shift ∧ ∀ j, shift j ≠ 0 := by
  rw [XiMobiusPrimeIntegralApertureCanonicalReconstruction,
    xiMobiusPrimeContinuousApertureCanonicalReconstruction_iff_injective_ne_zero]
  constructor
  · rintro ⟨hinjective, hnonzero⟩
    refine ⟨fun i j hij => hinjective (congrArg (fun a : ℕ => (a : ℝ)) hij), ?_⟩
    intro j hzero
    exact hnonzero j (by simp [hzero])
  · rintro ⟨hinjective, hnonzero⟩
    refine ⟨fun i j hij => hinjective (Nat.cast_injective hij), ?_⟩
    intro j hzero
    apply hnonzero j
    exact_mod_cast hzero

/-- Finite continuous canonical recovery and completed integral Möbius--Szegő strictness have
exactly the same phase. Natural-valued nonzero apertures automatically supply the positive
chamber required by completion. -/
theorem
    xiMobiusPrimeIntegralApertureCanonicalReconstruction_iff_szegoGram_posDef
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    XiMobiusPrimeIntegralApertureCanonicalReconstruction shift p ↔
      (xiMobiusPrimeIntegralApertureSzegoGramMatrix shift p).PosDef := by
  rw [xiMobiusPrimeIntegralApertureCanonicalReconstruction_iff_injective_ne_zero,
    xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_injective_ne_zero]

/-- **Continuous/integral exact-recovery connector.** Restricting continuous Möbius recovery to
natural apertures gives exactly the existing transverse first-valuation recovery phase. -/
theorem
    xiMobiusPrimeIntegralApertureCanonicalReconstruction_iff_transverseValuationCanonicalReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    XiMobiusPrimeIntegralApertureCanonicalReconstruction shift p ↔
      XiTransversePrimeValuationCanonicalReconstruction shift p := by
  rw [xiMobiusPrimeIntegralApertureCanonicalReconstruction_iff_injective_ne_zero,
    xiTransversePrimeValuationCanonicalReconstruction_iff_injective_ne_zero]

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

/-- **Continuous finite/cofinite exact-recovery connector.** Canonical coefficient recovery from
the first finite continuous valuation depths on the integral slice is equivalent to exact
prime-source shift-jet recovery after every finite deletion. -/
theorem
    xiMobiusPrimeIntegralApertureCanonicalReconstruction_iff_cofiniteApertureHilbertReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes) :
    XiMobiusPrimeIntegralApertureCanonicalReconstruction shift p ↔
      XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m := by
  rw [
    xiMobiusPrimeIntegralApertureCanonicalReconstruction_iff_transverseValuationCanonicalReconstruction,
    xiTransversePrimeValuationCanonicalReconstruction_iff_cofiniteApertureHilbertReconstruction]

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

/-- Differential independence of the Xi shift carriers is exactly finite continuous canonical
coefficient recovery on the integral aperture slice. -/
theorem
    xiTransverseShiftUpperEndCarrier_differentialIndependent_iff_mobiusIntegralApertureCanonicalReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ↔
      XiMobiusPrimeIntegralApertureCanonicalReconstruction shift p := by
  rw [
    xiTransverseShiftUpperEndCarrier_differentialIndependent_iff_canonicalValuationReconstruction,
    ←
      xiMobiusPrimeIntegralApertureCanonicalReconstruction_iff_transverseValuationCanonicalReconstruction]

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

/-- The same finite continuous recovery phase detects Xi shift independence after adjoining all
scalar prime-valuation layers. -/
theorem
    xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_mobiusIntegralApertureCanonicalReconstruction
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ↔
      XiMobiusPrimeIntegralApertureCanonicalReconstruction shift p := by
  rw [
    xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_canonicalValuationReconstruction,
    ←
      xiMobiusPrimeIntegralApertureCanonicalReconstruction_iff_transverseValuationCanonicalReconstruction]

end

end RHTower
