import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureDyadicCofiniteHilbertReconstruction
import GaloisForLFunctions.RHTower.XiMobiusIntegralApertureHilbertConnector
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialInstances

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder Differential

open scoped UpperEndDifferentialInstances

/-- The unit-mesh dyadic innovation Gram on integral apertures has no radical beyond the literal
zero and collision strata. -/
theorem xiMobiusIntegralApertureDyadicInnovationGram_posDef_iff_injective_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) :
    (xiMobiusContinuousApertureDyadicInnovationGram 2
      (fun j => (shift j : ℝ))).PosDef ↔
      Function.Injective shift ∧ ∀ j, shift j ≠ 0 := by
  rw [xiMobiusContinuousApertureDyadicInnovationGram_posDef_iff_scaled_injective_pos]
  constructor
  · rintro ⟨hscaled, hpos⟩
    refine ⟨?_, ?_⟩
    · intro i j hij
      apply hscaled
      simp only
      rw [hij]
    · intro j hj
      simpa [hj] using hpos j
  · rintro ⟨hinj, hne⟩
    constructor
    · intro i j hij
      apply hinj
      have hcast : (shift i : ℝ) = shift j := by
        norm_num at hij ⊢
        linarith
      exact Nat.cast_injective hcast
    · intro j
      have hcastPos : 0 < (shift j : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (hne j)
      positivity

/-- One-prime cofinite dyadic-depth recovery on integral apertures detects exactly the same zero
and collision strata as the completed innovation Gram. -/
theorem
    xiMobiusPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_injective_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    XiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction
        2 (fun j => (shift j : ℝ)) p ↔
      Function.Injective shift ∧ ∀ j, shift j ≠ 0 := by
  rw [
    xiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction_iff_scaled_injective_ne_zero]
  constructor
  · rintro ⟨hscaled, hne⟩
    refine ⟨?_, ?_⟩
    · intro i j hij
      apply hscaled
      simp only
      rw [hij]
    · intro j hj
      apply hne j
      simp [hj]
  · rintro ⟨hinjective, hne⟩
    constructor
    · intro i j hij
      apply hinjective
      have hcast : (shift i : ℝ) = shift j := by
        norm_num at hij ⊢
        linarith
      exact Nat.cast_injective hcast
    · intro j hj
      apply hne j
      have hcast : (shift j : ℝ) = 0 := by
        norm_num at hj ⊢
        linarith
      exact_mod_cast hcast

/-- **Xi Möbius dyadic/transverse matroid universality law.** On every finite integral shift
packet, strict dyadic-refinement positivity, continuous Möbius--Szegő positivity, cofinite
prime-jet positivity, and differential independence over either valuation base all detect exactly
the same zero and parallel classes. -/
theorem xiMobiusIntegralAperture_dyadicTransverseMatroidUniversality
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes) :
    let D := (xiMobiusContinuousApertureDyadicInnovationGram 2
      (fun j => (shift j : ℝ))).PosDef
    (D ↔ (xiMobiusPrimeIntegralApertureSzegoGramMatrix shift p).PosDef) ∧
      (D ↔ DifferentialIndependent upperEndRationalCoordinateField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j))) ∧
      (D ↔ DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j))) ∧
      (D ↔ ∀ forbidden : Set Nat.Primes, forbidden.Finite →
        ∃ points : Fin N × Fin (m + 1) → {r : Nat.Primes // r ∉ forbidden},
          (xiTransversePrimeJetApertureGram shift m forbidden points).PosDef) := by
  dsimp only
  have hmetric :
      (xiMobiusContinuousApertureDyadicInnovationGram 2
          (fun j => (shift j : ℝ))).PosDef ↔
        (xiMobiusPrimeIntegralApertureSzegoGramMatrix shift p).PosDef :=
    (xiMobiusIntegralApertureDyadicInnovationGram_posDef_iff_injective_ne_zero
      shift).trans
      (xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_injective_ne_zero
        shift p).symm
  exact ⟨hmetric,
    hmetric.trans
      (xiTransverseShiftUpperEndCarrier_differentialIndependent_iff_mobiusIntegralApertureSzegoGram_posDef
        shift p).symm,
    hmetric.trans
      (xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_mobiusIntegralApertureSzegoGram_posDef
        shift p).symm,
    hmetric.trans
      (xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_cofiniteApertureGram
        shift m p)⟩

/-- **Exact Xi Möbius dyadic/transverse Hilbert universality.** Strict dyadic-refinement
positivity, continuous Möbius--Szegő positivity, continuous canonical recovery, cofinite
dyadic-depth recovery, transverse canonical recovery, differential independence over both
valuation bases, and exact prime-jet recovery after every finite prime deletion are one phase. -/
theorem xiMobiusIntegralAperture_dyadicTransverseExactHilbertUniversality
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes) :
    let D := (xiMobiusContinuousApertureDyadicInnovationGram 2
      (fun j => (shift j : ℝ))).PosDef
    (D ↔ (xiMobiusPrimeIntegralApertureSzegoGramMatrix shift p).PosDef) ∧
      (D ↔ XiMobiusPrimeIntegralApertureCanonicalReconstruction shift p) ∧
      (D ↔ XiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction
        2 (fun j => (shift j : ℝ)) p) ∧
      (D ↔ XiTransversePrimeValuationCanonicalReconstruction shift p) ∧
      (D ↔ DifferentialIndependent upperEndRationalCoordinateField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j))) ∧
      (D ↔ DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j))) ∧
      (D ↔ XiTransversePrimeJetApertureCofiniteHilbertReconstruction
        shift m) := by
  dsimp only
  have hmetric :
      (xiMobiusContinuousApertureDyadicInnovationGram 2
          (fun j => (shift j : ℝ))).PosDef ↔
        (xiMobiusPrimeIntegralApertureSzegoGramMatrix shift p).PosDef :=
    (xiMobiusIntegralApertureDyadicInnovationGram_posDef_iff_injective_ne_zero
      shift).trans
      (xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_injective_ne_zero
        shift p).symm
  have hrecovery :
      (xiMobiusContinuousApertureDyadicInnovationGram 2
          (fun j => (shift j : ℝ))).PosDef ↔
        XiMobiusPrimeIntegralApertureCanonicalReconstruction shift p :=
    hmetric.trans
      (xiMobiusPrimeIntegralApertureCanonicalReconstruction_iff_szegoGram_posDef
        shift p).symm
  have hdyadicRecovery :
      (xiMobiusContinuousApertureDyadicInnovationGram 2
          (fun j => (shift j : ℝ))).PosDef ↔
        XiMobiusPrimeContinuousApertureDyadicCofiniteHilbertReconstruction
          2 (fun j => (shift j : ℝ)) p :=
    (xiMobiusIntegralApertureDyadicInnovationGram_posDef_iff_injective_ne_zero
      shift).trans
      (xiMobiusPrimeIntegralApertureDyadicCofiniteHilbertReconstruction_iff_injective_ne_zero
        shift p).symm
  exact ⟨hmetric, hrecovery, hdyadicRecovery,
    hrecovery.trans
      (xiMobiusPrimeIntegralApertureCanonicalReconstruction_iff_transverseValuationCanonicalReconstruction
        shift p),
    hrecovery.trans
      (xiTransverseShiftUpperEndCarrier_differentialIndependent_iff_mobiusIntegralApertureCanonicalReconstruction
        shift p).symm,
    hrecovery.trans
      (xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_mobiusIntegralApertureCanonicalReconstruction
        shift p).symm,
    hrecovery.trans
      (xiMobiusPrimeIntegralApertureCanonicalReconstruction_iff_cofiniteApertureHilbertReconstruction
        shift m p)⟩

end

end RHTower
