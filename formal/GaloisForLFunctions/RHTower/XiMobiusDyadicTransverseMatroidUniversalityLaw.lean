import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureStrictDyadicLaw
import GaloisForLFunctions.RHTower.XiMobiusIntegralApertureHilbertConnector

namespace RHTower

noncomputable section

open GaloisForLFunctions
open scoped Differential

private theorem xiMobiusPrimeContinuousApertureSzegoMetric_zero_left
    (b : ℝ) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureSzegoMetric 0 b p = 0 := by
  simp [xiMobiusPrimeContinuousApertureSzegoMetric,
    xiMobiusContinuousApertureDiskNode]

private theorem xiMobiusContinuousApertureDyadicInnovation_zero_left
    (h b : ℝ) :
    xiMobiusContinuousApertureDyadicInnovation h 0 b = 0 := by
  simp [xiMobiusContinuousApertureDyadicInnovation,
    xiMobiusPrimeContinuousApertureDyadicInnovation,
    xiMobiusPrimeContinuousApertureSzegoMetric_zero_left]

/-- The unit-mesh dyadic innovation Gram on integral apertures has no radical beyond the literal
zero and collision strata. -/
theorem xiMobiusIntegralApertureDyadicInnovationGram_posDef_iff_injective_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) :
    (xiMobiusContinuousApertureDyadicInnovationGram 2
      (fun j => (shift j : ℝ))).PosDef ↔
      Function.Injective shift ∧ ∀ j, shift j ≠ 0 := by
  constructor
  · intro hgram
    constructor
    · intro i j hij
      by_contra hne
      have hrows :
          xiMobiusContinuousApertureDyadicInnovationGram 2
              (fun j => (shift j : ℝ)) i =
            xiMobiusContinuousApertureDyadicInnovationGram 2
              (fun j => (shift j : ℝ)) j := by
        funext k
        simp [xiMobiusContinuousApertureDyadicInnovationGram, hij]
      exact hgram.det_pos.ne' (Matrix.det_zero_of_row_eq hne hrows)
    · intro j hzero
      have hdiag := hgram.diag_pos (i := j)
      simp only [xiMobiusContinuousApertureDyadicInnovationGram] at hdiag
      simp [hzero, xiMobiusContinuousApertureDyadicInnovation_zero_left] at hdiag
  · rintro ⟨hinj, hne⟩
    have hcastInj : Function.Injective (fun j => (shift j : ℝ)) := by
      intro i j hij
      apply hinj
      exact_mod_cast hij
    have hcastPos : ∀ j, 0 < (shift j : ℝ) := by
      intro j
      exact_mod_cast Nat.pos_of_ne_zero (hne j)
    exact xiMobiusContinuousApertureDyadicInnovationGram_posDef
      (by norm_num) hcastInj hcastPos

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
  rw [xiMobiusIntegralApertureDyadicInnovationGram_posDef_iff_injective_ne_zero,
    xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_injective_ne_zero,
    xiTransverseShiftUpperEndCarrier_differentialIndependent_iff_mobiusIntegralApertureSzegoGram_posDef,
    xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_mobiusIntegralApertureSzegoGram_posDef,
    xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_cofiniteApertureGram]

end

end RHTower
