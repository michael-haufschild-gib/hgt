import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownLayerSourceLongEnergy
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeILongCoefficientEnergy

/-!
# Divisor-energy absorption for the sharp source-saving Type-I layers

This module discharges the literal dyadic long-coefficient energy using its fixed divisor-function
majorant.  Sharp layer threshold and negative amplifier powers remain unchanged.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- One sharp source-height layer block with long energy replaced by its divisor envelope. -/
noncomputable def mtTypeIPrimeHeathBrownLayerSourceDivisorBlockMomentBound
    (C₀ etaLong etaLayer C rho : ℝ) (w A P ell N : ℕ) (T V : ℝ)
    (_r : Fin ell) : ℝ :=
  ((ell : ℝ) / V) *
    (2 * mtTypeIPrimeRaisedHeathBrownLayerSourceHeightRootBound
      P ell N T etaLayer rho) *
    Real.sqrt (mtTypeILongFourthDivisorBound C₀ etaLong C w A T)

/-- One sharp long-energy block is bounded by its literal divisor envelope. -/
theorem mtTypeIPrimeHeathBrownLayerSourceLongEnergyBlockMomentBound_le_divisor
    {C₀ etaLong etaLayer C rho T V : ℝ} (a : ℕ → ℂ)
    {w A P ell N : ℕ} (r : Fin ell)
    (hC₀ : 0 ≤ C₀) (hT : 1 ≤ T) (hV : 0 ≤ V)
    (hetaLayer : 0 < etaLayer) (hA : 1 ≤ A) (hAT : (A : ℝ) ≤ T)
    (hpoint : ∀ {n : ℕ}, 0 < n →
      ‖a n‖ ≤ C * ((n.divisors.card : ℝ) ^ w)) :
    mtTypeIPrimeHeathBrownLayerSourceLongEnergyBlockMomentBound
        C₀ etaLong etaLayer rho a A P ell N T V r ≤
      mtTypeIPrimeHeathBrownLayerSourceDivisorBlockMomentBound
        C₀ etaLong etaLayer C rho w A P ell N T V r := by
  have hlong := mtTypeILongFourthRpowEnergyBound_le_divisorBound
    (eta := etaLong) hC₀ hT hA hAT a hpoint
  have hsqrt := Real.sqrt_le_sqrt hlong
  have hroot : 0 ≤ mtTypeIPrimeRaisedHeathBrownLayerSourceHeightRootBound
      P ell N T etaLayer rho := by
    have hdivisor : 0 ≤ divisorBoundConst etaLayer :=
      (divisorBoundConst_pos hetaLayer).le
    rw [mtTypeIPrimeRaisedHeathBrownLayerSourceHeightRootBound]
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg hdivisor (Real.rpow_nonneg (zero_le_one.trans hT) _)))
      (by positivity)
  rw [mtTypeIPrimeHeathBrownLayerSourceLongEnergyBlockMomentBound,
    mtTypeIPrimeHeathBrownLayerSourceDivisorBlockMomentBound]
  exact mul_le_mul_of_nonneg_left hsqrt
    (mul_nonneg (div_nonneg (by positivity) hV) (mul_nonneg (by positivity) hroot))

/-- Literal source-scale sub-height receiver with sharp layer sparsity and all long coefficient
energy replaced by its divisor envelope. -/
theorem exists_eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_layer_sourceDivisorEnergy
    {epsilon etaLayer : ℝ} (hepsilon : 0 < epsilon) (hetaLayer : 0 < etaLayer) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ (alpha T C : ℝ) (w : ℕ) (a : ℕ → ℂ) (A N N' : ℕ),
        (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
        X ^ (1 / 4 : ℝ) ≤ T → T ≤ X →
        (∀ {n : ℕ}, 0 < n →
          ‖a n‖ ≤ C * ((n.divisors.card : ℝ) ^ w)) →
        1 ≤ A → (A : ℝ) ≤ T →
        2 ≤ N → (N : ℝ) ≤ T → N < N' → N' ≤ 2 * N →
        let P := mtTypeIPrimeScale X alpha
        let ell := mtTypeIPrimeDegree P T
        let V := (((P ^ ell : ℕ) : ℝ)) ^ (-epsilon / 10)
        (∫ t in mtTypeIPrimeSourceLargeSet P T epsilon,
            ‖mtWattCoefficientBlock a A t‖ ^ 2 *
              ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
          ∑ r : Fin ell,
            mtTypeIPrimeHeathBrownLayerSourceDivisorBlockMomentBound
              C₀ (epsilon / 100) etaLayer C (1 / alpha)
                w A P ell N T V r := by
  obtain ⟨C₀, hC₀, hsource⟩ :=
    exists_eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_layer_sourceLongEnergy
      hepsilon hetaLayer
  refine ⟨C₀, hC₀, ?_⟩
  filter_upwards [hsource] with X hsourceX
  intro alpha T C w a A N N' halpha halpha2 hXT hTX hpoint
    hA hAT hN hNT hNN' hN'le
  dsimp only
  have hbase := hsourceX alpha T a A N N' halpha halpha2 hXT hTX
    hA hN hNT hNN' hN'le
  have hT : (1 : ℝ) ≤ T :=
    (show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega)).trans hNT
  have hV : 0 ≤ ((((mtTypeIPrimeScale X alpha ^
      mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T : ℕ) : ℝ)) ^
        (-epsilon / 10)) := Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ ∑ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T),
        mtTypeIPrimeHeathBrownLayerSourceLongEnergyBlockMomentBound
          C₀ (epsilon / 100) etaLayer (1 / alpha) a A
            (mtTypeIPrimeScale X alpha)
            (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N T
            ((((mtTypeIPrimeScale X alpha ^
              mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T : ℕ) : ℝ)) ^
                (-epsilon / 10)) r := hbase
    _ ≤ _ := Finset.sum_le_sum fun r _ =>
      mtTypeIPrimeHeathBrownLayerSourceLongEnergyBlockMomentBound_le_divisor
        a r hC₀.le hT hV hetaLayer hA hAT hpoint

end

end RHTower.Sieve
