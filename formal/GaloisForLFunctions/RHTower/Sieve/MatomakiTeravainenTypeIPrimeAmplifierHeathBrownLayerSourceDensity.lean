import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierLayerPrimeDensity
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownLayerSourceLongPower

/-!
# Prime-density insertion in the source-saving Type-I layers

Brun--Titchmarsh supplies an exponentially small ordered-prime tuple density.  This module inserts
that saving into the literal source-height root and its long-power receiver without changing either
negative amplifier power.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Source-height root with exact ordered-prime density replaced by its sixth-power
iterated-logarithmic saving. -/
def mtTypeIPrimeRaisedHeathBrownLayerSourceDensityRootBound
    (X : ℝ) (P ell N : ℕ) (T eta rho : ℝ) : ℝ :=
  let M : ℝ := ((P ^ ell : ℕ) : ℝ)
  Real.sqrt (heathBrownLemma34Coefficient eta) *
    (divisorBoundConst eta * T ^ (4 * eta)) *
    (Real.exp (-(Real.log (Real.log X)) ^ 6) +
      Real.sqrt (T ^ (4 * eta) * T / ((N : ℝ) ^ 2)) *
        M ^ (-(1 - rho) / 2) +
      Real.sqrt (T ^ (4 * eta) * T ^ (3 / 4 : ℝ) / ((N : ℝ) ^ 2)) *
        M ^ (-(1 - rho) / 8))

/-- The exact source-height root is eventually bounded by its prime-density form, uniformly over
the paper's source schedule. -/
theorem eventually_mtTypeIPrimeRaisedHeathBrownLayerSourceHeightRootBound_le_density :
    ∀ᶠ X : ℝ in atTop,
      ∀ alpha T : ℝ, (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
        X ^ (1 / 4 : ℝ) ≤ T →
        ∀ (N : ℕ) (eta : ℝ), 0 < eta →
          mtTypeIPrimeRaisedHeathBrownLayerSourceHeightRootBound
              (mtTypeIPrimeScale X alpha)
              (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T)
              N T eta (1 / alpha) ≤
            mtTypeIPrimeRaisedHeathBrownLayerSourceDensityRootBound
              X (mtTypeIPrimeScale X alpha)
              (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T)
              N T eta (1 / alpha) := by
  filter_upwards
    [eventually_mtTypeIPrimeRaisedPrimeDensity_le_exp_neg_logLogSix,
      Filter.eventually_gt_atTop (0 : ℝ)] with X hdensity hX
  intro alpha T halpha halpha2 hXT N eta heta
  have hT0 : 0 ≤ T :=
    (Real.rpow_pos_of_pos hX (1 / 4 : ℝ)).le.trans hXT
  have hprefactor :
      0 ≤ Real.sqrt (heathBrownLemma34Coefficient eta) *
        (divisorBoundConst eta * T ^ (4 * eta)) := by
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (divisorBoundConst_pos heta).le (Real.rpow_nonneg hT0 _))
  have hdensity' := hdensity alpha T halpha halpha2 hXT
  rw [mtTypeIPrimeRaisedHeathBrownLayerSourceHeightRootBound,
    mtTypeIPrimeRaisedHeathBrownLayerSourceDensityRootBound]
  apply mul_le_mul_of_nonneg_left _ hprefactor
  linarith

/-- One prime-density source block after every fixed long polylogarithm is paid by height. -/
noncomputable def mtTypeIPrimeHeathBrownLayerSourceDensityLongPowerBlockMomentBound
    (C₀ etaLong rhoLong etaLayer rho : ℝ) (X : ℝ)
    (A P ell N : ℕ) (T V : ℝ) (_r : Fin ell) : ℝ :=
  ((ell : ℝ) / V) *
    (2 * mtTypeIPrimeRaisedHeathBrownLayerSourceDensityRootBound
      X P ell N T etaLayer rho) *
    Real.sqrt (mtTypeILongFourthHeightPowerBound C₀ etaLong rhoLong A T)

/-- Root monotonicity lifts directly through one long-power block. -/
theorem mtTypeIPrimeHeathBrownLayerSourceLongPowerBlockMomentBound_le_density
    {C₀ etaLong rhoLong etaLayer rho X T V : ℝ}
    {A P ell N : ℕ} (r : Fin ell)
    (hV : 0 ≤ V)
    (hroot : mtTypeIPrimeRaisedHeathBrownLayerSourceHeightRootBound
        P ell N T etaLayer rho ≤
      mtTypeIPrimeRaisedHeathBrownLayerSourceDensityRootBound
        X P ell N T etaLayer rho) :
    mtTypeIPrimeHeathBrownLayerSourceLongPowerBlockMomentBound
        C₀ etaLong rhoLong etaLayer rho A P ell N T V r ≤
      mtTypeIPrimeHeathBrownLayerSourceDensityLongPowerBlockMomentBound
        C₀ etaLong rhoLong etaLayer rho X A P ell N T V r := by
  rw [mtTypeIPrimeHeathBrownLayerSourceLongPowerBlockMomentBound,
    mtTypeIPrimeHeathBrownLayerSourceDensityLongPowerBlockMomentBound]
  have hrootTwo :
      2 * mtTypeIPrimeRaisedHeathBrownLayerSourceHeightRootBound
          P ell N T etaLayer rho ≤
        2 * mtTypeIPrimeRaisedHeathBrownLayerSourceDensityRootBound
          X P ell N T etaLayer rho :=
    mul_le_mul_of_nonneg_left hroot (by norm_num)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hrootTwo
      (div_nonneg (by positivity) hV))
    (Real.sqrt_nonneg _)

/-- Literal sub-height Type-I receiver with ordered-prime density and all long coefficient energy
inserted unconditionally. -/
theorem exists_eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_layer_sourceDensity :
    ∀ {epsilon etaLayer : ℝ}, 0 < epsilon → 0 < etaLayer →
      ∀ (C : ℝ) (w : ℕ),
        ∃ C₀ : ℝ, 0 < C₀ ∧
          ∀ᶠ X : ℝ in atTop,
            ∀ (alpha T : ℝ) (a : ℕ → ℂ) (A N N' : ℕ),
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
                mtTypeIPrimeHeathBrownLayerSourceDensityLongPowerBlockMomentBound
                  C₀ (epsilon / 100) (epsilon / 100) etaLayer (1 / alpha)
                    X A P ell N T V r := by
  intro epsilon etaLayer hepsilon hetaLayer C w
  obtain ⟨C₀, hC₀, hsource⟩ :=
    exists_eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_layer_sourceLongPower
      hepsilon hetaLayer C w
  refine ⟨C₀, hC₀, ?_⟩
  filter_upwards [hsource,
    eventually_mtTypeIPrimeRaisedHeathBrownLayerSourceHeightRootBound_le_density]
      with X hsourceX hdensityX
  intro alpha T a A N N' halpha halpha2 hXT hTX hpoint
    hA hAT hN hNT hNN' hN'le
  dsimp only
  have hbase := hsourceX alpha T a A N N' halpha halpha2 hXT hTX
    hpoint hA hAT hN hNT hNN' hN'le
  have hroot := hdensityX alpha T halpha halpha2 hXT N etaLayer hetaLayer
  have hV : 0 ≤ ((((mtTypeIPrimeScale X alpha ^
      mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T : ℕ) : ℝ)) ^
        (-epsilon / 10)) := Real.rpow_nonneg (by positivity) _
  exact hbase.trans (Finset.sum_le_sum fun r _ =>
    mtTypeIPrimeHeathBrownLayerSourceLongPowerBlockMomentBound_le_density
      r hV hroot)

end

end RHTower.Sieve
