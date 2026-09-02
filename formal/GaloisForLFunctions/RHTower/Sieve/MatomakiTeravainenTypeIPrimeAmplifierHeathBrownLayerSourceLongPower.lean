import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownLayerSourceDivisorEnergy
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeILongCoefficientPowerEnergy

/-!
# Height-power long energy for the sharp source-saving Type-I layers

For fixed divisor-majorant data, the remaining long-coefficient polylogarithm is eventually paid by
an arbitrarily small positive height power.  Threshold-layer sparsity and both negative amplifier
powers are retained verbatim.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- One sharp source-height layer block with fixed long polylogarithms paid by height. -/
noncomputable def mtTypeIPrimeHeathBrownLayerSourceLongPowerBlockMomentBound
    (C₀ etaLong rhoLong etaLayer rho : ℝ) (A P ell N : ℕ) (T V : ℝ)
    (_r : Fin ell) : ℝ :=
  ((ell : ℝ) / V) *
    (2 * mtTypeIPrimeRaisedHeathBrownLayerSourceHeightRootBound
      P ell N T etaLayer rho) *
    Real.sqrt (mtTypeILongFourthHeightPowerBound C₀ etaLong rhoLong A T)

/-- One sharp divisor-energy block is bounded by its selected long height-power envelope. -/
theorem mtTypeIPrimeHeathBrownLayerSourceDivisorBlockMomentBound_le_longPower
    {C₀ etaLong rhoLong etaLayer C rho T V : ℝ}
    {w A P ell N : ℕ} (r : Fin ell)
    (hC₀ : 0 ≤ C₀) (hT : 1 ≤ T) (hV : 0 ≤ V)
    (hetaLayer : 0 < etaLayer)
    (hfactor : mtTypeILongCoefficientPolylogFactor C w T ≤ T ^ rhoLong) :
    mtTypeIPrimeHeathBrownLayerSourceDivisorBlockMomentBound
        C₀ etaLong etaLayer C rho w A P ell N T V r ≤
      mtTypeIPrimeHeathBrownLayerSourceLongPowerBlockMomentBound
        C₀ etaLong rhoLong etaLayer rho A P ell N T V r := by
  have hlong := mtTypeILongFourthDivisorBound_le_heightPower
    (eta := etaLong) (A := A) hC₀ hT hfactor
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
  rw [mtTypeIPrimeHeathBrownLayerSourceDivisorBlockMomentBound,
    mtTypeIPrimeHeathBrownLayerSourceLongPowerBlockMomentBound]
  exact mul_le_mul_of_nonneg_left hsqrt
    (mul_nonneg (div_nonneg (by positivity) hV) (mul_nonneg (by positivity) hroot))

/-- Literal source-scale sub-height receiver after every fixed long-coefficient polylogarithm is
absorbed into `T^(epsilon/100)`, with sharp layer sparsity unchanged. -/
theorem exists_eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_layer_sourceLongPower
    {epsilon etaLayer : ℝ} (hepsilon : 0 < epsilon) (hetaLayer : 0 < etaLayer)
    (C : ℝ) (w : ℕ) :
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
            mtTypeIPrimeHeathBrownLayerSourceLongPowerBlockMomentBound
              C₀ (epsilon / 100) (epsilon / 100) etaLayer (1 / alpha)
                A P ell N T V r := by
  obtain ⟨C₀, hC₀, hsource⟩ :=
    exists_eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_layer_sourceDivisorEnergy
      hepsilon hetaLayer
  have hfactor := eventually_mtTypeILongCoefficientPolylogFactor_le_rpow
    C w (show 0 < epsilon / 100 by linarith)
  obtain ⟨T₀, hfactorT₀⟩ := Filter.eventually_atTop.1 hfactor
  have hheight : ∀ᶠ X : ℝ in atTop, T₀ ≤ X ^ (1 / 4 : ℝ) :=
    (tendsto_rpow_atTop (show 0 < (1 / 4 : ℝ) by norm_num)).eventually_ge_atTop T₀
  refine ⟨C₀, hC₀, ?_⟩
  filter_upwards [hsource, hheight] with X hsourceX hheightX
  intro alpha T a A N N' halpha halpha2 hXT hTX hpoint
    hA hAT hN hNT hNN' hN'le
  dsimp only
  have hbase := hsourceX alpha T C w a A N N' halpha halpha2 hXT hTX
    hpoint hA hAT hN hNT hNN' hN'le
  have hT : (1 : ℝ) ≤ T :=
    (show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega)).trans hNT
  have hfactorT :
      mtTypeILongCoefficientPolylogFactor C w T ≤ T ^ (epsilon / 100) :=
    hfactorT₀ T (hheightX.trans hXT)
  have hV : 0 ≤ ((((mtTypeIPrimeScale X alpha ^
      mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T : ℕ) : ℝ)) ^
        (-epsilon / 10)) := Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ ∑ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T),
        mtTypeIPrimeHeathBrownLayerSourceDivisorBlockMomentBound
          C₀ (epsilon / 100) etaLayer C (1 / alpha) w A
            (mtTypeIPrimeScale X alpha)
            (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N T
            ((((mtTypeIPrimeScale X alpha ^
              mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T : ℕ) : ℝ)) ^
                (-epsilon / 10)) r := hbase
    _ ≤ _ := Finset.sum_le_sum fun r _ =>
      mtTypeIPrimeHeathBrownLayerSourceDivisorBlockMomentBound_le_longPower
        r hC₀.le hT hV hetaLayer hfactorT

end

end RHTower.Sieve
