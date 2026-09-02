import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownLayerSourceDensity

/-!
# Uniform power decay in the source-saving Type-I layers

The paper interval `alpha >= 1.0999` leaves a fixed gap in `1 - 1 / alpha`.  Combined with the
literal power window `T^(1/10) <= P^ell`, this turns the two variable amplifier powers into the
uniform height powers `T^(-9/2000)` and `T^(-9/8000)`.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Uniform gap in the source coefficient exponent. -/
theorem nine_hundredths_le_one_sub_one_div
    {alpha : ℝ} (halpha : (10999 / 10000 : ℝ) ≤ alpha) :
    (9 / 100 : ℝ) ≤ 1 - 1 / alpha := by
  have halphaPos : 0 < alpha := by norm_num at halpha ⊢; linarith
  have hinv : 1 / alpha ≤ (91 / 100 : ℝ) := by
    rw [div_le_iff₀ halphaPos]
    norm_num at halpha ⊢
    nlinarith
  linarith

/-- The half-power source term has a fixed negative height exponent. -/
theorem mtTypeIPrimeDegree_negativeHalf_le_heightDecay
    {P : ℕ} {T alpha : ℝ} (hP : 2 ≤ P) (hT : 1 ≤ T)
    (halpha : (10999 / 10000 : ℝ) ≤ alpha) :
    (((P ^ mtTypeIPrimeDegree P T : ℕ) : ℝ)) ^ (-(1 - 1 / alpha) / 2) ≤
      T ^ (-9 / 2000 : ℝ) := by
  have hgap := nine_hundredths_le_one_sub_one_div halpha
  have hexponent : -(1 - 1 / alpha) / 2 ≤ 0 := by linarith
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hTpowPos : 0 < T ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hTpos _
  have hwindow := (mtTypeIPrimeDegree_power_window hP hT).1
  have hbase := Real.rpow_le_rpow_of_nonpos hTpowPos hwindow hexponent
  rw [← Real.rpow_mul (zero_le_one.trans hT)] at hbase
  have hpower := Real.rpow_le_rpow_of_exponent_le hT
    (show (1 / 10 : ℝ) * (-(1 - 1 / alpha) / 2) ≤ -9 / 2000 by
      nlinarith)
  exact hbase.trans hpower

/-- The eighth-power source term has a fixed negative height exponent. -/
theorem mtTypeIPrimeDegree_negativeEighth_le_heightDecay
    {P : ℕ} {T alpha : ℝ} (hP : 2 ≤ P) (hT : 1 ≤ T)
    (halpha : (10999 / 10000 : ℝ) ≤ alpha) :
    (((P ^ mtTypeIPrimeDegree P T : ℕ) : ℝ)) ^ (-(1 - 1 / alpha) / 8) ≤
      T ^ (-9 / 8000 : ℝ) := by
  have hgap := nine_hundredths_le_one_sub_one_div halpha
  have hexponent : -(1 - 1 / alpha) / 8 ≤ 0 := by linarith
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hTpowPos : 0 < T ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hTpos _
  have hwindow := (mtTypeIPrimeDegree_power_window hP hT).1
  have hbase := Real.rpow_le_rpow_of_nonpos hTpowPos hwindow hexponent
  rw [← Real.rpow_mul (zero_le_one.trans hT)] at hbase
  have hpower := Real.rpow_le_rpow_of_exponent_le hT
    (show (1 / 10 : ℝ) * (-(1 - 1 / alpha) / 8) ≤ -9 / 8000 by
      nlinarith)
  exact hbase.trans hpower

/-- Source-density root with both remaining amplifier powers replaced by uniform height decay. -/
def mtTypeIPrimeRaisedHeathBrownLayerSourcePowerDecayRootBound
    (X : ℝ) (N : ℕ) (T eta : ℝ) : ℝ :=
  Real.sqrt (heathBrownLemma34Coefficient eta) *
    (divisorBoundConst eta * T ^ (4 * eta)) *
    (Real.exp (-(Real.log (Real.log X)) ^ 6) +
      Real.sqrt (T ^ (4 * eta) * T / ((N : ℝ) ^ 2)) *
        T ^ (-9 / 2000 : ℝ) +
      Real.sqrt (T ^ (4 * eta) * T ^ (3 / 4 : ℝ) / ((N : ℝ) ^ 2)) *
        T ^ (-9 / 8000 : ℝ))

/-- The prime-density root is eventually bounded by its fixed power-decay form. -/
theorem eventually_mtTypeIPrimeRaisedHeathBrownLayerSourceDensityRootBound_le_powerDecay :
    ∀ᶠ X : ℝ in atTop,
      ∀ alpha T : ℝ, (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
        X ^ (1 / 4 : ℝ) ≤ T →
        ∀ (N : ℕ) (eta : ℝ), 0 < eta →
          mtTypeIPrimeRaisedHeathBrownLayerSourceDensityRootBound
              X (mtTypeIPrimeScale X alpha)
              (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T)
              N T eta (1 / alpha) ≤
            mtTypeIPrimeRaisedHeathBrownLayerSourcePowerDecayRootBound
              X N T eta := by
  filter_upwards [eventually_mtTypeIPrimeScale_two_le,
    Filter.eventually_ge_atTop (1 : ℝ)] with X hPtwo hX
  intro alpha T halpha _halpha2 hXT N eta heta
  have halphaOne : (1 : ℝ) ≤ alpha := by norm_num at halpha ⊢; linarith
  have hT : (1 : ℝ) ≤ T := by
    have hquarter := Real.one_le_rpow hX (by norm_num : (0 : ℝ) ≤ 1 / 4)
    exact hquarter.trans hXT
  have hhalf := mtTypeIPrimeDegree_negativeHalf_le_heightDecay
    (hPtwo alpha halphaOne) hT halpha
  have heighth := mtTypeIPrimeDegree_negativeEighth_le_heightDecay
    (hPtwo alpha halphaOne) hT halpha
  have hprefactor :
      0 ≤ Real.sqrt (heathBrownLemma34Coefficient eta) *
        (divisorBoundConst eta * T ^ (4 * eta)) := by
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (divisorBoundConst_pos heta).le
        (Real.rpow_nonneg (zero_le_one.trans hT) _))
  have hhalfMul := mul_le_mul_of_nonneg_left hhalf
    (Real.sqrt_nonneg
      (T ^ (4 * eta) * T / ((N : ℝ) ^ 2)))
  have heighthMul := mul_le_mul_of_nonneg_left heighth
    (Real.sqrt_nonneg
      (T ^ (4 * eta) * T ^ (3 / 4 : ℝ) / ((N : ℝ) ^ 2)))
  rw [mtTypeIPrimeRaisedHeathBrownLayerSourceDensityRootBound,
    mtTypeIPrimeRaisedHeathBrownLayerSourcePowerDecayRootBound]
  apply mul_le_mul_of_nonneg_left _ hprefactor
  linarith

/-- One source power-decay block after every fixed long polylogarithm is paid by height. -/
noncomputable def mtTypeIPrimeHeathBrownLayerSourcePowerDecayBlockMomentBound
    (C₀ etaLong rhoLong etaLayer : ℝ) (X : ℝ)
    (A ell N : ℕ) (T V : ℝ) (_r : Fin ell) : ℝ :=
  ((ell : ℝ) / V) *
    (2 * mtTypeIPrimeRaisedHeathBrownLayerSourcePowerDecayRootBound
      X N T etaLayer) *
    Real.sqrt (mtTypeILongFourthHeightPowerBound C₀ etaLong rhoLong A T)

/-- Fixed-power root monotonicity lifts through one density/long-power block. -/
theorem mtTypeIPrimeHeathBrownLayerSourceDensityLongPowerBlockMomentBound_le_powerDecay
    {C₀ etaLong rhoLong etaLayer rho X T V : ℝ}
    {A P ell N : ℕ} (r : Fin ell)
    (hV : 0 ≤ V)
    (hroot : mtTypeIPrimeRaisedHeathBrownLayerSourceDensityRootBound
        X P ell N T etaLayer rho ≤
      mtTypeIPrimeRaisedHeathBrownLayerSourcePowerDecayRootBound
        X N T etaLayer) :
    mtTypeIPrimeHeathBrownLayerSourceDensityLongPowerBlockMomentBound
        C₀ etaLong rhoLong etaLayer rho X A P ell N T V r ≤
      mtTypeIPrimeHeathBrownLayerSourcePowerDecayBlockMomentBound
        C₀ etaLong rhoLong etaLayer X A ell N T V r := by
  rw [mtTypeIPrimeHeathBrownLayerSourceDensityLongPowerBlockMomentBound,
    mtTypeIPrimeHeathBrownLayerSourcePowerDecayBlockMomentBound]
  have hrootTwo :
      2 * mtTypeIPrimeRaisedHeathBrownLayerSourceDensityRootBound
          X P ell N T etaLayer rho ≤
        2 * mtTypeIPrimeRaisedHeathBrownLayerSourcePowerDecayRootBound
          X N T etaLayer :=
    mul_le_mul_of_nonneg_left hroot (by norm_num)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hrootTwo
      (div_nonneg (by positivity) hV))
    (Real.sqrt_nonneg _)

/-- Literal sub-height Type-I receiver with the ordered-prime density and both fixed power savings
inserted unconditionally. -/
theorem exists_eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_layer_sourcePowerDecay :
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
                mtTypeIPrimeHeathBrownLayerSourcePowerDecayBlockMomentBound
                  C₀ (epsilon / 100) (epsilon / 100) etaLayer
                    X A ell N T V r := by
  intro epsilon etaLayer hepsilon hetaLayer C w
  obtain ⟨C₀, hC₀, hsource⟩ :=
    exists_eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_layer_sourceDensity
      hepsilon hetaLayer C w
  refine ⟨C₀, hC₀, ?_⟩
  filter_upwards [hsource,
    eventually_mtTypeIPrimeRaisedHeathBrownLayerSourceDensityRootBound_le_powerDecay]
      with X hsourceX hdecayX
  intro alpha T a A N N' halpha halpha2 hXT hTX hpoint
    hA hAT hN hNT hNN' hN'le
  dsimp only
  have hbase := hsourceX alpha T a A N N' halpha halpha2 hXT hTX
    hpoint hA hAT hN hNT hNN' hN'le
  have hroot := hdecayX alpha T halpha halpha2 hXT N etaLayer hetaLayer
  have hV : 0 ≤ ((((mtTypeIPrimeScale X alpha ^
      mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T : ℕ) : ℝ)) ^
        (-epsilon / 10)) := Real.rpow_nonneg (by positivity) _
  exact hbase.trans (Finset.sum_le_sum fun r _ =>
    mtTypeIPrimeHeathBrownLayerSourceDensityLongPowerBlockMomentBound_le_powerDecay
      r hV hroot)

end

end RHTower.Sieve
