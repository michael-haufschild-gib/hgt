import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.AllApertureSourceRiemannRochAndCoercivityLaws
import GaloisForLFunctions.ArithmeticCompensationTheory.TheTranslationLawHasAnInverseSquareDeficit
import GaloisForLFunctions.BiScaleUncertainty.WeilLagCriticalDeficitEndpointAndLimitLaw

/-!
# All-Parity Critical-Deficit Identity, Vinogradov–Korobov Sobolev Floor, and Endpoint Attainment on the Scaling Surface

This module unites the hyperbolic-gauge critical-deficit explicit formula of `BiScaleUncertainty`,
the positive-definite horizon-resolvent energy of `ArithmeticCompensationTheory`, the pole-tilted
self-convolution factorization of `ArithmeticIncidencePositivity`, and the graded Sobolev source
cones of `ArithmeticCastelnuovoSeveri`:

1. **Exact All-Parity Horizon + Critical-Deficit Identity for `fullZeroForm` and `defect` (§1):**
   * For every `F ∈ C²_c(ℝ)` (with **no parity or vanishing-moment hypothesis**) and every shift
     `s ∈ ℝ`, the iterated hyperbolic gauge derivative `doubleGaugeDerivative (autocorr F) s`
     equals `-(autoCorrelation (deriv F) s + crossCorrelation F s - autoCorrelation F s / 4)`
     (`doubleGaugeDerivative_autocorr_eq`), and is bounded in absolute value by the sharp
     pole-tilted Sobolev norm `(1 / 4) ∫ F² + ∫ (F')²` (`abs_doubleGaugeDerivative_autocorr_le`).
   * On any cutoff `L ≥ 2A` beyond the support diameter of `F`, the polar autocorrelation integral
     `∫_0^L e^{-t/2} autocorr F t dt` is not an adversarial `O(A ∫ F²)` error: it equals
     `2 * horizonEnergy F ≥ 0` identically (`integral_exp_neg_half_mul_autocorr_eq_two_mul_horizonEnergy`).
   * Integrating `∫_0^L normalizedLogError t * gaugeDerivative (autocorr F) t dt` by parts against
     `ccmPrimeDeficitIncoming` (which vanishes at `0`) yields the **exact all-parity identity**
     (`fullZeroForm_eq_levy_add_horizon_add_criticalDeficit`,
     `scalingSubsurface_defect_eq_levy_add_horizon_add_criticalDeficit`):
     `fullZeroForm F = (gammaBracket 0 - 2) ∫ F² + biScaleLevyEnergy F + 4 * horizonEnergy F
       + 2 ∫_{0}^{2A} ccmPrimeDeficitIncoming t * doubleGaugeDerivative (autocorr F) t dt`,
     eliminating the `(2A + 5)` linear aperture loss of `TheWidthBoundsTheEnergyNormalisedWeilFloor`.

2. **Unconditional All-Parity Vinogradov–Korobov (`0 < ex < 3 / 5`) Sobolev Floor and Source
   Riemann–Roch (§2):**
   * Whereas pure `L²` coercivity on unrestricted `realTestsAt r` blows up doubly exponentially
     (`exists_l2SourceCone_realTestsAt_coercivity_le_doubleExp`) and previous sub-`e^r` bounds held
     only on `oddRealTestsAt r` at the de la Vallée Poussin rate `√r`, the exact all-parity
     critical-deficit identity combined with `exists_eventually_abs_ccmPrimeDeficitIncoming_le_vk`
     proves that for **every** `0 < ex < 3 / 5`, there exist `C ≥ 0` and `κ > 0` such that for
     **every** aperture `r > 0` and **every** `F ∈ realTestsAt r` (even, odd, and mixed parity),
     `-(C * e^{r - κ r^{ex}} * (∫ F² + ∫ (F')²)) ≤ fullZeroForm F`
     (`exists_fullZeroForm_ge_neg_vk_sobolev`), and `gradedSobolevSourceCone (-C e^{r - κ r^{ex}})`
     satisfies `RiemannRochAxiom` on `scalingSubsurface (realTestsAt r)` across all `r > 0`
     (`exists_gradedSobolevSourceCone_realTestsAt_riemannRoch_vk`).

3. **Exact Endpoint Attainment (`fullDefectFloorRates = oddDefectFloorRates = Ici zetaZeroWidth`),
   Slack-Free Sobolev Equivalence, and Aperture-Uniform `H¹` Self-Improvement (§3):**
   * Combining the `(1 + A)`-free all-parity lower bound with the universal endpoint theorem
     `exists_univ_abs_ccmPrimeDeficitIncoming_le_of_zetaZeroWidth_le` eliminates both the `β > σ`
     rate slack and the `(1 + A)` polynomial prefactor at every width `σ ≥ 0`:
     `zetaZeroWidth ≤ σ` holds if and only if there exists `C ≥ 0` such that
     `gradedSobolevSourceCone (-C e^{2σ r})` satisfies `RiemannRochAxiom` on `realTestsAt r`
     (and equivalently on `oddRealTestsAt r`) for all `r > 0`
     (`zetaZeroWidth_le_iff_endpoint_gradedSobolevSourceCone_riemannRoch`).
   * Consequently `fullDefectFloorRates = Ici zetaZeroWidth` and
     `oddDefectFloorRates = Ici zetaZeroWidth` (`fullDefectFloorRates_eq_Ici`,
     `oddDefectFloorRates_eq_Ici`), upgrading `fullDefectFloorRate_eq_zetaZeroWidth` and
     `oddDefectFloorRate_eq_zetaZeroWidth` from infimum equalities to exact minimum attainment
     (`isLeast_fullDefectFloorRates`, `isLeast_oddDefectFloorRates`).
   * At `σ = 0`, any aperture-independent `H¹` Sobolev defect floor `-C` across `r > 0`
     automatically self-improves to `C = 0` (`HodgeIndex` and `RiemannHypothesis`,
     `riemannHypothesis_iff_uniform_gradedSobolevSourceCone_riemannRoch`), and on any test class
     with bounded second-gauge oscillation `|doubleGaugeDerivative (autocorr F) t| ≤ K ∫ F²`, the
     plain `L²` Weil floor holds at exact rate `2 * zetaZeroWidth` with no `(1 + A)` factor
     (`exists_fullZeroForm_ge_neg_mass_of_zetaZeroWidth_le`).
-/

open Complex MeasureTheory Real Set Filter Topology Finset
open scoped Real ComplexConjugate
open Zeta23 RHTower GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticPositivityTheory
  GaloisForLFunctions.ArithmeticIncidencePositivity
  GaloisForLFunctions.ArithmeticCompensationTheory
  GaloisForLFunctions.SquareRootThreshold
  GaloisForLFunctions.BiScaleUncertainty
  GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
  GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

set_option autoImplicit false

/-! ### 1. Exact All-Parity Horizon + Critical-Deficit Identity and Pole-Tilted Sobolev Bound -/

/-- A gauge cutoff index whose logarithmic cutoff `log(N + 2)` strictly exceeds `2A`. -/
private def gaugeIdx (A : ℝ) : ℕ := ⌈Real.exp (2 * A)⌉₊ + 1

private theorem two_mul_lt_cutoff_gaugeIdx (A : ℝ) : 2 * A < cutoff (gaugeIdx A) := by
  have hc : Real.exp (2 * A) ≤ (⌈Real.exp (2 * A)⌉₊ : ℝ) := Nat.le_ceil _
  have hlt : Real.exp (2 * A) < ((gaugeIdx A + 2 : ℕ) : ℝ) := by
    have : ((gaugeIdx A + 2 : ℕ) : ℝ) = (⌈Real.exp (2 * A)⌉₊ : ℝ) + 3 := by
      simp [gaugeIdx]; ring
    rw [this]; linarith
  have hcut : cutoff (gaugeIdx A) = Real.log ((gaugeIdx A + 2 : ℕ) : ℝ) := rfl
  have hlog := Real.log_lt_log (Real.exp_pos _) hlt
  rw [Real.log_exp] at hlog
  rw [hcut]; exact hlog

/-- **Exact pole-tilted formula for `doubleGaugeDerivative (autocorr F)` across all parities.**
For every `F ∈ C²_c(ℝ)` and every shift `s ∈ ℝ`,
`doubleGaugeDerivative (autocorr F) s = -(autoCorrelation (deriv F) s + crossCorrelation F s - autoCorrelation F s / 4)`. -/
theorem doubleGaugeDerivative_autocorr_eq {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (s : ℝ) :
    doubleGaugeDerivative (ArchimedeanAnomaly.autocorr F) s =
      -(autoCorrelation (deriv F) s + crossCorrelation F s - autoCorrelation F s / 4) := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hF' : ContDiff ℝ 1 (deriv F) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) F from hF)).2.2
  have ha_eq : ArchimedeanAnomaly.autocorr F = autoCorrelation F := rfl
  have hg_eq : gaugeDerivative (ArchimedeanAnomaly.autocorr F) =
      fun u => crossCorrelation F u - autoCorrelation F u / 2 := by
    funext u
    rw [gaugeDerivative, ha_eq, deriv_autoCorrelation hF1 hFc]
  have hcc : HasDerivAt (crossCorrelation F) (-autoCorrelation (deriv F) s) s := by
    rw [← secondCrossCorr_eq_neg_autoCorrelation_deriv hF hFc s]
    exact hasDerivAt_crossCorrelation_of_contDiff hF1 hF' hFc s
  have hac : HasDerivAt (autoCorrelation F) (crossCorrelation F s) s :=
    hasDerivAt_autoCorrelation hF1 hFc s
  have hdg : deriv (gaugeDerivative (ArchimedeanAnomaly.autocorr F)) s =
      -autoCorrelation (deriv F) s - crossCorrelation F s / 2 := by
    rw [hg_eq]
    exact (hcc.sub (hac.div_const 2)).deriv
  rw [doubleGaugeDerivative, gaugeDerivative, hdg, hg_eq]
  ring

/-- **Pole-tilted self-convolution integral formula for `doubleGaugeDerivative (autocorr F)`.** -/
theorem doubleGaugeDerivative_autocorr_eq_poleTilted_integral {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (s : ℝ) :
    doubleGaugeDerivative (ArchimedeanAnomaly.autocorr F) s =
      -∫ x, (deriv F x + F x / 2) * (deriv F (x + s) - F (x + s) / 2) := by
  rw [doubleGaugeDerivative_autocorr_eq hF hFc s,
    autoCorrelation_deriv_add_crossCorrelation_sub_quarter_eq (hF.of_le (by norm_num)) hFc s]

/-- **Sharp pole-tilted `H¹` Sobolev bound on `doubleGaugeDerivative (autocorr F)` across all parities.**
For every `F ∈ C²_c(ℝ)` and every shift `s ∈ ℝ`,
`|doubleGaugeDerivative (autocorr F) s| ≤ (1 / 4) * ∫ F² + ∫ (F')²`. -/
theorem abs_doubleGaugeDerivative_autocorr_le {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (s : ℝ) :
    |doubleGaugeDerivative (ArchimedeanAnomaly.autocorr F) s| ≤
      (1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2 := by
  rw [doubleGaugeDerivative_autocorr_eq hF hFc s, abs_neg]
  exact abs_autoCorrelation_deriv_add_crossCorrelation_sub_quarter_le
    (hF.of_le (by norm_num)) hFc s

/-- **The polar autocorrelation integral on `[0, L]` (`2A ≤ L`) equals `2 * horizonEnergy F ≥ 0`.**
For any continuous compactly supported `F` vanishing outside `[-A, A]` (`0 ≤ A`) and any `L ≥ 2A`,
`∫_{0}^L e^{-t/2} autocorr F t dt = 2 * horizonEnergy F ≥ 0` with no parity assumption. -/
theorem integral_exp_neg_half_mul_autocorr_eq_two_mul_horizonEnergy
    {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    {A L : ℝ} (hA : 0 ≤ A) (hAL : 2 * A ≤ L) (hsupp : ∀ x : ℝ, A < |x| → F x = 0) :
    (∫ t in Icc 0 L, Real.exp (-t / 2) * ArchimedeanAnomaly.autocorr F t) =
      2 * horizonEnergy F := by
  have hL0 : 0 ≤ L := by linarith
  have ha_eq : ArchimedeanAnomaly.autocorr F = autoCorr F := rfl
  have hvan : ∀ t : ℝ, L < t → autoCorr F t = 0 := fun t ht => by
    rw [← ha_eq]
    refine autocorr_eq_zero_of_far hsupp ?_
    rw [abs_of_pos (by linarith)]
    linarith
  have hAcont : Continuous (autoCorr F) := continuous_autoCorr hF hFc
  have hAbnd : ∀ t : ℝ, |autoCorr F t| ≤ autoCorr F 0 := abs_autoCorr_le_autoCorr_zero hF hFc
  have hint_all : IntegrableOn (fun u => autoCorr F u * horizonDensity u) (Ioi 0) :=
    integrableOn_mul_horizonDensity hAcont hAbnd 0
  have hdisj : Disjoint (Ioc (0 : ℝ) L) (Ioi L) :=
    Set.disjoint_left.mpr fun _ hx hy => not_lt.mpr hx.2 hy
  have hzero_tail : (∫ u in Ioi L, autoCorr F u * horizonDensity u) = 0 := by
    have hcongr : ∀ u ∈ Ioi L, autoCorr F u * horizonDensity u = 0 := fun u hu => by
      rw [hvan u hu, zero_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
    simp
  have hsplit : horizonIntegral (autoCorr F) =
      ∫ u in Ioc 0 L, autoCorr F u * horizonDensity u := by
    rw [horizonIntegral, ← Set.Ioc_union_Ioi_eq_Ioi hL0,
      setIntegral_union hdisj measurableSet_Ioi
        (hint_all.mono_set Ioc_subset_Ioi_self) (hint_all.mono_set (Ioi_subset_Ioi hL0)),
      hzero_tail, add_zero]
  rw [horizonEnergy_eq_horizonIntegral_autoCorr hF hFc, hsplit,
    integral_Icc_eq_integral_Ioc, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [ha_eq, horizonDensity]
  ring

theorem integral_exp_neg_half_mul_autocorr_nonneg
    {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    {A L : ℝ} (hA : 0 ≤ A) (hAL : 2 * A ≤ L) (hsupp : ∀ x : ℝ, A < |x| → F x = 0) :
    0 ≤ ∫ t in Icc 0 L, Real.exp (-t / 2) * ArchimedeanAnomaly.autocorr F t := by
  rw [integral_exp_neg_half_mul_autocorr_eq_two_mul_horizonEnergy hF hFc hA hAL hsupp]
  exact mul_nonneg (by norm_num) (horizonEnergy_nonneg hF hFc)

/-- `ccmPrimeDeficitIncoming` vanishes at `0`. -/
theorem ccmPrimeDeficitIncoming_zero : ccmPrimeDeficitIncoming 0 = 0 := by
  simp [ccmPrimeDeficitIncoming, ccmLogChebyshevDeficitPrimitive]

/-- **Integration by parts on `[0, L]` (`w < L`) from `normalizedLogError` to `ccmPrimeDeficitIncoming`.**
Because `ccmPrimeDeficitIncoming 0 = 0` and `gaugeDerivative f` vanishes past `w`, both boundary
terms vanish identically on `[0, L]`, and the resulting integral localizes to `[0, w]`. -/
theorem integral_normalizedLogError_mul_gaugeDerivative_eq_incoming_Icc {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) {w L : ℝ} (hw0 : 0 ≤ w) (hwL : w < L)
    (hw : ∀ v : ℝ, w < |v| → f v = 0) :
    (∫ t in Icc 0 L, normalizedLogError t * gaugeDerivative f t) =
      ∫ t in Icc 0 w, ccmPrimeDeficitIncoming t * doubleGaugeDerivative f t := by
  have hL0 : 0 ≤ L := by linarith
  have hG : ContDiff ℝ 1 (gaugeDerivative f) := contDiff_one_gaugeDerivative hf
  have hAC : AbsolutelyContinuousOnInterval
      (fun t => ccmPrimeDeficitIncoming t * gaugeDerivative f t) 0 L :=
    (absolutelyContinuousOnInterval_ccmPrimeDeficitIncoming 0 L).fun_mul
      hG.contDiffOn.absolutelyContinuousOnInterval
  have hint := hAC.integral_deriv_eq_sub
  have hgL : gaugeDerivative f L = 0 :=
    gaugeDerivative_eq_zero_of_lt_abs hw (by rwa [abs_of_nonneg hL0])
  have hbd : ccmPrimeDeficitIncoming L * gaugeDerivative f L -
      ccmPrimeDeficitIncoming 0 * gaugeDerivative f 0 = 0 := by
    rw [hgL, ccmPrimeDeficitIncoming_zero, mul_zero, zero_mul, sub_self]
  rw [hbd] at hint
  have hae : (∫ t in (0 : ℝ)..L, deriv (fun s => ccmPrimeDeficitIncoming s * gaugeDerivative f s) t) =
      ∫ t in (0 : ℝ)..L, (ccmPrimeDeficitIncoming t * doubleGaugeDerivative f t -
        normalizedLogError t * gaugeDerivative f t) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_hasDerivAt_ccmPrimeDeficitIncoming] with t ht _
    have hGt : HasDerivAt (gaugeDerivative f) (deriv (gaugeDerivative f) t) t :=
      (hG.differentiable one_ne_zero t).hasDerivAt
    exact (ht.mul hGt).deriv.trans (by unfold doubleGaugeDerivative gaugeDerivative; ring)
  have hcont1 : Continuous (fun t => ccmPrimeDeficitIncoming t * doubleGaugeDerivative f t) :=
    continuous_ccmPrimeDeficitIncoming.mul (continuous_doubleGaugeDerivative hf)
  have hI1 : IntervalIntegrable
      (fun t => ccmPrimeDeficitIncoming t * doubleGaugeDerivative f t) volume 0 L :=
    hcont1.intervalIntegrable 0 L
  have hI2 : IntervalIntegrable
      (fun t => normalizedLogError t * gaugeDerivative f t) volume 0 L := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hL0]
    exact (integrableOn_normalizedLogError_Icc L).mul_continuousOn
      (continuous_gaugeDerivative (hf.of_le (by norm_num))).continuousOn isCompact_Icc
  rw [hae, intervalIntegral.integral_sub hI1 hI2, intervalIntegral.integral_of_le hL0,
    intervalIntegral.integral_of_le hL0, ← integral_Icc_eq_integral_Ioc,
    ← integral_Icc_eq_integral_Ioc] at hint
  have heq_L : (∫ t in Icc 0 L, normalizedLogError t * gaugeDerivative f t) =
      ∫ t in Icc 0 L, ccmPrimeDeficitIncoming t * doubleGaugeDerivative f t := by linarith
  rw [heq_L]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
    (Icc_subset_Icc_right hwL.le) fun t ht => ?_
  have hwt : w < t := not_le.mp fun htw => ht.2 ⟨ht.1.1, htw⟩
  rw [doubleGaugeDerivative_eq_zero_of_lt_abs hw (by rw [abs_of_pos (by linarith)]; exact hwt),
    mul_zero]

/-- **Exact All-Parity Horizon + Critical-Deficit Identity for `fullZeroForm F`:**
For every `F ∈ C²_c(ℝ)` vanishing outside `[-A, A]` (`0 ≤ A`, **no parity or moment assumption**),
`fullZeroForm F = (gammaBracket 0 - 2) ∫ F² + biScaleLevyEnergy F + 4 * horizonEnergy F
  + 2 ∫_{0}^{2A} ccmPrimeDeficitIncoming t * doubleGaugeDerivative (autocorr F) t dt`. -/
theorem fullZeroForm_eq_levy_add_horizon_add_criticalDeficit {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    {A : ℝ} (hA : 0 ≤ A) (hsupp : ∀ x : ℝ, A < |x| → F x = 0) :
    fullZeroForm F =
      (Zeta23.EF.gammaBracket 0 - 2) * (∫ x, F x ^ 2) +
        biScaleLevyEnergy F + 4 * horizonEnergy F +
        2 * ∫ t in Icc 0 (2 * A),
          ccmPrimeDeficitIncoming t *
            doubleGaugeDerivative (ArchimedeanAnomaly.autocorr F) t := by
  set N := gaugeIdx A
  set L := cutoff N
  have hLlt : 2 * A < L := two_mul_lt_cutoff_gaugeIdx A
  have hmass : ArchimedeanAnomaly.autocorr F 0 = ∫ x, F x ^ 2 :=
    RHTower.AutocorrelationKrein.autocorr_zero_eq F
  have hfar : ∀ v : ℝ, 2 * A < |v| → ArchimedeanAnomaly.autocorr F v = 0 :=
    fun _ => autocorr_eq_zero_of_far hsupp
  have hazero : ∀ x : ℝ, L ≤ x → ArchimedeanAnomaly.autocorr F x = 0 := fun x hx =>
    hfar x (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)]; linarith)
  have haC2 : ContDiff ℝ 2 (ArchimedeanAnomaly.autocorr F) := contDiff_autocorr hF hFc
  have haC1 : ContDiff ℝ 1 (ArchimedeanAnomaly.autocorr F) := haC2.of_le (by norm_num)
  have hJ : IntegrableOn
      (fun x => (ArchimedeanAnomaly.autocorr F 0 - ArchimedeanAnomaly.autocorr F x) *
        archLevySinhWeight x) (Ioi 0) :=
    integrableOn_biScaleLevyIntegrand hF hFc
  have hform : fullZeroForm F =
      Zeta23.EF.gammaBracket 0 * ArchimedeanAnomaly.autocorr F 0 + biScaleLevyEnergy F
        - 2 * fullPairing (ArchimedeanAnomaly.autocorr F) := by
    rw [fullZeroForm_eq_re_weilFullFunctional hF.continuous hFc]
    exact re_weilFullFunctional_eq_of_compact_finite_jump ⟨⟨F, hF.continuous⟩, hFc⟩ hJ
  have htrans : fullPairing (ArchimedeanAnomaly.autocorr F) =
      pairing N (ArchimedeanAnomaly.autocorr F) :=
    fullPairing_eq_pairing_of_tail _ N hazero
  have hstielt := pairing_eq_stieltjes_gauge (ArchimedeanAnomaly.autocorr F) haC1 N
  rw [hazero L le_rfl, mul_zero, add_zero] at hstielt
  have hhor := integral_exp_neg_half_mul_autocorr_eq_two_mul_horizonEnergy
    hF.continuous hFc hA hLlt.le hsupp
  have hibp := integral_normalizedLogError_mul_gaugeDerivative_eq_incoming_Icc
    haC2 (by positivity : (0 : ℝ) ≤ 2 * A) hLlt hfar
  rw [hform, htrans, hstielt, hhor, hibp, hmass]
  ring

/-- **Exact All-Parity Castelnuovo–Severi Defect Identity on `scalingSubsurface V` (`V ≤ realTestsAt r`).** -/
theorem scalingSubsurface_defect_eq_levy_add_horizon_add_criticalDeficit
    {r : ℝ} (hr : 0 ≤ r) {V : Submodule ℝ realTests} (hV : V ≤ realTestsAt r)
    (x : ℝ × ℝ × V) :
    (scalingSubsurface V).defect x x =
      (Zeta23.EF.gammaBracket 0 - 2) * (∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) +
        biScaleLevyEnergy (x.2.2.1 : ℝ → ℝ) + 4 * horizonEnergy (x.2.2.1 : ℝ → ℝ) +
        2 * ∫ t in Icc 0 (2 * r),
          ccmPrimeDeficitIncoming t *
            doubleGaugeDerivative (ArchimedeanAnomaly.autocorr (x.2.2.1 : ℝ → ℝ)) t := by
  set F : ℝ → ℝ := (x.2.2.1 : ℝ → ℝ)
  have hF : ContDiff ℝ 2 F := x.2.2.1.2.1
  have hFc : HasCompactSupport F := x.2.2.1.2.2
  have hsupp : ∀ u : ℝ, r < |u| → F u = 0 := fun u hu =>
    image_eq_zero_of_notMem_tsupport fun hmem =>
      not_le.mpr hu (abs_le.mpr (hV x.2.2.2 hmem))
  rw [scalingSubsurface_defect_self, weilPair_self_eq_fullZeroForm hF hFc]
  exact fullZeroForm_eq_levy_add_horizon_add_criticalDeficit hF hFc hr hsupp

/-- **`(2A + 5)`-Free All-Parity Lower Bound on `fullZeroForm F` via `∫_0^{2A} |ccmPrimeDeficitIncoming|`.**
Dropping the nonnegative archimedean terms `biScaleLevyEnergy F ≥ 0` and `4 * horizonEnergy F ≥ 0`
gives an aperture-factor-free lower bound controlled solely by the `L¹` norm of
`ccmPrimeDeficitIncoming` on `[0, 2A]` and the second-gauge-derivative bound `D₂`. -/
theorem fullZeroForm_ge_neg_of_doubleGaugeDerivative_le {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    {A D₂ : ℝ} (hA : 0 ≤ A) (hsupp : ∀ x : ℝ, A < |x| → F x = 0)
    (hD₂ : ∀ t : ℝ, |doubleGaugeDerivative (ArchimedeanAnomaly.autocorr F) t| ≤ D₂) :
    -((|Zeta23.EF.gammaBracket 0| + 2) * (∫ x, F x ^ 2) +
        2 * (∫ t in Icc 0 (2 * A), |ccmPrimeDeficitIncoming t|) * D₂) ≤
      fullZeroForm F := by
  have hD₂0 : 0 ≤ D₂ := (abs_nonneg _).trans (hD₂ 0)
  have hmass0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hlevy : 0 ≤ biScaleLevyEnergy F := biScaleLevyEnergy_nonneg hFc hF.continuous
  have hhor : 0 ≤ 4 * horizonEnergy F :=
    mul_nonneg (by norm_num) (horizonEnergy_nonneg hF.continuous hFc)
  have hgamma : -((|Zeta23.EF.gammaBracket 0| + 2) * ∫ x, F x ^ 2) ≤
      (Zeta23.EF.gammaBracket 0 - 2) * ∫ x, F x ^ 2 := by
    have hg := neg_abs_le (Zeta23.EF.gammaBracket 0)
    have hg' : -(|Zeta23.EF.gammaBracket 0| + 2) ≤ Zeta23.EF.gammaBracket 0 - 2 := by linarith
    simpa only [neg_mul] using mul_le_mul_of_nonneg_right hg' hmass0
  set g : ℝ → ℝ := fun t =>
    ccmPrimeDeficitIncoming t * doubleGaugeDerivative (ArchimedeanAnomaly.autocorr F) t
  have hg_cont : Continuous g :=
    continuous_ccmPrimeDeficitIncoming.mul
      (continuous_doubleGaugeDerivative (contDiff_autocorr hF hFc))
  have hint_abs : IntegrableOn (fun t => |ccmPrimeDeficitIncoming t| * D₂) (Icc 0 (2 * A)) :=
    (continuous_ccmPrimeDeficitIncoming.abs.integrableOn_Icc).mul_const D₂
  have hI_le : |∫ t in Icc 0 (2 * A), g t| ≤
      (∫ t in Icc 0 (2 * A), |ccmPrimeDeficitIncoming t|) * D₂ := by
    calc |∫ t in Icc 0 (2 * A), g t|
        ≤ ∫ t in Icc 0 (2 * A), |g t| := abs_integral_le_integral_abs
      _ ≤ ∫ t in Icc 0 (2 * A), |ccmPrimeDeficitIncoming t| * D₂ := by
          refine setIntegral_mono_on hg_cont.abs.integrableOn_Icc hint_abs
            measurableSet_Icc fun t _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hD₂ t) (abs_nonneg _)
      _ = (∫ t in Icc 0 (2 * A), |ccmPrimeDeficitIncoming t|) * D₂ :=
          MeasureTheory.integral_mul_const D₂ _
  have hI_lower : -((∫ t in Icc 0 (2 * A), |ccmPrimeDeficitIncoming t|) * D₂) ≤
      ∫ t in Icc 0 (2 * A), g t := (abs_le.mp hI_le).1
  rw [fullZeroForm_eq_levy_add_horizon_add_criticalDeficit hF hFc hA hsupp]
  linarith

/-- **Sharp All-Parity Sobolev Lower Bound on `fullZeroForm F` via `∫_0^{2A} |ccmPrimeDeficitIncoming|`.** -/
theorem fullZeroForm_ge_neg_criticalDeficit_L1_mul_sobolev {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    {A : ℝ} (hA : 0 ≤ A) (hsupp : ∀ x : ℝ, A < |x| → F x = 0) :
    -((|Zeta23.EF.gammaBracket 0| + 2) * (∫ x, F x ^ 2) +
        2 * (∫ t in Icc 0 (2 * A), |ccmPrimeDeficitIncoming t|) *
          ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2)) ≤
      fullZeroForm F :=
  fullZeroForm_ge_neg_of_doubleGaugeDerivative_le hF hFc hA hsupp
    (abs_doubleGaugeDerivative_autocorr_le hF hFc)

/-! ### 2. Unconditional All-Parity Vinogradov–Korobov Sobolev Floor and Source Riemann–Roch -/

/-- **Global Vinogradov–Korobov bound for `ccmPrimeDeficitIncoming` across all `T ≥ 0`.**
Upgrades `exists_eventually_abs_ccmPrimeDeficitIncoming_le_vk` from an eventual `atTop` bound to a
uniform global bound valid for every `T ≥ 0`. -/
theorem exists_forall_abs_ccmPrimeDeficitIncoming_le_vk
    {ex : ℝ} (h0 : 0 < ex) (h35 : ex < 3 / 5) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧
      ∀ T : ℝ, 0 ≤ T → |ccmPrimeDeficitIncoming T| ≤ C * Real.exp (T / 2 - κ * T ^ ex) := by
  obtain ⟨C₁, κ, hC₁, hκ, hev⟩ := exists_eventually_abs_ccmPrimeDeficitIncoming_le_vk h0 h35
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hev
  set T₁ : ℝ := max T₀ 1
  have hT₁_pos : 0 ≤ T₁ := zero_le_one.trans (le_max_right T₀ 1)
  obtain ⟨t_max, -, ht_max⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hT₁_pos) continuous_ccmPrimeDeficitIncoming.abs.continuousOn
  set M₀ : ℝ := |ccmPrimeDeficitIncoming t_max| * Real.exp (κ * T₁ ^ ex)
  refine ⟨max C₁ M₀, κ, le_max_of_le_left hC₁, hκ, fun T hT => ?_⟩
  rcases le_or_gt T T₁ with hle | hgt
  · have hmax : |ccmPrimeDeficitIncoming T| ≤ |ccmPrimeDeficitIncoming t_max| :=
      ht_max ⟨hT, hle⟩
    have hrpow : T ^ ex ≤ T₁ ^ ex := Real.rpow_le_rpow hT hle h0.le
    have hexp : 1 ≤ Real.exp (κ * T₁ ^ ex) * Real.exp (T / 2 - κ * T ^ ex) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    calc |ccmPrimeDeficitIncoming T|
        ≤ |ccmPrimeDeficitIncoming t_max| * 1 := by rw [mul_one]; exact hmax
      _ ≤ |ccmPrimeDeficitIncoming t_max| *
            (Real.exp (κ * T₁ ^ ex) * Real.exp (T / 2 - κ * T ^ ex)) :=
          mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
      _ = M₀ * Real.exp (T / 2 - κ * T ^ ex) := by dsimp [M₀]; ring
      _ ≤ max C₁ M₀ * Real.exp (T / 2 - κ * T ^ ex) :=
          mul_le_mul_of_nonneg_right (le_max_right C₁ M₀) (Real.exp_pos _).le
  · have hvk := hT₀ T ((le_max_left T₀ 1).trans hgt.le)
    exact hvk.trans (mul_le_mul_of_nonneg_right (le_max_left C₁ M₀) (Real.exp_pos _).le)

/-- Elementary polynomial domination `κ * r ^ ex - r / 2 ≤ κ + κ * (2 * κ + 1) ^ 3` for all `r ≥ 0`
when `0 < ex < 3 / 5` and `κ > 0`. -/
private theorem rpow_sub_half_le_const {ex κ r : ℝ} (h0 : 0 < ex) (h35 : ex < 3 / 5)
    (hκ : 0 < κ) (hr : 0 ≤ r) :
    κ * r ^ ex - r / 2 ≤ κ + κ * (2 * κ + 1) ^ 3 := by
  have hc3 : 0 ≤ κ * (2 * κ + 1) ^ 3 := by positivity
  rcases le_or_gt r 1 with hr1 | hr1
  · have hrp : r ^ ex ≤ 1 := Real.rpow_le_one hr hr1 h0.le
    nlinarith
  · have hrp : r ^ ex ≤ r ^ (3 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hr1.le h35.le
    set u : ℝ := r ^ (1 / 5 : ℝ)
    have hu0 : 0 ≤ u := Real.rpow_nonneg hr _
    have hu3 : u ^ (3 : ℕ) = r ^ (3 / 5 : ℝ) := by
      rw [← Real.rpow_natCast u 3, ← Real.rpow_mul hr]
      norm_num
    have hu5 : u ^ (5 : ℕ) = r := by
      rw [← Real.rpow_natCast u 5, ← Real.rpow_mul hr]
      norm_num
    rcases le_or_gt u (2 * κ + 1) with hu_le | hu_gt
    · have hp3 : u ^ 3 ≤ (2 * κ + 1) ^ 3 := pow_le_pow_left₀ hu0 hu_le 3
      rw [← hu3] at hrp
      nlinarith
    · have hu2 : 2 * κ ≤ u ^ 2 := by nlinarith
      have hmul : 2 * κ * u ^ 3 ≤ u ^ 2 * u ^ 3 :=
        mul_le_mul_of_nonneg_right hu2 (pow_nonneg hu0 3)
      have heq5 : u ^ 2 * u ^ 3 = r := by rw [← hu5]; ring
      rw [← hu3] at hrp
      nlinarith

/-- **Global Vinogradov–Korobov `L¹` bound for `ccmPrimeDeficitIncoming` on `[0, 2A]`.**
For every `0 < ex < 3 / 5`, there exist `C ≥ 0` and `κ > 0` such that for all `A ≥ 0`,
`∫_0^{2A} |ccmPrimeDeficitIncoming t| dt ≤ C * e^{A - κ A^{ex}}`. -/
theorem exists_integral_abs_ccmPrimeDeficitIncoming_le_vk
    {ex : ℝ} (h0 : 0 < ex) (h35 : ex < 3 / 5) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧
      ∀ A : ℝ, 0 ≤ A →
        (∫ t in Icc 0 (2 * A), |ccmPrimeDeficitIncoming t|) ≤
          C * Real.exp (A - κ * A ^ ex) := by
  obtain ⟨C₀, κ, hC₀, hκ, hpt⟩ := exists_forall_abs_ccmPrimeDeficitIncoming_le_vk h0 h35
  set M_κ : ℝ := κ + κ * (2 * κ + 1) ^ 3
  refine ⟨2 * C₀ * (Real.exp M_κ + 1), κ, by positivity, hκ, fun A hA => ?_⟩
  have hI_abs : IntervalIntegrable (fun t => |ccmPrimeDeficitIncoming t|) volume 0 (2 * A) :=
    continuous_ccmPrimeDeficitIncoming.abs.intervalIntegrable 0 (2 * A)
  have hsplit : (∫ t in Icc 0 (2 * A), |ccmPrimeDeficitIncoming t|) =
      (∫ t in (0 : ℝ)..A, |ccmPrimeDeficitIncoming t|) +
        ∫ t in A..(2 * A), |ccmPrimeDeficitIncoming t| := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : 0 ≤ 2 * A),
      ← intervalIntegral.integral_add_adjacent_intervals
        (continuous_ccmPrimeDeficitIncoming.abs.intervalIntegrable 0 A)
        (continuous_ccmPrimeDeficitIncoming.abs.intervalIntegrable A (2 * A))]
  have hprim : ∀ c : ℝ, ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => 2 * c * Real.exp (s / 2)) (c * Real.exp (t / 2)) t := fun c t => by
    have h1 : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) t := by
      simpa using (hasDerivAt_id' t).div_const 2
    refine (h1.exp.const_mul (2 * c)).congr_deriv ?_
    ring
  have h1 : (∫ t in (0 : ℝ)..A, |ccmPrimeDeficitIncoming t|) ≤ 2 * C₀ * Real.exp (A / 2) := by
    have hmono : (∫ t in (0 : ℝ)..A, |ccmPrimeDeficitIncoming t|) ≤
        ∫ t in (0 : ℝ)..A, C₀ * Real.exp (t / 2) := by
      refine intervalIntegral.integral_mono_on hA
        (continuous_ccmPrimeDeficitIncoming.abs.intervalIntegrable 0 A)
        (by apply Continuous.intervalIntegrable; fun_prop) fun t ht => ?_
      have hrp0 : 0 ≤ t ^ ex := Real.rpow_nonneg ht.1 _
      exact (hpt t ht.1).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith)) hC₀)
    have heval : (∫ t in (0 : ℝ)..A, C₀ * Real.exp (t / 2)) =
        2 * C₀ * (Real.exp (A / 2) - 1) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hprim C₀ t)
        (by apply Continuous.intervalIntegrable; fun_prop)]
      simp only [zero_div, Real.exp_zero]
      ring
    linarith [hmono, heval]
  have h2 : (∫ t in A..(2 * A), |ccmPrimeDeficitIncoming t|) ≤
      2 * C₀ * Real.exp (A - κ * A ^ ex) := by
    set c : ℝ := C₀ * Real.exp (-κ * A ^ ex)
    have hc0 : 0 ≤ c := by positivity
    have hmono : (∫ t in A..(2 * A), |ccmPrimeDeficitIncoming t|) ≤
        ∫ t in A..(2 * A), c * Real.exp (t / 2) := by
      refine intervalIntegral.integral_mono_on (by linarith)
        (continuous_ccmPrimeDeficitIncoming.abs.intervalIntegrable A (2 * A))
        (by apply Continuous.intervalIntegrable; fun_prop) fun t ht => ?_
      have hrp : A ^ ex ≤ t ^ ex := Real.rpow_le_rpow hA ht.1 h0.le
      calc |ccmPrimeDeficitIncoming t|
          ≤ C₀ * Real.exp (t / 2 - κ * t ^ ex) := hpt t (hA.trans ht.1)
        _ ≤ C₀ * Real.exp (t / 2 - κ * A ^ ex) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC₀
        _ = c * Real.exp (t / 2) := by
            dsimp [c]; rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    have heval : (∫ t in A..(2 * A), c * Real.exp (t / 2)) =
        2 * c * (Real.exp A - Real.exp (A / 2)) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hprim c t)
        (by apply Continuous.intervalIntegrable; fun_prop)]
      have h2A : (2 * A) / 2 = A := by ring
      rw [h2A]
      ring
    have hle_c : 2 * c * (Real.exp A - Real.exp (A / 2)) ≤ 2 * c * Real.exp A := by
      nlinarith [Real.exp_pos (A / 2)]
    have hcexp : 2 * c * Real.exp A = 2 * C₀ * Real.exp (A - κ * A ^ ex) := by
      dsimp [c]
      rw [show 2 * (C₀ * Real.exp (-κ * A ^ ex)) * Real.exp A =
        2 * C₀ * (Real.exp (-κ * A ^ ex) * Real.exp A) by ring, ← Real.exp_add]
      congr 2; ring
    linarith [hmono, heval, hle_c, hcexp]
  have hdom : Real.exp (A / 2) ≤ Real.exp M_κ * Real.exp (A - κ * A ^ ex) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [rpow_sub_half_le_const h0 h35 hκ hA])
  have h1' : 2 * C₀ * Real.exp (A / 2) ≤
      2 * C₀ * Real.exp M_κ * Real.exp (A - κ * A ^ ex) := by
    calc 2 * C₀ * Real.exp (A / 2)
        ≤ 2 * C₀ * (Real.exp M_κ * Real.exp (A - κ * A ^ ex)) :=
          mul_le_mul_of_nonneg_left hdom (by positivity)
      _ = 2 * C₀ * Real.exp M_κ * Real.exp (A - κ * A ^ ex) := by ring
  rw [hsplit]
  linarith [h1, h2, h1']

/-- **Unconditional All-Parity Vinogradov–Korobov Sobolev Weil Floor (`0 < ex < 3 / 5`):**
For every `0 < ex < 3 / 5`, there exist `C ≥ 0` and `κ > 0` such that for **every** `A ≥ 0` and
**every** `F ∈ C²_c(ℝ)` supported in `[-A, A]` (even, odd, and mixed parity alike),
`-(C * e^{A - κ A^{ex}} * (∫ F² + ∫ (F')²)) ≤ fullZeroForm F`. -/
theorem exists_fullZeroForm_ge_neg_vk_sobolev
    {ex : ℝ} (h0 : 0 < ex) (h35 : ex < 3 / 5) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧
      ∀ (A : ℝ), 0 ≤ A → ∀ (F : ℝ → ℝ), ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x : ℝ, A < |x| → F x = 0) →
        -(C * Real.exp (A - κ * A ^ ex) * ((∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2)) ≤
          fullZeroForm F := by
  obtain ⟨C₁, κ, hC₁, hκ, hL1⟩ := exists_integral_abs_ccmPrimeDeficitIncoming_le_vk h0 h35
  set M_κ : ℝ := κ + κ * (2 * κ + 1) ^ 3
  set C : ℝ := (|Zeta23.EF.gammaBracket 0| + 2) * Real.exp M_κ + 2 * C₁
  refine ⟨C, κ, by dsimp [C]; positivity, hκ, fun A hA F hF hFc hsupp => ?_⟩
  have hlow := fullZeroForm_ge_neg_criticalDeficit_L1_mul_sobolev hF hFc hA hsupp
  refine le_trans ?_ hlow
  apply neg_le_neg
  have hF0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hd0 : 0 ≤ ∫ x, deriv F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  set S : ℝ := (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2
  have hS0 : 0 ≤ S := add_nonneg hF0 hd0
  have hdom1 : 1 ≤ Real.exp M_κ * Real.exp (A - κ * A ^ ex) := by
    rw [← Real.exp_add]
    have hm := rpow_sub_half_le_const h0 h35 hκ hA
    exact Real.one_le_exp (by linarith)
  have hterm1 : (|Zeta23.EF.gammaBracket 0| + 2) * (∫ x, F x ^ 2) ≤
      (|Zeta23.EF.gammaBracket 0| + 2) * Real.exp M_κ * Real.exp (A - κ * A ^ ex) * S := by
    have hFS : (∫ x, F x ^ 2) ≤ S := by dsimp [S]; linarith
    calc (|Zeta23.EF.gammaBracket 0| + 2) * (∫ x, F x ^ 2)
        ≤ (|Zeta23.EF.gammaBracket 0| + 2) * (1 * S) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ (|Zeta23.EF.gammaBracket 0| + 2) *
            ((Real.exp M_κ * Real.exp (A - κ * A ^ ex)) * S) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hdom1 hS0) (by positivity)
      _ = (|Zeta23.EF.gammaBracket 0| + 2) * Real.exp M_κ * Real.exp (A - κ * A ^ ex) * S := by
          ring
  have hI0 : 0 ≤ ∫ t in Icc 0 (2 * A), |ccmPrimeDeficitIncoming t| :=
    setIntegral_nonneg measurableSet_Icc fun _ _ => abs_nonneg _
  have hterm2 : 2 * (∫ t in Icc 0 (2 * A), |ccmPrimeDeficitIncoming t|) *
        ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) ≤
      2 * C₁ * Real.exp (A - κ * A ^ ex) * S := by
    have hqS : (1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2 ≤ S := by dsimp [S]; linarith
    have hq0 : 0 ≤ (1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2 := by linarith [hF0, hd0]
    calc 2 * (∫ t in Icc 0 (2 * A), |ccmPrimeDeficitIncoming t|) *
          ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2)
        ≤ 2 * (C₁ * Real.exp (A - κ * A ^ ex)) * S := by
          have hm1 : (∫ t in Icc 0 (2 * A), |ccmPrimeDeficitIncoming t|) *
                ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) ≤
              (C₁ * Real.exp (A - κ * A ^ ex)) * S :=
            mul_le_mul (hL1 A hA) hqS hq0 (by positivity)
          linarith
      _ = 2 * C₁ * Real.exp (A - κ * A ^ ex) * S := by ring
  have hexpand : C * Real.exp (A - κ * A ^ ex) * S =
      (|Zeta23.EF.gammaBracket 0| + 2) * Real.exp M_κ * Real.exp (A - κ * A ^ ex) * S +
        2 * C₁ * Real.exp (A - κ * A ^ ex) * S := by
    dsimp [C]; ring
  rw [hexpand]
  linarith

/-- **Unconditional All-Parity Vinogradov–Korobov Graded Sobolev Source Riemann–Roch across All
Apertures `r > 0` (`realTestsAt r` and all `V ≤ realTestsAt r`):**
Although pure `L²` coercivity on `realTestsAt r` blows up doubly exponentially, in `H¹` Sobolev
normalization `gradedSobolevSourceCone (-C e^{r - κ r^{ex}})` satisfies `RiemannRochAxiom` across
the **entire unrestricted `realTestsAt r`** at every aperture `r > 0` for every `0 < ex < 3 / 5`. -/
theorem exists_gradedSobolevSourceCone_realTestsAt_riemannRoch_vk
    {ex : ℝ} (h0 : 0 < ex) (h35 : ex < 3 / 5) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧
      ∀ (r : ℝ), 0 < r → ∀ V : Submodule ℝ realTests, V ≤ realTestsAt r →
        (scalingSubsurface V).RiemannRochAxiom
          (gradedSobolevSourceCone (-C * Real.exp (r - κ * r ^ ex)) V) := by
  obtain ⟨C, κ, hC, hκ, hvk⟩ := exists_fullZeroForm_ge_neg_vk_sobolev h0 h35
  refine ⟨C, κ, hC, hκ, fun r hr V hV => ?_⟩
  rw [gradedSobolevSourceCone_riemannRoch_iff_weilPair_ge]
  intro f
  have hF : ContDiff ℝ 2 f.1.1 := f.1.2.1
  have hFc : HasCompactSupport f.1.1 := f.1.2.2
  have hsupp : ∀ u : ℝ, r < |u| → f.1.1 u = 0 := fun u hu =>
    image_eq_zero_of_notMem_tsupport fun hmem =>
      not_le.mpr hu (abs_le.mpr (hV f.2 hmem))
  rw [weilPair_self_eq_fullZeroForm hF hFc, neg_mul, neg_mul]
  exact hvk r hr.le f.1.1 hF hFc hsupp

/-! ### 3. Slack-Free Endpoint Attainment, Closed-Ray Rate Laws, and Uniform `H¹` Self-Improvement -/

/-- **`(1 + A)`-Free and Slack-Free Weil Floor at Every Strictly Positive Width `σ > 0`:**
Whenever `zetaZeroWidth ≤ σ` and `σ > 0`, there exists `C ≥ 0` such that for all `A ≥ 0`, every
`F ∈ C²_c(ℝ)` supported in `[-A, A]`, and every uniform bound `D₂` on
`|doubleGaugeDerivative (autocorr F)|`,
`-(C * e^{2σ A} * (∫ F² + D₂)) ≤ fullZeroForm F`. -/
theorem exists_fullZeroForm_ge_neg_of_zetaZeroWidth_le_pos {σ : ℝ}
    (hσ : 0 < σ) (hw : zetaZeroWidth ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 ≤ A → ∀ (F : ℝ → ℝ), ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x : ℝ, A < |x| → F x = 0) → ∀ (D₂ : ℝ),
      (∀ t : ℝ, |doubleGaugeDerivative (ArchimedeanAnomaly.autocorr F) t| ≤ D₂) →
      -(C * Real.exp (2 * σ * A) * ((∫ x, F x ^ 2) + D₂)) ≤ fullZeroForm F := by
  obtain ⟨B, hB, huniv⟩ := exists_univ_abs_ccmPrimeDeficitIncoming_le_of_zetaZeroWidth_le
  set C : ℝ := |Zeta23.EF.gammaBracket 0| + 2 + 2 * B / σ
  refine ⟨C, by dsimp [C]; positivity, fun A hA F hF hFc hsupp D₂ hD₂ => ?_⟩
  have hlow := fullZeroForm_ge_neg_of_doubleGaugeDerivative_le hF hFc hA hsupp hD₂
  refine le_trans ?_ hlow
  apply neg_le_neg
  have hD₂0 : 0 ≤ D₂ := (abs_nonneg _).trans (hD₂ 0)
  have hF0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hexp1 : 1 ≤ Real.exp (2 * σ * A) := Real.one_le_exp (by positivity)
  have hprim : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (B / σ) * Real.exp (σ * s))
      (B * Real.exp (σ * t)) t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => σ * s) σ t := by
      simpa only [mul_one] using (hasDerivAt_id' t).const_mul σ
    refine (h1.exp.const_mul (B / σ)).congr_deriv ?_
    field_simp
  have hI_le : (∫ t in Icc 0 (2 * A), |ccmPrimeDeficitIncoming t|) ≤
      (B / σ) * Real.exp (2 * σ * A) := by
    have hmono : (∫ t in Icc 0 (2 * A), |ccmPrimeDeficitIncoming t|) ≤
        ∫ t in Icc 0 (2 * A), B * Real.exp (σ * t) :=
      setIntegral_mono_on continuous_ccmPrimeDeficitIncoming.abs.integrableOn_Icc
        (by apply Continuous.integrableOn_Icc; fun_prop)
        measurableSet_Icc fun t ht => huniv hσ.le hw t ht.1
    have heval : (∫ t in Icc 0 (2 * A), B * Real.exp (σ * t)) =
        (B / σ) * (Real.exp (2 * σ * A) - 1) := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : 0 ≤ 2 * A),
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hprim t)
          (by apply Continuous.intervalIntegrable; fun_prop)]
      simp only [mul_zero, Real.exp_zero]
      have h2σA : σ * (2 * A) = 2 * σ * A := by ring
      rw [h2σA]
      ring
    rw [heval] at hmono
    exact hmono.trans (by nlinarith [div_nonneg hB.le hσ.le])
  set S : ℝ := (∫ x, F x ^ 2) + D₂
  have hS0 : 0 ≤ S := add_nonneg hF0 hD₂0
  have h1 : (|Zeta23.EF.gammaBracket 0| + 2) * (∫ x, F x ^ 2) ≤
      (|Zeta23.EF.gammaBracket 0| + 2) * Real.exp (2 * σ * A) * S := by
    calc (|Zeta23.EF.gammaBracket 0| + 2) * (∫ x, F x ^ 2)
        ≤ (|Zeta23.EF.gammaBracket 0| + 2) * (1 * S) :=
          mul_le_mul_of_nonneg_left (by dsimp [S]; linarith) (by positivity)
      _ ≤ (|Zeta23.EF.gammaBracket 0| + 2) * (Real.exp (2 * σ * A) * S) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp1 hS0) (by positivity)
      _ = (|Zeta23.EF.gammaBracket 0| + 2) * Real.exp (2 * σ * A) * S := by ring
  have h2 : 2 * (∫ t in Icc 0 (2 * A), |ccmPrimeDeficitIncoming t|) * D₂ ≤
      (2 * B / σ) * Real.exp (2 * σ * A) * S := by
    have hm : (∫ t in Icc 0 (2 * A), |ccmPrimeDeficitIncoming t|) * D₂ ≤
        ((B / σ) * Real.exp (2 * σ * A)) * S :=
      mul_le_mul hI_le (by dsimp [S]; linarith) hD₂0 (by positivity)
    calc 2 * (∫ t in Icc 0 (2 * A), |ccmPrimeDeficitIncoming t|) * D₂
        = 2 * ((∫ t in Icc 0 (2 * A), |ccmPrimeDeficitIncoming t|) * D₂) := by ring
      _ ≤ 2 * (((B / σ) * Real.exp (2 * σ * A)) * S) := by linarith
      _ = (2 * B / σ) * Real.exp (2 * σ * A) * S := by ring
  have hexpand : C * Real.exp (2 * σ * A) * S =
      (|Zeta23.EF.gammaBracket 0| + 2) * Real.exp (2 * σ * A) * S +
        (2 * B / σ) * Real.exp (2 * σ * A) * S := by
    dsimp [C]; ring
  rw [hexpand]
  linarith

/-- **`(1 + A)`-Free and Slack-Free `L²` Weil Floor on Bounded-Second-Gauge-Oscillation Classes
at All `σ ≥ 0` (Including `σ = 0` and `σ = zetaZeroWidth`):**
Sharpens `exists_fullZeroForm_ge_neg_mass_of_zetaZeroWidth_lt` simultaneously by reaching the
endpoint `σ = zetaZeroWidth` (`∀ σ ≥ 0, zetaZeroWidth ≤ σ → ...`) and removing the `(1 + A)`
linear prefactor. -/
theorem exists_fullZeroForm_ge_neg_mass_of_zetaZeroWidth_le {σ K : ℝ}
    (hσ : 0 ≤ σ) (hw : zetaZeroWidth ≤ σ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 ≤ A → ∀ (F : ℝ → ℝ), ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x : ℝ, A < |x| → F x = 0) →
      (∀ t : ℝ, |doubleGaugeDerivative (ArchimedeanAnomaly.autocorr F) t| ≤ K * ∫ x, F x ^ 2) →
      -(C * Real.exp (2 * σ * A) * ∫ x, F x ^ 2) ≤ fullZeroForm F := by
  rcases eq_or_lt_of_le hσ with rfl | hσ_pos
  · have hRH : RiemannHypothesis :=
      riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr (le_antisymm hw zetaZeroWidth_nonneg)
    have hpos := RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive.mp hRH
    refine ⟨0, le_rfl, fun A _ F hF hFc _ _ => ?_⟩
    simp only [zero_mul, neg_zero]
    rw [← weilPair_self_eq_fullZeroForm hF hFc]
    exact hpos F hF hFc
  · obtain ⟨C, hC, hfl⟩ := exists_fullZeroForm_ge_neg_of_zetaZeroWidth_le_pos hσ_pos hw
    refine ⟨C * (1 + K), by positivity, fun A hA F hF hFc hsupp hD₂ => ?_⟩
    have h := hfl A hA F hF hFc hsupp (K * ∫ x, F x ^ 2) hD₂
    have heq : C * Real.exp (2 * σ * A) * ((∫ x, F x ^ 2) + K * ∫ x, F x ^ 2) =
        C * (1 + K) * Real.exp (2 * σ * A) * ∫ x, F x ^ 2 := by ring
    rwa [heq] at h

/-- **Exact-Width (`σ = zetaZeroWidth`) `(1 + A)`-Free `L²` Weil Floor on Bounded-Second-Gauge-Oscillation
Classes.** -/
theorem exists_fullZeroForm_ge_neg_mass_at_zetaZeroWidth {K : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 ≤ A → ∀ (F : ℝ → ℝ), ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x : ℝ, A < |x| → F x = 0) →
      (∀ t : ℝ, |doubleGaugeDerivative (ArchimedeanAnomaly.autocorr F) t| ≤ K * ∫ x, F x ^ 2) →
      -(C * Real.exp (2 * zetaZeroWidth * A) * ∫ x, F x ^ 2) ≤ fullZeroForm F :=
  exists_fullZeroForm_ge_neg_mass_of_zetaZeroWidth_le zetaZeroWidth_nonneg le_rfl hK

/-- **Slack-Free Endpoint `H¹` Sobolev Defect Floor on `scalingSubsurface V` (`V ≤ realTestsAt r`)
for Every `σ ≥ 0` (Including `σ = 0` and `σ = zetaZeroWidth`):** -/
theorem exists_scalingSubsurface_sobolev_defect_floor_of_zetaZeroWidth_le {σ : ℝ}
    (hσ : 0 ≤ σ) (hw : zetaZeroWidth ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 < r → ∀ V : Submodule ℝ realTests, V ≤ realTestsAt r →
      ∀ x : ℝ × ℝ × V,
        -(C * Real.exp (2 * σ * r) *
            ((∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) + ∫ u, deriv (x.2.2.1 : ℝ → ℝ) u ^ 2)) ≤
          (scalingSubsurface V).defect x x := by
  rcases eq_or_lt_of_le hσ with rfl | hσ_pos
  · have hRH : RiemannHypothesis :=
      riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr (le_antisymm hw zetaZeroWidth_nonneg)
    have hpos := RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive.mp hRH
    refine ⟨0, le_rfl, fun r _ V _ x => ?_⟩
    simp only [zero_mul, neg_zero]
    rw [scalingSubsurface_defect_self]
    exact hpos (x.2.2.1 : ℝ → ℝ) x.2.2.1.2.1 x.2.2.1.2.2
  · obtain ⟨C₀, hC₀, hfl⟩ := exists_fullZeroForm_ge_neg_of_zetaZeroWidth_le_pos hσ_pos hw
    refine ⟨2 * C₀, by positivity, fun r hr V hV x => ?_⟩
    set F : ℝ → ℝ := (x.2.2.1 : ℝ → ℝ)
    have hF : ContDiff ℝ 2 F := x.2.2.1.2.1
    have hFc : HasCompactSupport F := x.2.2.1.2.2
    have hsupp : ∀ u : ℝ, r < |u| → F u = 0 := fun u hu =>
      image_eq_zero_of_notMem_tsupport fun hmem =>
        not_le.mpr hu (abs_le.mpr (hV x.2.2.2 hmem))
    set D₂ : ℝ := (1 / 4) * (∫ u, F u ^ 2) + ∫ u, deriv F u ^ 2
    have h := hfl r hr.le F hF hFc hsupp D₂ (abs_doubleGaugeDerivative_autocorr_le hF hFc)
    rw [scalingSubsurface_defect_self, weilPair_self_eq_fullZeroForm hF hFc]
    refine le_trans ?_ h
    apply neg_le_neg
    have hF0 : 0 ≤ ∫ u, F u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have hd0 : 0 ≤ ∫ u, deriv F u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have hsum : (∫ u, F u ^ 2) + D₂ ≤ 2 * ((∫ u, F u ^ 2) + ∫ u, deriv F u ^ 2) := by
      dsimp [D₂]; linarith
    calc C₀ * Real.exp (2 * σ * r) * ((∫ u, F u ^ 2) + D₂)
        ≤ C₀ * Real.exp (2 * σ * r) * (2 * ((∫ u, F u ^ 2) + ∫ u, deriv F u ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 2 * C₀ * Real.exp (2 * σ * r) * ((∫ u, F u ^ 2) + ∫ u, deriv F u ^ 2) := by ring

/-- **Slack-Free Endpoint Equivalence Between `zetaZeroWidth ≤ σ` (`σ ≥ 0`) and the `H¹` Sobolev
Castelnuovo–Severi Defect Floor at Exact Rate `σ` on `realTestsAt r` and `oddRealTestsAt r`.** -/
theorem zetaZeroWidth_le_iff_endpoint_sobolev_defect_floor {σ : ℝ} (hσ : 0 ≤ σ) :
    (zetaZeroWidth ≤ σ ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ x : ℝ × ℝ × realTestsAt r,
        -(C * Real.exp (2 * σ * r) *
            ((∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) + ∫ u, deriv (x.2.2.1 : ℝ → ℝ) u ^ 2)) ≤
          (scalingSubsurface (realTestsAt r)).defect x x) ∧
    (zetaZeroWidth ≤ σ ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ x : ℝ × ℝ × oddRealTestsAt r,
        -(C * Real.exp (2 * σ * r) *
            ((∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) + ∫ u, deriv (x.2.2.1 : ℝ → ℝ) u ^ 2)) ≤
          (scalingSubsurface (oddRealTestsAt r)).defect x x) := by
  constructor
  · constructor
    · intro hw
      obtain ⟨C, hC0, hC⟩ := exists_scalingSubsurface_sobolev_defect_floor_of_zetaZeroWidth_le hσ hw
      exact ⟨C, hC0, fun r hr x => hC r hr (realTestsAt r) le_rfl x⟩
    · rintro ⟨C, _, hC⟩
      exact zetaZeroWidth_le_of_scalingSubsurface_odd_sobolev_defect_floor hσ fun r hr x =>
        hC r hr (x.1, x.2.1, ⟨x.2.2.1, x.2.2.2.1⟩)
  · constructor
    · intro hw
      obtain ⟨C, hC0, hC⟩ := exists_scalingSubsurface_sobolev_defect_floor_of_zetaZeroWidth_le hσ hw
      exact ⟨C, hC0, fun r hr x => hC r hr (oddRealTestsAt r) (fun _ hf => hf.1) x⟩
    · rintro ⟨C, _, hC⟩
      exact zetaZeroWidth_le_of_scalingSubsurface_odd_sobolev_defect_floor hσ hC

/-- **Slack-Free Endpoint Equivalence Between `zetaZeroWidth ≤ σ` (`σ ≥ 0`) and All-Aperture
`RiemannRochAxiom` for `gradedSobolevSourceCone (-C e^{2σ r})` (`realTestsAt r` and `oddRealTestsAt r`).**
Eliminates the `∀ β > σ` universal quantifier of `zetaZeroWidth_le_iff_gradedSobolevSourceCone_riemannRoch`. -/
theorem zetaZeroWidth_le_iff_endpoint_gradedSobolevSourceCone_riemannRoch {σ : ℝ} (hσ : 0 ≤ σ) :
    (zetaZeroWidth ≤ σ ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
        (scalingSubsurface (realTestsAt r)).RiemannRochAxiom
          (gradedSobolevSourceCone (-C * Real.exp (2 * σ * r)) (realTestsAt r))) ∧
    (zetaZeroWidth ≤ σ ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
        (scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom
          (gradedSobolevSourceCone (-C * Real.exp (2 * σ * r)) (oddRealTestsAt r))) := by
  obtain ⟨hfull, hodd⟩ := zetaZeroWidth_le_iff_endpoint_sobolev_defect_floor hσ
  constructor
  · rw [hfull]
    refine exists_congr fun C => and_congr_right fun _ => forall_congr' fun r =>
      imp_congr_right fun _ => ?_
    rw [gradedSobolevSourceCone_riemannRoch_iff_weilPair_ge]
    constructor
    · intro h f
      have hx := h (0, 0, f)
      rw [scalingSubsurface_defect_self] at hx
      linarith
    · intro h x
      rw [scalingSubsurface_defect_self]
      have hf := h x.2.2
      linarith
  · rw [hodd]
    refine exists_congr fun C => and_congr_right fun _ => forall_congr' fun r =>
      imp_congr_right fun _ => ?_
    rw [gradedSobolevSourceCone_riemannRoch_iff_weilPair_ge]
    constructor
    · intro h f
      have hx := h (0, 0, f)
      rw [scalingSubsurface_defect_self] at hx
      linarith
    · intro h x
      rw [scalingSubsurface_defect_self]
      have hf := h x.2.2
      linarith

/-- **Exact Closed-Ray Theorem for `fullDefectFloorRates`:**
`fullDefectFloorRates = Ici zetaZeroWidth`, upgrading `fullDefectFloorRate_eq_zetaZeroWidth` from
an infimum equality to exact closed-ray identification and minimum attainment. -/
theorem fullDefectFloorRates_eq_Ici : fullDefectFloorRates = Ici zetaZeroWidth := by
  ext β
  rw [fullDefectFloorRates, mem_setOf_eq, Set.mem_Ici]
  constructor
  · rintro ⟨hβ, h⟩
    exact (zetaZeroWidth_le_iff_endpoint_sobolev_defect_floor hβ).1.mpr h
  · intro hw
    have hβ : 0 ≤ β := zetaZeroWidth_nonneg.trans hw
    exact ⟨hβ, (zetaZeroWidth_le_iff_endpoint_sobolev_defect_floor hβ).1.mp hw⟩

/-- **Exact Closed-Ray Theorem for `oddDefectFloorRates`:**
`oddDefectFloorRates = Ici zetaZeroWidth`, upgrading `oddDefectFloorRate_eq_zetaZeroWidth` from
an infimum equality to exact closed-ray identification and minimum attainment. -/
theorem oddDefectFloorRates_eq_Ici : oddDefectFloorRates = Ici zetaZeroWidth := by
  ext β
  rw [oddDefectFloorRates, mem_setOf_eq, Set.mem_Ici]
  constructor
  · rintro ⟨hβ, h⟩
    exact (zetaZeroWidth_le_iff_endpoint_sobolev_defect_floor hβ).2.mpr h
  · intro hw
    have hβ : 0 ≤ β := zetaZeroWidth_nonneg.trans hw
    exact ⟨hβ, (zetaZeroWidth_le_iff_endpoint_sobolev_defect_floor hβ).2.mp hw⟩

theorem isLeast_fullDefectFloorRates : IsLeast fullDefectFloorRates zetaZeroWidth := by
  rw [fullDefectFloorRates_eq_Ici]; exact isLeast_Ici

theorem isLeast_oddDefectFloorRates : IsLeast oddDefectFloorRates zetaZeroWidth := by
  rw [oddDefectFloorRates_eq_Ici]; exact isLeast_Ici

/-- **Aperture-Uniform `H¹` Sobolev Self-Improvement (`σ = 0`):**
`RiemannHypothesis` (and `scalingSurface.HodgeIndex`) holds if and only if there exists a single
aperture-independent constant `C ≥ 0` such that `gradedSobolevSourceCone (-C)` satisfies
`RiemannRochAxiom` across all apertures `r > 0` on `realTestsAt r` (or equivalently on
`oddRealTestsAt r`) — any bounded `H¹` defect floor `-C` across `r > 0` automatically self-improves
to `C = 0`. -/
theorem riemannHypothesis_iff_uniform_gradedSobolevSourceCone_riemannRoch :
    (RiemannHypothesis ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
        (scalingSubsurface (realTestsAt r)).RiemannRochAxiom
          (gradedSobolevSourceCone (-C) (realTestsAt r))) ∧
    (RiemannHypothesis ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
        (scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom
          (gradedSobolevSourceCone (-C) (oddRealTestsAt r))) := by
  have hw0 : RiemannHypothesis ↔ zetaZeroWidth ≤ 0 := by
    rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero]
    exact ⟨fun h => h.le, fun h => le_antisymm h zetaZeroWidth_nonneg⟩
  obtain ⟨hfull, hodd⟩ := zetaZeroWidth_le_iff_endpoint_gradedSobolevSourceCone_riemannRoch le_rfl
  simp only [mul_zero, zero_mul, Real.exp_zero, mul_one] at hfull hodd
  exact ⟨hw0.trans hfull, hw0.trans hodd⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
