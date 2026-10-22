import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPrimeAnomalyHaarCyclicity
import GaloisForLFunctions.RHTower.GaussHodgeWeilDeviationMoment
import GaloisForLFunctions.HTGeometry.WeightedDensityL2
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import GaloisForLFunctions.RHTower.L2MellinUnitary

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile HedenmalmPrimeTranslation HedenmalmIntervalAnomaly

namespace HedenmalmThetaSource

def criticalWeight (x : ℝ) : ℝ := Real.exp |x|

theorem measurable_criticalWeight : Measurable criticalWeight := by
  unfold criticalWeight
  fun_prop

theorem criticalWeight_pos (x : ℝ) : 0 < criticalWeight x := Real.exp_pos _

abbrev CriticalL2 := WeightedL2 (μ := (volume : Measure ℝ)) criticalWeight

def criticalFeatureRaw (z : ℂ) (x : ℝ) : ℂ :=
  (starRingEnd ℂ) (sourceChar z x) / (criticalWeight x : ℂ)

theorem continuous_criticalFeatureRaw (z : ℂ) : Continuous (criticalFeatureRaw z) := by
  unfold criticalFeatureRaw criticalWeight
  exact (continuous_sourceChar z).star.div (by fun_prop) fun x => by
    exact_mod_cast (Real.exp_ne_zero |x|)

theorem norm_sqrtWeight_criticalWeight (x : ℝ) :
    ‖sqrtWeight criticalWeight x‖ = Real.exp (|x| / 2) := by
  rw [sqrtWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (Real.exp_half |x|).symm

theorem norm_sqrtWeight_mul_criticalFeatureRaw (z : ℂ) (x : ℝ) :
    ‖sqrtWeight criticalWeight x * criticalFeatureRaw z x‖ ^ 2 =
      Real.exp (-|x| - 2 * z.im * x) := by
  rw [norm_mul, norm_sqrtWeight_criticalWeight, criticalFeatureRaw, norm_div,
    RCLike.norm_conj, norm_sourceChar, criticalWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), ← Real.exp_sub, ← Real.exp_add, ← Real.exp_nat_mul]
  congr 1
  ring_nf

theorem criticalFeatureRaw_memLp {z : ℂ} (hz : |z.im| < 1 / 2) :
    MemLp (criticalFeatureRaw z) 2
      ((volume : Measure ℝ).withDensity (realDensity criticalWeight)) := by
  rw [memLp_two_withDensity_iff measurable_criticalWeight criticalWeight_pos]
  apply (memLp_two_iff_integrable_sq_norm
    ((measurable_sqrtWeight measurable_criticalWeight).aestronglyMeasurable.mul
      (continuous_criticalFeatureRaw z).aestronglyMeasurable)).2
  have hc : 0 < 1 - 2 * |z.im| := by linarith
  refine Integrable.mono' (integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hc) ?_ ?_
  · have hsw : Continuous (sqrtWeight criticalWeight) := by
      unfold sqrtWeight criticalWeight
      fun_prop
    exact ((hsw.mul (continuous_criticalFeatureRaw z)).norm.pow 2).aestronglyMeasurable
  · filter_upwards with x
    change ‖‖sqrtWeight criticalWeight x * criticalFeatureRaw z x‖ ^ 2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    rw [norm_sqrtWeight_mul_criticalFeatureRaw]
    refine Real.exp_le_exp.2 ?_
    have hx : -2 * z.im * x ≤ 2 * |z.im| * |x| := by
      calc -2 * z.im * x ≤ |-2 * z.im * x| := le_abs_self _
        _ = 2 * |z.im| * |x| := by norm_num
    linarith

def criticalFeature (z : ℂ) (hz : |z.im| < 1 / 2) : CriticalL2 :=
  (criticalFeatureRaw_memLp hz).toLp _

def criticalEvaluation (z : ℂ) (hz : |z.im| < 1 / 2) : CriticalL2 →L[ℂ] ℂ :=
  innerSL ℂ (criticalFeature z hz)

theorem criticalEvaluation_eq_integral (z : ℂ) (hz : |z.im| < 1 / 2)
    (f : CriticalL2) :
    criticalEvaluation z hz f = ∫ x : ℝ, f x * sourceChar z x := by
  rw [criticalEvaluation, innerSL_apply_apply, MeasureTheory.L2.inner_def]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_realDensity measurable_criticalWeight)
    (Filter.Eventually.of_forall fun x => by simp [realDensity])]
  apply integral_congr_ae
  have hfeature := (withDensity_realDensity_ae_eq measurable_criticalWeight
    criticalWeight_pos).mp (criticalFeatureRaw_memLp hz).coeFn_toLp
  filter_upwards [hfeature] with x hx
  rw [criticalFeature, hx, RCLike.inner_apply, criticalFeatureRaw]
  rw [show (realDensity criticalWeight x).toReal = criticalWeight x by
    rw [realDensity, ENNReal.toReal_ofReal (criticalWeight_pos x).le]]
  change ((criticalWeight x : ℂ) *
    (f x * (starRingEnd ℂ) ((starRingEnd ℂ) (sourceChar z x) /
      (criticalWeight x : ℂ)))) = _
  rw [map_div₀ (starRingEnd ℂ)]
  have hconjchar : (starRingEnd ℂ) ((starRingEnd ℂ) (sourceChar z x)) =
      sourceChar z x := by simp
  have hconjweight : (starRingEnd ℂ) (criticalWeight x : ℂ) =
      (criticalWeight x : ℂ) := by simp
  rw [hconjchar, hconjweight]
  field_simp [(criticalWeight_pos x).ne']

/-! anomaly -/

def criticalAnomalyBoundConstant (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(1 / 2 : ℝ)) *
    (Real.log n * (thetaBound * Real.exp (Real.log n)))

theorem criticalAnomalyBoundConstant_nonneg (n : ℕ) :
    0 ≤ criticalAnomalyBoundConstant n := by
  unfold criticalAnomalyBoundConstant
  have := thetaBound_nonneg
  positivity

theorem norm_integerAnomaly_le_criticalExp
    {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    ‖integerAnomaly thetaSource n x‖ ≤
      criticalAnomalyBoundConstant n * Real.exp (-|x|) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hnR
  have hpow : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_pos_of_pos hnpos _).le
  rw [integerAnomaly_eq_intervalMass thetaSource hn, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hpow (intervalMass_nonneg _ _)),
    criticalAnomalyBoundConstant]
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left (intervalMass_le_exp hlog x) hpow

theorem integerAnomaly_memLp_critical
    {n : ℕ} (hn : 1 ≤ n) :
    MemLp (integerAnomaly thetaSource n) 2
      ((volume : Measure ℝ).withDensity (realDensity criticalWeight)) := by
  rw [memLp_two_withDensity_iff measurable_criticalWeight criticalWeight_pos]
  have hanomaly : Continuous (fun x : ℝ => integerAnomaly thetaSource n x) := by
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log n := Real.log_nonneg hnR
    have hfun : (fun x : ℝ => integerAnomaly thetaSource n x) = fun x =>
        Complex.I * ((((n : ℝ) ^ (-(1 / 2 : ℝ)) *
          intervalMass thetaSource x (x + Real.log n) : ℝ)) : ℂ) := by
      funext x
      exact integerAnomaly_eq_intervalMass thetaSource hn x
    rw [hfun]
    have hwindow := continuous_intervalMass_add thetaSource hlog
    fun_prop
  have hsw : Continuous (sqrtWeight criticalWeight) := by
    unfold sqrtWeight criticalWeight
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm
    (hsw.mul hanomaly).aestronglyMeasurable).2
  refine Integrable.mono'
    ((integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic (by norm_num : (0 : ℝ) < 1)).const_mul
      ((criticalAnomalyBoundConstant n) ^ 2))
    ((hsw.mul hanomaly).norm.pow 2).aestronglyMeasurable ?_
  filter_upwards with x
  change ‖‖sqrtWeight criticalWeight x * integerAnomaly thetaSource n x‖ ^ 2‖ ≤
    (criticalAnomalyBoundConstant n) ^ 2 * Real.exp (-(1 * |x|))
  rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul,
    norm_sqrtWeight_criticalWeight, one_mul]
  have hC := criticalAnomalyBoundConstant_nonneg n
  have hbound := norm_integerAnomaly_le_criticalExp hn x
  calc
    (Real.exp (|x| / 2) * ‖integerAnomaly thetaSource n x‖) ^ 2
        ≤ (Real.exp (|x| / 2) *
            (criticalAnomalyBoundConstant n * Real.exp (-|x|))) ^ 2 := by
          gcongr
    _ = (criticalAnomalyBoundConstant n) ^ 2 * Real.exp (-|x|) := by
          rw [show Real.exp (|x| / 2) *
              (criticalAnomalyBoundConstant n * Real.exp (-|x|)) =
              criticalAnomalyBoundConstant n * Real.exp (-|x| / 2) by
            calc
              Real.exp (|x| / 2) *
                  (criticalAnomalyBoundConstant n * Real.exp (-|x|)) =
                  criticalAnomalyBoundConstant n *
                    (Real.exp (|x| / 2) * Real.exp (-|x|)) := by ring_nf
              _ = criticalAnomalyBoundConstant n * Real.exp (-|x| / 2) := by
                rw [← Real.exp_add]
                congr 2
                ring_nf]
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 1
          ring_nf

def criticalAnomaly {n : ℕ} (hn : 1 ≤ n) : CriticalL2 :=
  (integerAnomaly_memLp_critical hn).toLp _

theorem criticalEvaluation_criticalAnomaly
    {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : |z.im| < 1 / 2) (hz0 : z ≠ 0) :
    criticalEvaluation z hz (criticalAnomaly hn) = shiftMultiplier n z * XiC z := by
  rw [criticalEvaluation_eq_integral]
  have hcoe := (withDensity_realDensity_ae_eq measurable_criticalWeight
    criticalWeight_pos).mp (integerAnomaly_memLp_critical hn).coeFn_toLp
  rw [show (∫ x : ℝ, (criticalAnomaly hn : ℝ → ℂ) x * sourceChar z x) =
      ∫ x : ℝ, integerAnomaly thetaSource n x * sourceChar z x by
    apply integral_congr_ae
    filter_upwards [hcoe] with x hx
    rw [criticalAnomaly, hx]]
  exact integral_integerAnomaly_sourceChar hn (by linarith) hz0

theorem criticalEvaluation_criticalAnomaly_xi_zero
    {n : ℕ} (hn : 1 ≤ n) (q : XiZeroCopy) :
    criticalEvaluation (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q)
      (criticalAnomaly hn) = 0 := by
  rw [criticalEvaluation_criticalAnomaly hn (abs_xiSpectralPoint_im_lt_half q)
    (xiSpectralPoint_ne_zero q), XiC_xiSpectralPoint_eq_zero, mul_zero]

/-! critical prime covariance -/

def criticalShiftSymbol (L x : ℝ) : ℂ :=
  ((Real.exp (-L / 2) * Real.exp (|x| / 2) *
    Real.exp (-|x + L| / 2) : ℝ) : ℂ)

theorem measurable_criticalShiftSymbol (L : ℝ) : Measurable (criticalShiftSymbol L) := by
  unfold criticalShiftSymbol
  fun_prop

theorem norm_criticalShiftSymbol_le_one {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    ‖criticalShiftSymbol L x‖ ≤ 1 := by
  have habs : |x| - |x + L| ≤ L := by
    have h := abs_sub_abs_le_abs_sub x (x + L)
    have hdist : |x - (x + L)| = L := by
      rw [show x - (x + L) = -L by ring_nf, abs_neg, abs_of_nonneg hL]
    linarith
  rw [criticalShiftSymbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)) (Real.exp_pos _)),
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]
  apply Real.exp_le_exp.2
  linarith

private def criticalToHaar : CriticalL2 →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (weightedDensityUnitary criticalWeight measurable_criticalWeight
    criticalWeight_pos).toLinearIsometry.toContinuousLinearMap

private def criticalFromHaar : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] CriticalL2 :=
  (weightedDensityUnitary criticalWeight measurable_criticalWeight
    criticalWeight_pos).symm.toLinearIsometry.toContinuousLinearMap

private def haarTranslation (L : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (MellinL2.additiveTranslationUnitary L).toLinearIsometry.toContinuousLinearMap

def criticalShift (L : ℝ) (hL : 0 ≤ L) : CriticalL2 →L[ℂ] CriticalL2 :=
  criticalFromHaar.comp
    ((lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
      (measurable_criticalShiftSymbol L) zero_le_one
      (norm_criticalShiftSymbol_le_one hL)).comp
      ((haarTranslation L).comp criticalToHaar))

theorem norm_criticalShift_apply_le (L : ℝ) (hL : 0 ≤ L) (f : CriticalL2) :
    ‖criticalShift L hL f‖ ≤ ‖f‖ := by
  let U := weightedDensityUnitary (μ := (volume : Measure ℝ)) criticalWeight
    measurable_criticalWeight criticalWeight_pos
  let V := MellinL2.additiveTranslationUnitary L
  let M := lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    (measurable_criticalShiftSymbol L) zero_le_one
    (norm_criticalShiftSymbol_le_one hL)
  change ‖U.symm (M (V (U f)))‖ ≤ ‖f‖
  rw [U.symm.norm_map]
  calc
    ‖M (V (U f))‖ ≤ ‖M‖ * ‖V (U f)‖ := M.le_opNorm _
    _ ≤ 1 * ‖V (U f)‖ := mul_le_mul_of_nonneg_right
      (norm_lpBoundedMulCLM_le (p := 2) (μ := (volume : Measure ℝ))
        (measurable_criticalShiftSymbol L) zero_le_one
        (norm_criticalShiftSymbol_le_one hL)) (norm_nonneg _)
    _ = ‖f‖ := by rw [one_mul, V.norm_map, U.norm_map]

theorem criticalShift_ae (L : ℝ) (hL : 0 ≤ L) (f : CriticalL2) :
    (criticalShift L hL f : ℝ → ℂ) =ᵐ[volume]
      fun x => (Real.exp (-L / 2) : ℂ) * f (x + L) := by
  let U := weightedDensityUnitary (μ := (volume : Measure ℝ)) criticalWeight
    measurable_criticalWeight criticalWeight_pos
  let g : Lp ℂ 2 (volume : Measure ℝ) := U f
  let V := MellinL2.additiveTranslationUnitary L
  let h : Lp ℂ 2 (volume : Measure ℝ) := V g
  let M := lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    (measurable_criticalShiftSymbol L) zero_le_one
    (norm_criticalShiftSymbol_le_one hL)
  let k : Lp ℂ 2 (volume : Measure ℝ) := M h
  have hU : (g : ℝ → ℂ) =ᵐ[volume]
      fun x => sqrtWeight criticalWeight x * f x := by
    simpa [g, U] using densityMul_ae criticalWeight measurable_criticalWeight
      criticalWeight_pos f
  have hVraw := Lp.coeFn_compMeasurePreserving g
    (MellinL2.realTranslation_measurePreserving L)
  have hV : (h : ℝ → ℂ) =ᵐ[volume] fun x => g (x + L) := by
    change ((Lp.compMeasurePreserving (MellinL2.realTranslationEquiv L)
      (MellinL2.realTranslation_measurePreserving L) g : Lp ℂ 2 volume) : ℝ → ℂ)
        =ᵐ[volume] fun x => g (x + L)
    filter_upwards [hVraw] with x hx
    rw [hx]
    rfl
  have hM : (k : ℝ → ℂ) =ᵐ[volume]
      fun x => criticalShiftSymbol L x * h x := by
    simp [k, M, lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
      (measurable_criticalShiftSymbol L) zero_le_one
      (norm_criticalShiftSymbol_le_one hL) h]
  have hDiv := densityDiv_ae criticalWeight measurable_criticalWeight
    criticalWeight_pos k
  have hUshift : ∀ᵐ x : ℝ ∂volume,
      g (x + L) = sqrtWeight criticalWeight (x + L) * f (x + L) :=
    (measurePreserving_add_right (volume : Measure ℝ) L).quasiMeasurePreserving
      |>.ae hU
  filter_upwards [hDiv, hM, hV, hUshift] with x hdiv hm hv hushift
  rw [show criticalShift L hL f =
      (weightedDensityUnitary criticalWeight measurable_criticalWeight
        criticalWeight_pos).symm k by rfl]
  change densityDiv criticalWeight measurable_criticalWeight criticalWeight_pos k x = _
  rw [hdiv, hm, hv, hushift]
  have hsqrt (y : ℝ) : sqrtWeight criticalWeight y =
      (Real.exp (|y| / 2) : ℂ) := by
    rw [sqrtWeight, criticalWeight]
    norm_cast
    exact (Real.exp_half |y|).symm
  rw [hsqrt x, hsqrt (x + L), criticalShiftSymbol]
  push_cast
  have hxne : (Real.exp (|x| / 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_ne_zero (|x| / 2))
  field_simp [hxne]
  rw [← Complex.exp_add]
  simp

def criticalIntegerShift {n : ℕ} (hn : 1 ≤ n) : CriticalL2 →L[ℂ] CriticalL2 :=
  criticalShift (Real.log n) (Real.log_nonneg (by exact_mod_cast hn))

theorem norm_criticalIntegerShift_apply_le
    {n : ℕ} (hn : 1 ≤ n) (f : CriticalL2) :
    ‖criticalIntegerShift hn f‖ ≤ ‖f‖ :=
  norm_criticalShift_apply_le _ _ f

theorem criticalIntegerShift_ae
    {n : ℕ} (hn : 1 ≤ n) (f : CriticalL2) :
    (criticalIntegerShift hn f : ℝ → ℂ) =ᵐ[volume] integerShift n f := by
  have h := criticalShift_ae (Real.log n)
    (Real.log_nonneg (by exact_mod_cast hn)) f
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hrpow : (n : ℝ) ^ (-(1 / 2 : ℝ)) =
      Real.exp (-Real.log n / 2) := by
    rw [Real.rpow_def_of_pos hnpos]
    congr 1
    ring_nf
  filter_upwards [h] with x hx
  rw [criticalIntegerShift, hx]
  change (Real.exp (-Real.log n / 2) : ℂ) * f (x + Real.log n) =
    (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * f (x + Real.log n)
  rw [hrpow]

/-- The critical-rigging evaluation retains the literal normalized integer character. -/
theorem criticalEvaluation_criticalIntegerShift
    {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : |z.im| < 1 / 2) (f : CriticalL2) :
    criticalEvaluation z hz (criticalIntegerShift hn f) =
      ((n : ℂ) ^ (-(dirichletExponent z))) * criticalEvaluation z hz f := by
  rw [criticalEvaluation_eq_integral, criticalEvaluation_eq_integral]
  have hshift := criticalIntegerShift_ae hn f
  rw [show (∫ x : ℝ, (criticalIntegerShift hn f : ℝ → ℂ) x * sourceChar z x) =
      sourceEvaluation z (integerShift n f) by
    unfold sourceEvaluation
    apply integral_congr_ae
    filter_upwards [hshift] with x hx
    rw [hx]]
  exact sourceEvaluation_integerShift z f (lt_of_lt_of_le Nat.zero_lt_one hn)

/-- Prime-normalized squared character energy seen by the critical detector. -/
def criticalRiggingPrimeEnergy (z : ℂ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) * Complex.normSq (((p : ℂ) ^ (-(dirichletExponent z))))

theorem quarterI_mem_criticalEvaluationStrip :
    |((((1 / 4 : ℝ) : ℂ) * Complex.I).im)| < 1 / 2 := by
  norm_num

/-- A detector strictly inside the admitted strip already has expanding Route-P energy.  Thus
critical-carrier contractivity alone cannot supply the missing half-density inequality. -/
theorem one_lt_criticalRiggingPrimeEnergy_quarterI (p : Nat.Primes) :
    1 < criticalRiggingPrimeEnergy (((1 / 4 : ℝ) : ℂ) * Complex.I) p := by
  let P : ℝ := p.1
  change 1 < P * Complex.normSq
    ((P : ℂ) ^ (-(dirichletExponent (((1 / 4 : ℝ) : ℂ) * Complex.I))))
  have hp : 0 < P := by dsimp [P]; exact_mod_cast p.2.pos
  have hp1 : 1 < P := by dsimp [P]; exact_mod_cast p.2.one_lt
  have hexp :
      (-(dirichletExponent (((1 / 4 : ℝ) : ℂ) * Complex.I))).re = -(1 / 4 : ℝ) := by
    norm_num [dirichletExponent]
  have hnorm :
      ‖((P : ℂ) ^ (-(dirichletExponent (((1 / 4 : ℝ) : ℂ) * Complex.I))))‖ =
        P ^ (-(dirichletExponent (((1 / 4 : ℝ) : ℂ) * Complex.I))).re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hp _
  rw [Complex.normSq_eq_norm_sq, hnorm, hexp,
    ← Real.rpow_natCast, ← Real.rpow_mul hp.le]
  nth_rewrite 1 [← Real.rpow_one P]
  rw [← Real.rpow_add hp]
  norm_num
  rw [← Real.rpow_zero P]
  exact (Real.strictMono_rpow_of_base_gt_one hp1) (by norm_num)

/-! sharp Goldilocks classification -/

def radialRiggingWeight (a x : ℝ) : ℝ := Real.exp (a * |x|)

def radialRiggingDetectorEnergy (a : ℝ) (z : ℂ) (x : ℝ) : ℝ :=
  Real.exp (-(a * |x|) - 2 * z.im * x)

def radialRiggingShiftEnergyRatio (a L x : ℝ) : ℝ :=
  Real.exp (-L) * radialRiggingWeight a x / radialRiggingWeight a (x + L)

def radialRiggingReflectedShiftEnergyRatio (a L x : ℝ) : ℝ :=
  Real.exp (-L) * radialRiggingWeight a x / radialRiggingWeight a (x - L)

theorem norm_criticalShiftSymbol_sq (L x : ℝ) :
    ‖criticalShiftSymbol L x‖ ^ 2 = radialRiggingShiftEnergyRatio 1 L x := by
  rw [criticalShiftSymbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)) (Real.exp_pos _)),
    radialRiggingShiftEnergyRatio, radialRiggingWeight]
  rw [show (Real.exp (-L / 2) * Real.exp (|x| / 2) *
      Real.exp (-|x + L| / 2)) ^ 2 =
      Real.exp (-L + |x| - |x + L|) by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    ring_nf]
  simp only [radialRiggingWeight, one_mul]
  rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
  congr 1

theorem radialRiggingDetectorEnergy_one_eq_featureEnergy (z : ℂ) (x : ℝ) :
    radialRiggingDetectorEnergy 1 z x =
      ‖sqrtWeight criticalWeight x * criticalFeatureRaw z x‖ ^ 2 := by
  rw [norm_sqrtWeight_mul_criticalFeatureRaw, radialRiggingDetectorEnergy, one_mul]

theorem integrable_radialRiggingDetectorEnergy
    {a : ℝ} {z : ℂ} (hz : 2 * |z.im| < a) :
    Integrable (radialRiggingDetectorEnergy a z) := by
  have hc : 0 < a - 2 * |z.im| := by linarith
  refine Integrable.mono' (integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hc)
    (by unfold radialRiggingDetectorEnergy; fun_prop) ?_
  filter_upwards with x
  rw [radialRiggingDetectorEnergy, Real.norm_of_nonneg (Real.exp_nonneg _)]
  refine Real.exp_le_exp.2 ?_
  have hx : -2 * z.im * x ≤ 2 * |z.im| * |x| := by
    calc
      -2 * z.im * x ≤ |-2 * z.im * x| := le_abs_self _
      _ = 2 * |z.im| * |x| := by norm_num
  linarith

theorem not_integrable_radialRiggingDetectorEnergy_of_lt
    {a b : ℝ} (hab : a < 2 * b) :
    ¬ Integrable (radialRiggingDetectorEnergy a ((b : ℂ) * Complex.I)) := by
  intro h
  have hrestr : IntegrableOn (radialRiggingDetectorEnergy a ((b : ℂ) * Complex.I))
      (Iic 0) := h.integrableOn
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic 0) := by
    refine Integrable.mono' hrestr aestronglyMeasurable_const ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    rw [Real.norm_eq_abs, abs_one, radialRiggingDetectorEnergy,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im,
      mul_one, zero_mul, add_zero]
    rw [abs_of_nonpos hx]
    have hexp : 0 ≤ -(a * -x) - 2 * b * x := by
      have hprod : 0 ≤ (a - 2 * b) * x :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) hx
      nlinarith
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 hexp
  rw [integrableOn_const_iff] at hone
  simp at hone

theorem radialRiggingShiftEnergyRatio_le_one
    {a L : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hL : 0 ≤ L) (x : ℝ) :
    radialRiggingShiftEnergyRatio a L x ≤ 1 := by
  have habs : |x| - |x + L| ≤ L := by
    have h := abs_sub_abs_le_abs_sub x (x + L)
    have hdist : |x - (x + L)| = L := by
      rw [show x - (x + L) = -L by ring_nf, abs_neg, abs_of_nonneg hL]
    linarith
  change Real.exp (-L) * Real.exp (a * |x|) /
      Real.exp (a * |x + L|) ≤ 1
  rw [div_eq_mul_inv,
    ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]
  apply Real.exp_le_exp.2
  nlinarith

theorem radialRiggingReflectedShiftEnergyRatio_le_one
    {a L : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hL : 0 ≤ L) (x : ℝ) :
    radialRiggingReflectedShiftEnergyRatio a L x ≤ 1 := by
  rw [show radialRiggingReflectedShiftEnergyRatio a L x =
      radialRiggingShiftEnergyRatio a L (-x) by
    change Real.exp (-L) * Real.exp (a * |x|) / Real.exp (a * |x - L|) =
      Real.exp (-L) * Real.exp (a * |-x|) / Real.exp (a * |-x + L|)
    rw [abs_neg, show -x + L = -(x - L) by ring_nf, abs_neg]]
  exact radialRiggingShiftEnergyRatio_le_one ha0 ha1 hL (-x)

theorem one_lt_radialRiggingShiftEnergyRatio_at_negative_edge
    {a L : ℝ} (ha : 1 < a) (hL : 0 < L) :
    1 < radialRiggingShiftEnergyRatio a L (-L) := by
  change 1 < Real.exp (-L) * Real.exp (a * |-L|) /
    Real.exp (a * |-L + L|)
  rw [neg_add_cancel, abs_neg, abs_of_pos hL, abs_zero, mul_zero, Real.exp_zero, div_one,
    ← Real.exp_add, ← Real.exp_zero]
  apply Real.exp_lt_exp.2
  nlinarith

def FullXiStripEvaluationAdmissible (a : ℝ) : Prop :=
  ∀ z : ℂ, |z.im| < 1 / 2 → Integrable (radialRiggingDetectorEnergy a z)

def PrimeCovarianceContractive (a : ℝ) : Prop :=
  ∀ L : ℝ, 0 ≤ L → ∀ x : ℝ, radialRiggingShiftEnergyRatio a L x ≤ 1

theorem fullXiStripEvaluationAdmissible_and_primeCovarianceContractive_iff
    {a : ℝ} (ha0 : 0 ≤ a) :
    FullXiStripEvaluationAdmissible a ∧ PrimeCovarianceContractive a ↔ a = 1 := by
  constructor
  · rintro ⟨heval, hshift⟩
    have ha1 : 1 ≤ a := by
      by_contra hnot
      have halt : a < 1 := lt_of_not_ge hnot
      let b : ℝ := (a + 1) / 4
      have hb0 : 0 ≤ b := by dsimp [b]; linarith
      have hbhalf : b < 1 / 2 := by dsimp [b]; linarith
      have hab : a < 2 * b := by dsimp [b]; linarith
      have hmem := heval ((b : ℂ) * Complex.I) (by
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im,
          Complex.ofReal_im, mul_one, zero_mul, add_zero]
        rw [abs_of_nonneg hb0]
        exact hbhalf)
      exact (not_integrable_radialRiggingDetectorEnergy_of_lt hab) hmem
    have haUpper : a ≤ 1 := by
      by_contra hnot
      have ha : 1 < a := lt_of_not_ge hnot
      have hle := hshift 1 zero_le_one (-1)
      have hgt := one_lt_radialRiggingShiftEnergyRatio_at_negative_edge ha zero_lt_one
      linarith
    linarith
  · rintro rfl
    constructor
    · intro z hz
      apply integrable_radialRiggingDetectorEnergy
      linarith
    · intro L hL x
      exact radialRiggingShiftEnergyRatio_le_one zero_le_one le_rfl hL x

end HedenmalmThetaSource
end
end RHTower
