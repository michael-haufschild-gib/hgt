import GaloisForLFunctions.OrderSixMetaplecticTheory.TheRatioPairsCarryTwistedSexticJacobiSums

/-!
# The ratio traces read the relation of the opposite pairs

For `c ≠ 0, 1` and `λ` the quadratic character of `O/q`, the trace of the ratio pair sum
`G^{(c)}_λ = Σ_tλ(t)θ(T_tw)θ(T_{ct}w)` has constant term (`integral_sourceRatioTrace`)

`|P|(g_λλ(1 − c)J_c Σ_kb(k)b(−k)λ(k) + N²C_c Σ_kb₂(k)b₂(−k)g_{χλ}(k))`.

The cusp `∞` contributes `g_λλ((1 − c)k)`, the generic pairs of the middle cusps `g_λλ((1 − c)k)(J_c − 1)`;
their high pairs cancel against `λ`; the cusp `0` contributes `N²C_c g_{χλ}(k)`. Since
`λ(1 − c)J_c C_{−1} = λ(2)J₆C_c`, **every ratio trace has the constant term of the opposite-pair trace up to the
factor `C_c/C_{−1}`** (`integral_sourceRatioTrace_eq`). So at level `q²` the quadratic grade carries
one relation between the double poles of `L_λ` and `L_{χ̄λ}`, the one of
`sexticTwist_relation`; no ratio pair decides their common value.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

open MeasureTheory

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- The ratio trace of the projected theta function with the quadratic weight. -/
abbrev sourceRatioTrace (c : P.Res) : HyperbolicSpace → ℂ := P.ratioTrace P.lam c sourceTheta

theorem continuous_ratioCorrelation_source (c x : P.Res) : Continuous (P.ratioCorrelation c sourceTheta x) := by
  unfold ratioCorrelation
  exact (cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _)).mul
    (cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _))

theorem continuous_ratioSum_source (c : P.Res) : Continuous (P.ratioSum P.lam c sourceTheta) := by
  unfold ratioSum
  exact continuous_finsetSum _ fun x _ => continuous_const.mul (P.continuous_ratioCorrelation_source c x)

/-- **The cusp `∞`.** -/
theorem integral_ratioSum_source (h2 : (2 : P.Res) ≠ 0) (c : P.Res) (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, P.ratioSum P.lam c sourceTheta (upperPoint z v hv) =
      periodArea * ∑' k : O, rationalSourceModeAmplitude v k * rationalSourceModeAmplitude v (-k) *
        (P.lam ((1 - c) * P.res k) * gaussSum P.lam P.traceChar) := by
  set b := rationalSourceModeAmplitude v
  have hb : Summable (fun h => ‖b h‖) := rationalSourceModeAmplitude_summable v hv
  have e : ∀ z, P.ratioSum P.lam c sourceTheta (upperPoint z v hv) = ∑ x : P.Res, P.lam x *
      (cuspCharacterSeries b (z + 3 * ringComplex (P.lift x) / ringComplex P.p) *
        cuspCharacterSeries b (z + 3 * ringComplex (P.lift (c * x)) / ringComplex P.p)) := by
    intro z
    unfold ratioSum ratioCorrelation
    simp_rw [P.sourceTheta_fracShift]
    rfl
  simp_rw [e]
  rw [integral_wsum_translate_mul b b hb hb]
  congr 1
  refine tsum_congr fun k => ?_
  congr 1
  have hsum : ∑ x : P.Res, P.lam x * tracePhase (cuspFrequency k * (3 * ringComplex (P.lift x) / ringComplex P.p -
      3 * ringComplex (P.lift (c * x)) / ringComplex P.p)) =
      ∑ x : P.Res, P.lam x * P.traceChar (x * ((1 - c) * P.res k)) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show 3 * ringComplex (P.lift x) / ringComplex P.p - 3 * ringComplex (P.lift (c * x)) / ringComplex P.p =
        3 * ringComplex (P.lift x - P.lift (c * x)) / ringComplex P.p by rw [map_sub]; ring,
      P.tracePhase_low, map_sub, res_lift, res_lift]
    congr 2
    ring
  rw [hsum, P.sum_lam_traceChar h2]

/-- **One ratio pair over a middle cusp**: generic pairs carry `χ((1 + s)(1 + cs))`, `s = 9tx`; at
`s = −1` or `s = −c⁻¹` one factor is the high point `A_q²w`. -/
theorem ratioCorrelation_lowerThree (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (c : P.Res) (hc1 : c ≠ 1) (x : {x : P.Res // x ≠ 0}) (t : P.Res) (w : HyperbolicSpace) :
    P.ratioCorrelation c Θ t (complexMatrix (lowerThree (P.p * P.lift x.1)) • w) =
      if 1 + 9 * t * x.1 = 0 then
        (P.chi (3 * x.1))⁻¹ * P.chi (1 + c * (9 * t * x.1)) *
          (Θ (P.dilation • P.dilation • w) * Θ (P.fracShift (P.lift (c * t / (1 + c * (9 * t * x.1)))) • w))
      else if 1 + c * (9 * t * x.1) = 0 then
        P.chi (1 + 9 * t * x.1) * (P.chi (3 * x.1))⁻¹ *
          (Θ (P.fracShift (P.lift (t / (1 + 9 * t * x.1))) • w) * Θ (P.dilation • P.dilation • w))
      else
        P.chi ((1 + 9 * t * x.1) * (1 + c * (9 * t * x.1))) *
          (Θ (P.fracShift (P.lift (t / (1 + 9 * t * x.1))) • w) *
            Θ (P.fracShift (P.lift (c * t / (1 + c * (9 * t * x.1)))) • w)) := by
  have hp : P.res (P.lift t) = t := res_lift _ _
  have hq : P.res (P.lift (c * t)) = c * t := res_lift _ _
  have hB : ∀ y : P.Res, 1 + 9 * (c * t) * y = 1 + c * (9 * t * y) := fun y => by ring
  unfold ratioCorrelation
  split_ifs with h1 h1'
  · have hm : 1 + 9 * P.res (P.lift (c * t)) * x.1 ≠ 0 := by
      rw [hq, hB, show 1 + c * (9 * t * x.1) = 1 - c + c * (1 + 9 * t * x.1) by ring, h1, mul_zero, add_zero]
      exact sub_ne_zero.mpr (Ne.symm hc1)
    rw [P.theta_mid_high Θ hΘ x _ (by rw [hp]; exact h1), P.theta_mid_generic Θ hΘ x _ hm, hq, hB]
    ring
  · have hm : 1 + 9 * P.res (P.lift t) * x.1 ≠ 0 := by rw [hp]; exact h1
    rw [P.theta_mid_generic Θ hΘ x _ hm, P.theta_mid_high Θ hΘ x _ (by rw [hq, hB]; exact h1'), hp]
    ring
  · have hm : 1 + 9 * P.res (P.lift t) * x.1 ≠ 0 := by rw [hp]; exact h1
    have hm' : 1 + 9 * P.res (P.lift (c * t)) * x.1 ≠ 0 := by rw [hq, hB]; exact h1'
    rw [P.theta_mid_generic Θ hΘ x _ hm, P.theta_mid_generic Θ hΘ x _ hm', hp, hq, hB, map_mul]
    ring

theorem norm_lam_chi_chi_traceChar_le (t a b r : P.Res) :
    ‖P.lam t * (P.chi a * P.chi b * P.traceChar r)‖ ≤ 1 := by
  rw [norm_mul, norm_mul, norm_mul, P.norm_traceChar, mul_one]
  exact mul_le_one₀ (P.norm_lam_le t) (by positivity)
    (mul_le_one₀ (P.norm_chi_le a) (norm_nonneg _) (P.norm_chi_le b))

theorem integral_high_mul_comm (u : O) (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, sourceTheta (P.fracShift u • upperPoint z v hv) *
        sourceTheta (P.dilation • P.dilation • upperPoint z v hv) = P.highTerm v := by
  rw [highTerm, ← P.integral_high_mul u v hv]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)

/-- **One ratio pair over a middle cusp, integrated.** -/
theorem integral_ratioCorrelation_middle (h2 : (2 : P.Res) ≠ 0) (c : P.Res) (hc1 : c ≠ 1)
    (x : {x : P.Res // x ≠ 0}) (t : P.Res) (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, P.ratioCorrelation c sourceTheta t
        (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) =
      (if 1 + 9 * t * x.1 = 0 then (P.chi (3 * x.1))⁻¹ * P.chi (1 + c * (9 * t * x.1)) * P.highTerm v
        else if 1 + c * (9 * t * x.1) = 0 then P.chi (1 + 9 * t * x.1) * (P.chi (3 * x.1))⁻¹ * P.highTerm v
        else 0) +
      P.chi ((1 + 9 * t * x.1) * (1 + c * (9 * t * x.1))) *
        (periodArea * ∑' k : O, rationalSourceModeAmplitude v k * rationalSourceModeAmplitude v (-k) *
          P.traceChar ((1 - c) * t / ((1 + 9 * t * x.1) * (1 + c * (9 * t * x.1))) * P.res k)) := by
  have hb : Summable (fun h => ‖rationalSourceModeAmplitude v h‖) := rationalSourceModeAmplitude_summable v hv
  simp_rw [P.ratioCorrelation_lowerThree sourceTheta sourceTheta_automorphy c hc1 x t]
  by_cases h₁ : 1 + 9 * t * x.1 = 0
  · have hQ : (1 + 9 * t * x.1) * (1 + c * (9 * t * x.1)) = 0 := by rw [h₁, zero_mul]
    simp_rw [if_pos h₁]
    rw [hQ, MulChar.map_zero, zero_mul, add_zero, integral_const_mul, P.integral_high_mul, highTerm]
  · by_cases h₂ : 1 + c * (9 * t * x.1) = 0
    · have hQ : (1 + 9 * t * x.1) * (1 + c * (9 * t * x.1)) = 0 := by rw [h₂, mul_zero]
      simp_rw [if_neg h₁, if_pos h₂]
      rw [hQ, MulChar.map_zero, zero_mul, add_zero, integral_const_mul, P.integral_high_mul_comm]
    · simp_rw [if_neg h₁, if_neg h₂]
      rw [zero_add, integral_const_mul]
      simp_rw [P.sourceTheta_fracShift]
      rw [integral_translate_mul _ _ hb hb]
      congr 2
      refine tsum_congr fun k => ?_
      congr 1
      rw [show 3 * ringComplex (P.lift (t / (1 + 9 * t * x.1))) / ringComplex P.p -
          3 * ringComplex (P.lift (c * t / (1 + c * (9 * t * x.1)))) / ringComplex P.p =
          3 * ringComplex (P.lift (t / (1 + 9 * t * x.1)) - P.lift (c * t / (1 + c * (9 * t * x.1)))) /
            ringComplex P.p by rw [map_sub]; ring, P.tracePhase_low, map_sub, res_lift, res_lift]
      congr 1
      field_simp
      ring

/-- **The middle cusps.** `Σ_{x≢0}∫_P G^{(c)}_λ(L_{qx}w) = |P|Σ_kb(k)b(−k)g_λλ((1 − c)k)(J_c − 1)`. -/
theorem integral_middle_sumR (h2 : (2 : P.Res) ≠ 0) (c : P.Res) (hc1 : c ≠ 1) (v : ℝ) (hv : 0 < v) :
    ∑ x : {x : P.Res // x ≠ 0}, ∫ z in periodDomain,
        P.ratioSum P.lam c sourceTheta (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) =
      periodArea * ∑' k : O, rationalSourceModeAmplitude v k * rationalSourceModeAmplitude v (-k) *
        (gaussSum P.lam P.traceChar * P.lam ((1 - c) * P.res k) * (P.ratioJacobi c - 1)) := by
  set b := rationalSourceModeAmplitude v with hbdef
  have hb : Summable (fun h => ‖b h‖) := rationalSourceModeAmplitude_summable v hv
  have hsplit : ∀ x : {x : P.Res // x ≠ 0}, ∫ z in periodDomain,
      P.ratioSum P.lam c sourceTheta (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) =
      ∑ t : P.Res, P.lam t * ∫ z in periodDomain, P.ratioCorrelation c sourceTheta t
        (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) := fun x => by
    unfold ratioSum
    rw [integral_finsetSum _ (fun t _ => integrableOn_periodDomain_of_continuous
      (fun z => P.lam t * P.ratioCorrelation c sourceTheta t
        (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv))
      (continuous_const.mul ((P.continuous_ratioCorrelation_source c t).comp
        ((continuous_hyperbolic_action (complexMatrix (lowerThree (P.p * P.lift x.1)))).comp
          (continuous_upperPoint_z v hv)))))]
    simp_rw [integral_const_mul]
  simp_rw [hsplit, P.integral_ratioCorrelation_middle h2 c hc1 _ _ v hv, mul_add, Finset.sum_add_distrib]
  simp only [← hbdef]
  obtain ⟨g, hgs⟩ : ∃ g : P.Res → ℂ, ∀ s, g s = if 1 + s = 0 then P.chi (1 + c * s) * P.highTerm v
      else if 1 + c * s = 0 then P.chi (1 + s) * P.highTerm v else 0 := ⟨_, fun s => rfl⟩
  have hhigh : ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.lam t *
      (if 1 + 9 * t * x.1 = 0 then (P.chi (3 * x.1))⁻¹ * P.chi (1 + c * (9 * t * x.1)) * P.highTerm v
        else if 1 + c * (9 * t * x.1) = 0 then P.chi (1 + 9 * t * x.1) * (P.chi (3 * x.1))⁻¹ * P.highTerm v
        else 0) = 0 := by
    refine (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun t _ => ?_).trans (P.high_sum_vanish h2 g)
    congr 1
    rw [hgs]
    split_ifs <;> ring
  rw [hhigh, zero_add]
  have hgen : ∀ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.lam t *
      (P.chi ((1 + 9 * t * x.1) * (1 + c * (9 * t * x.1))) *
        (periodArea * ∑' k : O, b k * b (-k) *
          P.traceChar ((1 - c) * t / ((1 + 9 * t * x.1) * (1 + c * (9 * t * x.1))) * P.res k))) =
      periodArea * ∑' k : O, b k * b (-k) * ∑ t : P.Res, P.lam t *
        (P.chi ((1 + 9 * t * x.1) * (1 + c * (9 * t * x.1))) *
          P.traceChar ((1 - c) * t / ((1 + 9 * t * x.1) * (1 + c * (9 * t * x.1))) * P.res k)) := by
    intro x
    rw [← sum_tsum_swap b b hb hb _ 1 (fun t k => P.norm_lam_chi_traceChar_le _ _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [show (∑' k : O, b k * b (-k) * (P.lam t * (P.chi ((1 + 9 * t * x.1) * (1 + c * (9 * t * x.1))) *
        P.traceChar ((1 - c) * t / ((1 + 9 * t * x.1) * (1 + c * (9 * t * x.1))) * P.res k)))) =
        P.lam t * P.chi ((1 + 9 * t * x.1) * (1 + c * (9 * t * x.1))) *
        ∑' k : O, b k * b (-k) *
          P.traceChar ((1 - c) * t / ((1 + 9 * t * x.1) * (1 + c * (9 * t * x.1))) * P.res k) by
      rw [← tsum_mul_left]
      exact tsum_congr fun k => by ring]
    ring
  rw [Finset.sum_congr rfl fun x _ => hgen x]
  rw [← Finset.mul_sum, sum_tsum_swap b b hb hb _ _ (fun x k => P.norm_sum_lam_chi_traceChar_le _ _)]
  congr 1
  refine tsum_congr fun k => ?_
  congr 1
  rw [P.jacobi_double_sum_ratio h2 c (P.res k)]

/-- **The cusp `0`.** `Σ_{s ∈ O/q²}∫_P G^{(c)}_λ(ST(3s)w) = N²|P|C_cΣ_kb₂(k)b₂(−k)g_{χλ}(k)`. -/
theorem integral_cuspZero_sumR (c : P.Res) (hc0 : c ≠ 0) (hc1 : c ≠ 1) (v : ℝ) (hv : 0 < v) :
    ∑ s : P.Res × P.Res, ∫ z in periodDomain, P.ratioSum P.lam c sourceTheta
        (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) =
      P.normC ^ 2 * (periodArea * (P.cuspZeroCoeff c *
        ∑' k : O, rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) k *
          rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) (-k) * P.sexticGaussAt k)) := by
  have hn := P.norm_pos
  have hv1 : 0 < v / ‖ringComplex P.p‖ := div_pos hv hn
  set b₂ := rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖)
  have hb₂ : Summable (fun h => ‖b₂ h‖) := rationalSourceModeAmplitude_summable _ (div_pos hv1 hn)
  have hinj : Function.Injective (fun m : O => m * P.p) := fun x y h => mul_right_cancel₀ P.ne_zero h
  set g : {x : P.Res // x ≠ 0} → O → ℂ := fun x =>
    cuspConv (P.shiftedLow (v / ‖ringComplex P.p‖) (-P.lowBeta (-P.lift (c * x.1)) - -P.lowBeta (-P.lift x.1))) b₂
  have hg : ∀ x, Summable (fun h => ‖g x h‖) := fun x => summable_cuspConv (P.summable_shiftedLow _ hv1 _) hb₂
  have hg2 : ∀ x, Summable (fun m => ‖g x (m * P.p * P.p)‖) := fun x =>
    ((hg x).comp_injective hinj).comp_injective hinj
  have hpt : ∀ z, ∑ s : P.Res × P.Res, P.ratioSum P.lam c sourceTheta
      (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) =
      ∑ x : {x : P.Res // x ≠ 0}, P.lam x.1 * (P.chi (-3 * x.1) * P.chi (-3 * (c * x.1)) * (P.normC ^ 2 *
        cuspCharacterSeries (fun m => g x (m * P.p * P.p)) z)) := by
    intro z
    simp_rw [P.ratioSum_sO P.lam c sourceTheta sourceTheta_automorphy sourceTheta_rational_inv hc0,
      MulChar.map_zero, zero_mul, zero_add]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, P.sum_lowLow]
    rfl
  have hcont : ∀ s : P.Res × P.Res, Continuous (fun z : ℂ => P.ratioSum P.lam c sourceTheta
      (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) := fun s =>
    (P.continuous_ratioSum_source c).comp ((continuous_hyperbolic_action _).comp
      ((continuous_hyperbolic_action _).comp (continuous_upperPoint_z v hv)))
  have hc2 : ∀ x : {x : P.Res // x ≠ 0}, Continuous (fun z : ℂ => P.lam x.1 * (P.chi (-3 * x.1) *
      P.chi (-3 * (c * x.1)) * (P.normC ^ 2 * cuspCharacterSeries (fun m => g x (m * P.p * P.p)) z))) := fun x =>
    continuous_const.mul (continuous_const.mul (continuous_const.mul (cuspCharacterSeries_continuous _ (hg2 x))))
  rw [← integral_finsetSum _ (fun s _ => integrableOn_periodDomain_of_continuous _ (hcont s))]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun x _ => integrableOn_periodDomain_of_continuous _ (hc2 x)]
  have hI : ∀ x : {x : P.Res // x ≠ 0}, ∫ z in periodDomain, P.lam x.1 * (P.chi (-3 * x.1) *
      P.chi (-3 * (c * x.1)) * (P.normC ^ 2 * cuspCharacterSeries (fun m => g x (m * P.p * P.p)) z)) =
      P.lam x.1 * (P.chi (-3 * x.1) * P.chi (-3 * (c * x.1)) * (P.normC ^ 2 * (periodArea * g x 0))) := by
    intro x
    rw [integral_const_mul, integral_const_mul, integral_const_mul,
      PrimaryPrime.integral_cuspCharacterSeries _ (hg2 x), zero_mul, zero_mul]
  rw [Finset.sum_congr rfl fun x _ => hI x]
  have hg0 : ∀ x : {x : P.Res // x ≠ 0}, g x 0 =
      ∑' k : O, b₂ k * b₂ (-k) * P.traceChar ((9 * x.1)⁻¹ * (c⁻¹ - 1) * P.res k) := by
    intro x
    have hx : ¬ P.p ∣ P.lift x.1 := P.not_dvd_lift x
    have hx' : ¬ P.p ∣ -P.lift x.1 := fun h => hx (dvd_neg.mp h)
    have hcx : ¬ P.p ∣ -P.lift (c * x.1) := fun h => mul_ne_zero hc0 x.2 (P.res_lift_eq_zero (dvd_neg.mp h))
    simp only [g, cuspConv, zero_sub, shiftedLow]
    refine tsum_congr fun k => ?_
    have hβ : P.res (-(-P.lowBeta (-P.lift (c * x.1)) - -P.lowBeta (-P.lift x.1))) = (9 * x.1)⁻¹ * (c⁻¹ - 1) := by
      have e1 := P.res_neg_lowBeta (-P.lift x.1) hx'
      have e2 := P.res_neg_lowBeta (-P.lift (c * x.1)) hcx
      rw [show -(-P.lowBeta (-P.lift (c * x.1)) - -P.lowBeta (-P.lift x.1)) =
          -P.lowBeta (-P.lift x.1) - -P.lowBeta (-P.lift (c * x.1)) by ring, map_sub, e1, e2]
      simp only [map_neg, res_lift]
      have h9 := P.nine_ne_zero'
      field_simp
      ring
    rw [P.phase_eq_psi, P.psi_eq_traceChar, hβ]
    ring
  simp_rw [hg0]
  have hsw : ∑ x : {x : P.Res // x ≠ 0}, P.lam x.1 * (P.chi (-3 * x.1) * P.chi (-3 * (c * x.1)) *
      (P.normC ^ 2 * (periodArea * ∑' k : O, b₂ k * b₂ (-k) * P.traceChar ((9 * x.1)⁻¹ * (c⁻¹ - 1) * P.res k)))) =
      P.normC ^ 2 * (periodArea * ∑ x : {x : P.Res // x ≠ 0}, ∑' k : O, b₂ k * b₂ (-k) *
        (P.lam x.1 * (P.chi (-3 * x.1) * P.chi (-3 * (c * x.1)) *
          P.traceChar ((9 * x.1)⁻¹ * (c⁻¹ - 1) * P.res k)))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show (∑' k : O, b₂ k * b₂ (-k) * (P.lam x.1 * (P.chi (-3 * x.1) * P.chi (-3 * (c * x.1)) *
        P.traceChar ((9 * x.1)⁻¹ * (c⁻¹ - 1) * P.res k)))) =
        P.lam x.1 * (P.chi (-3 * x.1) * P.chi (-3 * (c * x.1))) *
        ∑' k : O, b₂ k * b₂ (-k) * P.traceChar ((9 * x.1)⁻¹ * (c⁻¹ - 1) * P.res k) by
      rw [← tsum_mul_left]
      refine tsum_congr fun k => ?_
      ring]
    ring
  rw [hsw, sum_tsum_swap b₂ b₂ hb₂ hb₂ _ 1 (fun x k => P.norm_lam_chi_chi_traceChar_le _ _ _ _)]
  congr 2
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [P.gauss_low_sum_ratio c hc0 hc1 (P.res k), sexticGaussAt]
  ring

/-- **The constant term of the ratio trace.** -/
theorem integral_sourceRatioTrace (h2 : (2 : P.Res) ≠ 0) (c : P.Res) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, P.sourceRatioTrace c (upperPoint z v hv) =
      periodArea * (gaussSum P.lam P.traceChar * P.lam (1 - c) * P.ratioJacobi c *
          ∑' k : O, rationalSourceModeAmplitude v k * rationalSourceModeAmplitude v (-k) * P.lam (P.res k) +
        P.normC ^ 2 * P.cuspZeroCoeff c *
          ∑' k : O, rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) k *
            rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) (-k) * P.sexticGaussAt k) := by
  set b := rationalSourceModeAmplitude v
  have hb : Summable (fun h => ‖b h‖) := rationalSourceModeAmplitude_summable v hv
  have hu := continuous_upperPoint_z v hv
  have e : ∀ z, P.sourceRatioTrace c (upperPoint z v hv) = P.ratioSum P.lam c sourceTheta (upperPoint z v hv) +
      (∑ x : {x : P.Res // x ≠ 0}, P.ratioSum P.lam c sourceTheta
          (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) +
        ∑ s : P.Res × P.Res, P.ratioSum P.lam c sourceTheta
          (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) := fun z =>
    P.ratioTrace_eq P.lam P.lam_squareInvariant c sourceTheta sourceTheta_automorphy sourceTheta_rational_inv _
  simp_rw [e]
  have hA : Continuous (fun z : ℂ => P.ratioSum P.lam c sourceTheta (upperPoint z v hv)) :=
    (P.continuous_ratioSum_source c).comp hu
  have hB : ∀ x : {x : P.Res // x ≠ 0}, Continuous (fun z : ℂ => P.ratioSum P.lam c sourceTheta
      (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv)) := fun x =>
    (P.continuous_ratioSum_source c).comp ((continuous_hyperbolic_action _).comp hu)
  have hC : ∀ s : P.Res × P.Res, Continuous (fun z : ℂ => P.ratioSum P.lam c sourceTheta
      (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) := fun s =>
    (P.continuous_ratioSum_source c).comp ((continuous_hyperbolic_action _).comp ((continuous_hyperbolic_action _).comp hu))
  have hBs : Continuous (fun z : ℂ => ∑ x : {x : P.Res // x ≠ 0}, P.ratioSum P.lam c sourceTheta
      (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv)) := continuous_finsetSum _ fun x _ => hB x
  have hCs : Continuous (fun z : ℂ => ∑ s : P.Res × P.Res, P.ratioSum P.lam c sourceTheta
      (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) :=
    continuous_finsetSum _ fun s _ => hC s
  rw [integral_add (integrableOn_periodDomain_of_continuous _ hA)
      (integrableOn_periodDomain_of_continuous (fun z : ℂ => ∑ x : {x : P.Res // x ≠ 0},
          P.ratioSum P.lam c sourceTheta (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) +
          ∑ s : P.Res × P.Res, P.ratioSum P.lam c sourceTheta
            (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) (hBs.add hCs)),
    integral_add (integrableOn_periodDomain_of_continuous _ hBs) (integrableOn_periodDomain_of_continuous _ hCs),
    integral_finsetSum _ fun x _ => integrableOn_periodDomain_of_continuous _ (hB x),
    integral_finsetSum _ fun s _ => integrableOn_periodDomain_of_continuous _ (hC s),
    P.integral_ratioSum_source h2 c v hv, P.integral_middle_sumR h2 c hc1 v hv, P.integral_cuspZero_sumR c hc0 hc1 v hv]
  have hφ : ∀ k : O, ‖P.lam (P.res k)‖ ≤ 1 := fun k => P.norm_lam_le _
  have s₀ := summable_mul_neg_bdd hb hb _ _ hφ
  have s₁ := s₀.mul_right (P.lam (1 - c) * gaussSum P.lam P.traceChar)
  have s₂ := s₀.mul_right (gaussSum P.lam P.traceChar * P.lam (1 - c) * (P.ratioJacobi c - 1))
  have hsum : (∑' k : O, b k * b (-k) * (P.lam ((1 - c) * P.res k) * gaussSum P.lam P.traceChar)) +
      (∑' k : O, b k * b (-k) * (gaussSum P.lam P.traceChar * P.lam ((1 - c) * P.res k) * (P.ratioJacobi c - 1))) =
      gaussSum P.lam P.traceChar * P.lam (1 - c) * P.ratioJacobi c * ∑' k : O, b k * b (-k) * P.lam (P.res k) := by
    have e1 : (∑' k : O, b k * b (-k) * (P.lam ((1 - c) * P.res k) * gaussSum P.lam P.traceChar)) =
        ∑' k : O, b k * b (-k) * P.lam (P.res k) * (P.lam (1 - c) * gaussSum P.lam P.traceChar) :=
      tsum_congr fun k => by rw [map_mul]; ring
    have e2 : (∑' k : O, b k * b (-k) * (gaussSum P.lam P.traceChar * P.lam ((1 - c) * P.res k) *
        (P.ratioJacobi c - 1))) = ∑' k : O, b k * b (-k) * P.lam (P.res k) *
          (gaussSum P.lam P.traceChar * P.lam (1 - c) * (P.ratioJacobi c - 1)) :=
      tsum_congr fun k => by rw [map_mul]; ring
    rw [e1, e2, ← s₁.tsum_add s₂, ← tsum_mul_left]
    exact tsum_congr fun k => by ring
  linear_combination periodArea * hsum

theorem cuspZeroCoeff_neg_one_ne_zero (h2 : (2 : P.Res) ≠ 0) : P.cuspZeroCoeff (-1) ≠ 0 := by
  have h4 : (-4 : P.Res) ≠ 0 := by
    rw [show (-4 : P.Res) = -(2 * 2) by norm_num]
    exact neg_ne_zero.mpr (mul_ne_zero h2 h2)
  rw [P.cuspZeroCoeff_neg_one]
  exact mul_ne_zero (mul_ne_zero (P.chi_ne_zero_of_ne _ h4) (inv_ne_zero (P.chi_ne_zero_of_ne _ P.nine_ne_zero')))
    (P.lam_ne_zero _ (neg_ne_zero.mpr h2))

/-- **Rigidity of the quadratic pair traces at level `q²`.** For every ratio `c ≠ 0, 1` the constant
term of the ratio trace is `C_c/C_{−1}` times the constant term of the opposite-pair trace `Tr G_λ`. -/
theorem integral_sourceRatioTrace_eq (h2 : (2 : P.Res) ≠ 0) (c : P.Res) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, P.sourceRatioTrace c (upperPoint z v hv) =
      P.cuspZeroCoeff c / P.cuspZeroCoeff (-1) * ∫ z in periodDomain, P.sourceFracTraceW (upperPoint z v hv) := by
  have hC := P.cuspZeroCoeff_neg_one_ne_zero h2
  have hprop := P.ratio_coefficients_proportional h2 c hc0 hc1
  have key : P.cuspZeroCoeff (-1) * ∫ z in periodDomain, P.sourceRatioTrace c (upperPoint z v hv) =
      P.cuspZeroCoeff c * ∫ z in periodDomain, P.sourceFracTraceW (upperPoint z v hv) := by
    rw [P.integral_sourceRatioTrace h2 c hc0 hc1 v hv, P.integral_sourceFracTraceW h2 v hv, P.cuspZeroCoeff_neg_one]
    set S₁ := ∑' k : O, rationalSourceModeAmplitude v k * rationalSourceModeAmplitude v (-k) * P.lam (P.res k)
    have h2k : (∑' k : O, rationalSourceModeAmplitude v k * rationalSourceModeAmplitude v (-k) *
        P.lam (2 * P.res k)) = P.lam 2 * S₁ := by
      rw [← tsum_mul_left]
      exact tsum_congr fun k => by rw [map_mul]; ring
    rw [h2k]
    linear_combination (periodArea * gaussSum P.lam P.traceChar * S₁) * hprop
  rw [div_mul_eq_mul_div, eq_div_iff hC]
  linear_combination key

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
