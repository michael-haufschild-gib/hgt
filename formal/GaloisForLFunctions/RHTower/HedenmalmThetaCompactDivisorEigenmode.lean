import GaloisForLFunctions.RHTower.HedenmalmThetaSourceModeNormalization
import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy

/-!
# Theta divisors are genuine vectors of the compact source inverse

The pointwise theta-source divisor mode was already known to satisfy the source-inverse
eigen-equation.  To turn that identity into an operator eigenvector, one must first prove the
missing weighted-domain statement

`sourceModeF thetaSource z ∈ L²(ℝ, thetaSource.k⁻¹ dx)`.

The crude exponential root-mode estimate cannot prove this because the reciprocal theta density
grows doubly exponentially.  At a zero, the right primitive is instead the complementary tail.
The sharp theta envelope then gives `‖sourceModeU z x‖ = O(thetaEnvelope x)`; reflection supplies
the other end.  Dividing its square by the source leaves one integrable theta envelope.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmPrimeTranslation

/-- At a theta divisor, the source mode inherits the doubly exponential decay of the source tail.
This is strictly sharper than the generic exponential strip bound. -/
theorem norm_sourceModeU_le_thetaEnvelope_right {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) {x : ℝ} (hx : 1 ≤ x) :
    ‖sourceModeU thetaSource z x‖ ≤ thetaEnvelopeUpper * thetaEnvelope x := by
  let a : ℝ := Real.pi * Real.exp (2 * x)
  let c : ℝ := thetaEnvelopeUpper * thetaEnvelope x
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hb : -1 < z.im := by
    have := neg_abs_le z.im
    linarith
  have ha_three : 3 < a := by
    have hexp_one : 1 < Real.exp (2 * x) := Real.one_lt_exp_iff.mpr (by linarith)
    have hpi_lt : Real.pi < Real.pi * Real.exp (2 * x) := by
      calc
        Real.pi = Real.pi * 1 := by ring
        _ < Real.pi * Real.exp (2 * x) := mul_lt_mul_of_pos_left hexp_one Real.pi_pos
    exact lt_trans Real.pi_gt_three (by simpa only [a] using hpi_lt)
  have hab : 0 < a + z.im := by linarith
  have hab_one : 1 ≤ a + z.im := by linarith
  have hc : 0 ≤ c := (mul_pos thetaEnvelopeUpper_pos (thetaEnvelope_pos x)).le
  have hXi : XiC z = 0 := by
    rw [← xiC_thetaSource hz]
    exact hzero
  have htail := (sourceModeI_eq_neg_tail_iff_XiC hz x).2 hXi
  have hint : IntegrableOn
      (fun y : ℝ => (thetaSource.k y : ℂ) * sourceChar z y) (Ioi x) volume :=
    (integrable_k_sourceChar thetaSource (hasShiftedTail_thetaSource hz)).integrableOn
  have hleft : IntegrableOn (fun y : ℝ => Real.exp (z.im * x) *
      ‖(thetaSource.k y : ℂ) * sourceChar z y‖) (Ioi x) volume :=
    hint.norm.const_mul _
  have hright : IntegrableOn
      (fun y : ℝ => c * Real.exp (-(a + z.im) * (y - x))) (Ioi x) volume :=
    (integrableOn_exp_neg_shift hab).const_mul c
  have hpoint : ∀ y ∈ Ioi x,
      Real.exp (z.im * x) * ‖(thetaSource.k y : ℂ) * sourceChar z y‖
        ≤ c * Real.exp (-(a + z.im) * (y - x)) := by
    intro y hy
    have hxy : x ≤ y := le_of_lt hy
    have hk := thetaCuspFullSource_le_shift hx hxy
    have hknorm : ‖(thetaSource.k y : ℂ) * sourceChar z y‖ =
        thetaSource.k y * Real.exp (-z.im * y) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (thetaSource.pos_k y), norm_sourceChar]
    rw [hknorm]
    calc
      Real.exp (z.im * x) * (thetaSource.k y * Real.exp (-z.im * y))
          ≤ Real.exp (z.im * x) *
              (c * Real.exp (-a * (y - x)) * Real.exp (-z.im * y)) := by
            gcongr
            simpa only [thetaSource_k, c, a] using hk
      _ = c * (Real.exp (z.im * x) * Real.exp (-a * (y - x)) *
          Real.exp (-z.im * y)) := by ring
      _ = c * Real.exp (z.im * x + (-a * (y - x)) + (-z.im * y)) := by
        rw [Real.exp_add, Real.exp_add]
      _ = c * Real.exp (-(a + z.im) * (y - x)) := by
        congr 1
        ring
  have hmono := setIntegral_mono_on hleft hright measurableSet_Ioi hpoint
  have hnorm : ‖sourceModeU thetaSource z x‖ =
      Real.exp (z.im * x) * ‖sourceModeI thetaSource z x‖ := by
    rw [sourceModeU, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
      norm_exp_neg_I_mul]
  have htail' : sourceModeI thetaSource z x =
      -∫ y in Ioi x, (thetaSource.k y : ℂ) * sourceChar z y := by
    simpa only [thetaSource_k] using htail
  calc
    ‖sourceModeU thetaSource z x‖ =
        Real.exp (z.im * x) *
          ‖-∫ y in Ioi x, (thetaSource.k y : ℂ) * sourceChar z y‖ := by
      rw [hnorm, htail']
    _ ≤ Real.exp (z.im * x) *
          ∫ y in Ioi x, ‖(thetaSource.k y : ℂ) * sourceChar z y‖ := by
      rw [norm_neg]
      gcongr
      exact MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ y in Ioi x,
          Real.exp (z.im * x) * ‖(thetaSource.k y : ℂ) * sourceChar z y‖ := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ ∫ y in Ioi x, c * Real.exp (-(a + z.im) * (y - x)) := hmono
    _ = c / (a + z.im) := by
      rw [MeasureTheory.integral_const_mul, integral_Ioi_exp_neg_shift hab, mul_one_div]
    _ ≤ c := div_le_self hc hab_one
    _ = thetaEnvelopeUpper * thetaEnvelope x := rfl

/-- Weighted energy density of the explicit theta divisor mode. -/
def sourceModeFWeightedEnergyDensity (z : ℂ) (x : ℝ) : ℝ :=
  ‖sourceModeF thetaSource z x‖ ^ 2 / thetaSource.k x

theorem continuous_sourceModeFWeightedEnergyDensity {z : ℂ} (hz : |z.im| < 1) :
    Continuous (sourceModeFWeightedEnergyDensity z) := by
  unfold sourceModeFWeightedEnergyDensity sourceModeF
  exact ((continuous_const.mul (continuous_sourceModeU hz)).norm.pow 2).div
    thetaSource.continuous_k (fun x => (thetaSource.pos_k x).ne')

theorem sourceModeFWeightedEnergyDensity_nonneg (z : ℂ) (x : ℝ) :
    0 ≤ sourceModeFWeightedEnergyDensity z x :=
  div_nonneg (sq_nonneg _) (thetaSource.pos_k x).le

/-- On the positive tail, division by the theta source consumes one of the two envelope factors. -/
theorem sourceModeFWeightedEnergyDensity_le_right {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) {x : ℝ} (hx : 1 ≤ x) :
    sourceModeFWeightedEnergyDensity z x ≤
      (‖z‖ ^ 2 * thetaEnvelopeUpper ^ 2 / thetaEnvelopeLower) * thetaEnvelope x := by
  have hU := norm_sourceModeU_le_thetaEnvelope_right hz hzero hx
  have hnum : ‖sourceModeF thetaSource z x‖ ^ 2 ≤
      ‖z‖ ^ 2 * thetaEnvelopeUpper ^ 2 * thetaEnvelope x ^ 2 := by
    rw [sourceModeF, norm_mul, norm_neg]
    rw [mul_pow]
    have hbound_nonneg : 0 ≤ thetaEnvelopeUpper * thetaEnvelope x :=
      (mul_pos thetaEnvelopeUpper_pos (thetaEnvelope_pos x)).le
    have hsq : ‖sourceModeU thetaSource z x‖ ^ 2 ≤
        (thetaEnvelopeUpper * thetaEnvelope x) ^ 2 := by
      nlinarith [norm_nonneg (sourceModeU thetaSource z x)]
    calc
      ‖z‖ ^ 2 * ‖sourceModeU thetaSource z x‖ ^ 2
          ≤ ‖z‖ ^ 2 * (thetaEnvelopeUpper * thetaEnvelope x) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg ‖z‖)
      _ = ‖z‖ ^ 2 * thetaEnvelopeUpper ^ 2 * thetaEnvelope x ^ 2 := by ring
  have hlow : thetaEnvelopeLower * thetaEnvelope x ≤ thetaSource.k x := by
    simpa only [thetaSource_k] using thetaCuspFullSource_ge_envelope (by linarith : 0 < x)
  have hupper_nonneg : 0 ≤ ‖z‖ ^ 2 * thetaEnvelopeUpper ^ 2 * thetaEnvelope x ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have hden_pos : 0 < thetaEnvelopeLower * thetaEnvelope x :=
    mul_pos thetaEnvelopeLower_pos (thetaEnvelope_pos x)
  calc
    sourceModeFWeightedEnergyDensity z x
        ≤ (‖z‖ ^ 2 * thetaEnvelopeUpper ^ 2 * thetaEnvelope x ^ 2) /
            (thetaEnvelopeLower * thetaEnvelope x) := by
          exact div_le_div₀ hupper_nonneg hnum hden_pos hlow
    _ = (‖z‖ ^ 2 * thetaEnvelopeUpper ^ 2 / thetaEnvelopeLower) * thetaEnvelope x := by
      field_simp [(thetaEnvelopeLower_pos).ne', (thetaEnvelope_pos x).ne']

/-- Reflection converts the positive-tail estimate into a two-sided estimate. -/
theorem sourceModeFWeightedEnergyDensity_le_abs {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) {x : ℝ} (hx : 1 ≤ |x|) :
    sourceModeFWeightedEnergyDensity z x ≤
      (‖z‖ ^ 2 * thetaEnvelopeUpper ^ 2 / thetaEnvelopeLower) * thetaEnvelope |x| := by
  rcases le_or_gt 0 x with hnonneg | hneg
  · rw [abs_of_nonneg hnonneg]
    exact sourceModeFWeightedEnergyDensity_le_right hz hzero
      (by simpa [abs_of_nonneg hnonneg] using hx)
  · have hzneg : |(-z).im| < 1 := by simpa using hz
    have hXi : XiC z = 0 := by
      rw [← xiC_thetaSource hz]
      exact hzero
    have hzeroNeg : xiC thetaSource (-z) = 0 := by
      rw [xiC_thetaSource hzneg, XiC_even]
      exact hXi
    have href := sourceModeF_neg thetaSource thetaSource_even
      (hasShiftedTail_thetaSource hz) hzero x
    have henergy : sourceModeFWeightedEnergyDensity z x =
        sourceModeFWeightedEnergyDensity (-z) (-x) := by
      unfold sourceModeFWeightedEnergyDensity
      rw [← href, thetaSource_even x]
    rw [henergy, abs_of_neg hneg]
    simpa using sourceModeFWeightedEnergyDensity_le_right hzneg hzeroNeg
      (x := -x) (by simpa [abs_of_neg hneg] using hx)

/-- The divisor mode has finite weighted source energy.  This is the missing analytic-domain
statement needed to promote the pointwise source-inverse identity to a compact-operator
eigenvector. -/
theorem integrable_sourceModeFWeightedEnergyDensity {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    Integrable (sourceModeFWeightedEnergyDensity z) (volume : Measure ℝ) := by
  let C : ℝ := ‖z‖ ^ 2 * thetaEnvelopeUpper ^ 2 / thetaEnvelopeLower
  let a : ℝ := Real.pi * Real.exp 2
  have hC : 0 ≤ C := by
    exact div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) thetaEnvelopeLower_pos.le
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hmajor : Integrable
      (fun x : ℝ => (C * thetaEnvelope 1 * Real.exp a) * Real.exp (-a * |x|))
      (volume : Measure ℝ) :=
    by simpa only [neg_mul] using
      (integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic ha).const_mul (C * thetaEnvelope 1 * Real.exp a)
  have htail : ∀ x : ℝ, 1 ≤ |x| →
      sourceModeFWeightedEnergyDensity z x ≤
        (C * thetaEnvelope 1 * Real.exp a) * Real.exp (-a * |x|) := by
    intro x hx
    have hmode := sourceModeFWeightedEnergyDensity_le_abs hz hzero hx
    have henv := thetaEnvelope_le_shift (x := (1 : ℝ)) (y := |x|) le_rfl hx
    calc
      sourceModeFWeightedEnergyDensity z x ≤ C * thetaEnvelope |x| := by
        simpa only [C] using hmode
      _ ≤ C * (thetaEnvelope 1 * Real.exp (-a * (|x| - 1))) := by
        gcongr
        simpa only [a, mul_one] using henv
      _ = C * thetaEnvelope 1 * Real.exp (-a * (|x| - 1)) := by ring
      _ = C * thetaEnvelope 1 * Real.exp (a + (-a * |x|)) := by
        congr 2
        ring
      _ = C * thetaEnvelope 1 *
          (Real.exp a * Real.exp (-a * |x|)) := by rw [Real.exp_add]
      _ = (C * thetaEnvelope 1 * Real.exp a) * Real.exp (-a * |x|) := by ring
  have hmeas : AEStronglyMeasurable (sourceModeFWeightedEnergyDensity z)
      (volume : Measure ℝ) :=
    (continuous_sourceModeFWeightedEnergyDensity hz).aestronglyMeasurable
  have hleft : IntegrableOn (sourceModeFWeightedEnergyDensity z) (Iic (-1 : ℝ)) volume := by
    refine Integrable.mono' hmajor.integrableOn
      (hmeas.mono_measure Measure.restrict_le_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    change x ≤ -1 at hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sourceModeFWeightedEnergyDensity_nonneg z x)]
    have hx0 : x ≤ 0 := by linarith
    have habs : 1 ≤ |x| := by rw [abs_of_nonpos hx0]; linarith
    exact htail x habs
  have hmid : IntegrableOn (sourceModeFWeightedEnergyDensity z) (Ioc (-1 : ℝ) 1) volume :=
    ((continuous_sourceModeFWeightedEnergyDensity hz).integrableOn_Icc
      (a := (-1 : ℝ)) (b := 1)).mono_set Ioc_subset_Icc_self
  have hright : IntegrableOn (sourceModeFWeightedEnergyDensity z) (Ioi (1 : ℝ)) volume := by
    refine Integrable.mono' hmajor.integrableOn
      (hmeas.mono_measure Measure.restrict_le_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 1 < x at hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sourceModeFWeightedEnergyDensity_nonneg z x)]
    have hx0 : 0 ≤ x := by linarith
    have habs : 1 ≤ |x| := by rw [abs_of_nonneg hx0]; linarith
    exact htail x habs
  have hunion : (Iic (-1 : ℝ)) ∪ (Ioc (-1 : ℝ) 1 ∪ Ioi 1) = univ := by
    rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (-1 : ℝ) ≤ 1), Iic_union_Ioi]
  rw [← integrableOn_univ, ← hunion]
  exact hleft.union (hmid.union hright)

/-- Every theta divisor in the natural strip defines a vector of the weighted source Hilbert
space `L²(ℝ, k⁻¹ dx)`. -/
theorem memLp_sourceModeF_thetaSource_weighted {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    MemLp (sourceModeF thetaSource z) 2
      ((volume : Measure ℝ).withDensity (realDensity (sourceWeight thetaSource))) := by
  refine (memLp_two_withDensity_iff (measurable_sourceWeight thetaSource)
    (sourceWeight_pos thetaSource)).mpr ?_
  have hcont : Continuous (fun x : ℝ =>
      sqrtWeight (sourceWeight thetaSource) x * sourceModeF thetaSource z x) := by
    have hw : Continuous (sourceWeight thetaSource) := by
      unfold sourceWeight
      exact thetaSource.continuous_k.inv₀ (fun x => (thetaSource.pos_k x).ne')
    have hsw : Continuous (sqrtWeight (sourceWeight thetaSource)) := by
      unfold sqrtWeight
      exact Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp hw)
    unfold sourceModeF
    exact hsw.mul (continuous_const.mul (continuous_sourceModeU hz))
  refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr ?_
  refine (integrable_sourceModeFWeightedEnergyDensity hz hzero).congr ?_
  filter_upwards with x
  have hk : 0 < thetaSource.k x := thetaSource.pos_k x
  rw [norm_mul, sqrtWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (show 0 ≤ sourceWeight thetaSource x from (sourceWeight_pos thetaSource x).le)]
  unfold sourceModeFWeightedEnergyDensity sourceWeight
  field_simp

/-! ### Promotion to the fixed compact operator -/

open HedenmalmHilbertSchmidt

local instance factTwoNeTopThetaCompactDivisorEigenmode : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- The pinned kernel field evaluates to the intrinsic pinned primitive. -/
theorem pinnedKernelField_apply_eq_pinnedVolterraFun (S : PositiveDensitySource) (t : ℝ)
    (f : Lp ℂ 2 unitIntervalMeasure) :
    pinnedKernelField S t f =
      Complex.I * (quantileSpeed S t : ℂ) * pinnedVolterraFun f t := by
  have hinner : (inner ℂ (pinnedSliceVec t) f : ℂ) = pinnedVolterraFun f t := by
    rw [MeasureTheory.L2.inner_def, pinnedVolterraFun, pinnedPrefix, pinnedMean]
    have hcoe : (fun u => (inner ℂ ((pinnedSliceVec t : ℝ → ℂ) u) (f u) : ℂ))
        =ᵐ[unitIntervalMeasure]
        fun u => (Iic t).indicator (fun u => f u) u - (t : ℂ) * f u := by
      filter_upwards [pinnedSliceVec_coeFn t] with u hu
      rw [hu, RCLike.inner_apply', pinnedKernelSlice]
      by_cases hut : u ≤ t <;> simp [hut] <;> ring
    rw [integral_congr_ae hcoe,
      MeasureTheory.integral_sub ((integrable_coe f).indicator measurableSet_Iic)
        ((integrable_coe f).const_mul (t : ℂ)),
      MeasureTheory.integral_const_mul]
  rw [pinnedKernelField]
  change (inner ℂ
      ((-(Complex.I * (quantileSpeed S t : ℂ))) • pinnedSliceVec t) f : ℂ) = _
  rw [inner_smul_left, hinner]
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- The field-form kernel operator has the expected pointwise representative. -/
theorem pinnedKernelOperator_ae (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S)
    (f : Lp ℂ 2 unitIntervalMeasure) :
    kernelOperator (E := Lp ℂ 2 unitIntervalMeasure) unitIntervalMeasure
        (pinnedKernelL2 S hfin) f =ᵐ[unitIntervalMeasure]
      fun t => pinnedKernelField S t f := by
  have hholder :=
    (evalBilinear (𝕜 := ℂ) (E := Lp ℂ 2 unitIntervalMeasure)).coeFn_holder
      (r := (2 : ENNReal)) (pinnedKernelL2 S hfin)
      (Lp.const ∞ unitIntervalMeasure f)
  have hfield := (memLp_pinnedKernelField S hfin).coeFn_toLp
  have hconst := Lp.coeFn_const (p := ∞) unitIntervalMeasure f
  filter_upwards [hholder, hfield, hconst] with t hholderT hfieldT hconstT
  rw [kernelOperator, kernelOperatorMap_apply, hholderT, pinnedKernelL2, hfieldT, hconstT]
  simp [evalBilinear]

/-- The source inverse depends only on the Lebesgue almost-everywhere class of its input. -/
theorem sourceInverse_congr_ae (S : PositiveDensitySource) {f g : ℝ → ℂ}
    (hfg : f =ᵐ[(volume : Measure ℝ)] g) (x : ℝ) :
    sourceInverse S f x = sourceInverse S g x := by
  have htotal : (∫ y, f y) = ∫ y, g y := integral_congr_ae hfg
  rw [sourceInverse, htotal]
  congr 1
  refine setIntegral_congr_ae measurableSet_Iic ?_
  filter_upwards [hfg] with y hy _
  rw [hy]

/-- Canonical weighted source-space vector attached to a theta divisor. -/
def thetaDivisorSourceVector (z : ℂ) (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) : SourceSpace thetaSource :=
  (memLp_sourceModeF_thetaSource_weighted hz hzero).toLp _

theorem thetaDivisorSourceVector_ae (z : ℂ) (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    (thetaDivisorSourceVector z hz hzero : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)]
      sourceModeF thetaSource z := by
  exact (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
    (sourceWeight_pos thetaSource)).mp
      (MemLp.coeFn_toLp (memLp_sourceModeF_thetaSource_weighted hz hzero))

/-- Canonical divisor vector is nonzero because its Lebesgue integral is the positive source
mass. -/
theorem thetaDivisorSourceVector_ne_zero (z : ℂ) (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    thetaDivisorSourceVector z hz hzero ≠ 0 := by
  intro hv
  have hae := thetaDivisorSourceVector_ae z hz hzero
  rw [hv] at hae
  have hzeroWeighted :
      ((0 : SourceSpace thetaSource) : ℝ → ℂ) =ᵐ[
        (volume : Measure ℝ).withDensity
          (realDensity (sourceWeight thetaSource))] fun _ => 0 :=
    Lp.coeFn_zero ℂ 2 _
  have hzeroLeb :
      ((0 : SourceSpace thetaSource) : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)] fun _ => 0 :=
    (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
      (sourceWeight_pos thetaSource)).mp hzeroWeighted
  have hfzero : sourceModeF thetaSource z =ᵐ[(volume : Measure ℝ)] fun _ => 0 :=
    hae.symm.trans hzeroLeb
  have hmass := integral_sourceModeF_thetaSource_eq_mass hz hzero
  have hmassZero : (thetaSource.mass : ℂ) = 0 := by
    rw [← hmass, integral_congr_ae hfzero, integral_zero]
  have hmassNe : (thetaSource.mass : ℂ) ≠ 0 := by
    exact_mod_cast thetaSource.mass_ne_zero
  exact hmassNe hmassZero

/-- Pullback of the canonical representative along the theta quantile. -/
theorem thetaDivisorSourceVector_quantile_ae (z : ℂ) (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    (fun t => (thetaDivisorSourceVector z hz hzero)
        (thetaSource.quantileFun t)) =ᵐ[unitIntervalMeasure]
      fun t => sourceModeF thetaSource z (thetaSource.quantileFun t) := by
  have hlaw : (thetaDivisorSourceVector z hz hzero : ℝ → ℂ) =ᵐ[thetaSource.law]
      sourceModeF thetaSource z :=
    (thetaSource.law_ae_eq).mpr (thetaDivisorSourceVector_ae z hz hzero)
  exact hlaw.comp_tendsto
    (measurePreserving_quantile_unitInterval thetaSource).quasiMeasurePreserving.tendsto_ae

/-- Fixed compact source inverse obtained solely from the theta density. -/
def thetaCompactSourceInverse :
    Lp ℂ 2 unitIntervalMeasure →L[ℂ] Lp ℂ 2 unitIntervalMeasure :=
  kernelOperator (E := Lp ℂ 2 unitIntervalMeasure) unitIntervalMeasure
    (pinnedKernelL2 thetaSource hasFiniteKernelEnergy_thetaSource)

theorem isCompactOperator_thetaCompactSourceInverse :
    IsCompactOperator thetaCompactSourceInverse :=
  isCompactOperator_thetaKernelOperator

/-- Quantile-coordinate image of the canonical divisor vector. -/
def thetaDivisorEigenvector (z : ℂ) (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) : Lp ℂ 2 unitIntervalMeasure :=
  quantileUnitary thetaSource (thetaDivisorSourceVector z hz hzero)

theorem thetaDivisorEigenvector_ne_zero (z : ℂ) (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    thetaDivisorEigenvector z hz hzero ≠ 0 := by
  intro hzeroVector
  apply thetaDivisorSourceVector_ne_zero z hz hzero
  apply (quantileUnitary thetaSource).injective
  simpa only [thetaDivisorEigenvector, map_zero] using hzeroVector

/-- **Unconditional compact divisor eigenmode.** Every zero of the completed theta transform in
its natural strip is a nonzero eigenmode of one fixed compact operator constructed from the theta
density, with reciprocal eigenvalue `-z⁻¹`. -/
theorem thetaCompactSourceInverse_eigen (z : ℂ) (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    thetaCompactSourceInverse (thetaDivisorEigenvector z hz hzero) =
      (-z⁻¹) • thetaDivisorEigenvector z hz hzero := by
  let g : Lp ℂ 2 unitIntervalMeasure := thetaDivisorEigenvector z hz hzero
  change thetaCompactSourceInverse g = (-z⁻¹) • g
  apply Lp.ext
  let v : SourceSpace thetaSource := thetaDivisorSourceVector z hz hzero
  have hgv : g = quantileUnitary thetaSource v := by rfl
  have hv : (v : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)] sourceModeF thetaSource z :=
    thetaDivisorSourceVector_ae z hz hzero
  have hvq : (fun t => v (thetaSource.quantileFun t)) =ᵐ[unitIntervalMeasure]
      fun t => sourceModeF thetaSource z (thetaSource.quantileFun t) :=
    thetaDivisorSourceVector_quantile_ae z hz hzero
  filter_upwards [pinnedKernelOperator_ae thetaSource hasFiniteKernelEnergy_thetaSource g,
    ae_unitIntervalMeasure_mem_Ioo, quantileUnitary_ae thetaSource v, hvq,
    Lp.coeFn_smul (-z⁻¹) g] with t hoperator ht hg hvqt hsmul
  rw [hsmul]
  change (thetaCompactSourceInverse g : ℝ → ℂ) t = (-z⁻¹) * g t
  rw [thetaCompactSourceInverse, hoperator,
    pinnedKernelField_apply_eq_pinnedVolterraFun]
  rw [hgv]
  rw [← quantileTransform_sourceInverse_eq_pinned thetaSource v ht]
  unfold quantileTransform
  rw [sourceInverse_congr_ae thetaSource hv (thetaSource.quantileFun t),
    sourceInverse_sourceModeF_eq_smul_thetaSource hz hzero]
  rw [hg, hvqt]
  ring

end HedenmalmThetaSource

end

end RHTower
