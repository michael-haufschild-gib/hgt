import GaloisForLFunctions.RHTower.HedenmalmThetaRootModeDecay

/-!
# The endpoint hypotheses of the quantile flux identity are theorems

The quantile root mode is the source mode read in the quantile coordinate,

`h(t) = -(1/M) i u_z(Q t)`,

so the exponential decay of `u_z` at a zero of the completed transform gives all four endpoint
conditions of the flux identity: the two boundary limits, boundedness (hence integrability of the
value), and integrability of the energy after the quantile change of variables.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmPrimeTranslation

variable (S : PositiveDensitySource)

/-! ### The root primitive is the source primitive in quantile coordinates -/

theorem rootA_eq_sourceModeI (z : ℂ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    rootA S z t = sourceModeI S z (S.quantileFun t) / (S.mass : ℂ) := by
  have hmeas : AEStronglyMeasurable (sourceChar z) (volume : Measure ℝ) :=
    (continuous_sourceChar z).aestronglyMeasurable
  have h := setIntegral_comp_quantile S (sourceChar z) hmeas ht
  have hpt : ∀ x : ℝ, S.normalized x • sourceChar z x
      = (S.k x : ℂ) * sourceChar z x / (S.mass : ℂ) := by
    intro x
    rw [Complex.real_smul, show S.normalized x = S.k x / S.mass from rfl]
    push_cast
    ring
  rw [rootA, intervalIntegral.integral_of_le ht.1.le,
    MeasureTheory.integral_Ioc_eq_integral_Ioo, h,
    setIntegral_congr_fun measurableSet_Iic (fun x _ => hpt x),
    MeasureTheory.integral_div, sourceModeI]

theorem norm_rootH_eq (z : ℂ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ‖rootH S z t‖ = ‖sourceModeU S z (S.quantileFun t)‖ / S.mass := by
  have hM : (0 : ℝ) < S.mass := S.mass_pos
  rw [rootH, norm_neg, norm_mul, rootA_eq_sourceModeI S z ht, sourceModeU, norm_mul, norm_mul,
    norm_neg, Complex.norm_I, one_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hM, rootFactor]
  ring

/-! ### The two boundary limits of the quantile coordinate -/

theorem tendsto_quantileFun_nhdsGT_zero : Tendsto S.quantileFun (𝓝[>] (0 : ℝ)) atBot := by
  refine tendsto_atBot.mpr fun M => ?_
  have hc : S.cdfFun M ∈ Ioo (0 : ℝ) 1 := S.cdfFun_mem_Ioo M
  have hmem : Ioo (0 : ℝ) (S.cdfFun M) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT hc.1
  filter_upwards [hmem] with t ht
  have htmem : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, lt_trans ht.2 hc.2⟩
  have hlt := S.strictMonoOn_quantileFun htmem hc ht.2
  rw [S.quantile_cdfFun] at hlt
  exact hlt.le

theorem tendsto_quantileFun_nhdsLT_one : Tendsto S.quantileFun (𝓝[<] (1 : ℝ)) atTop := by
  refine tendsto_atTop.mpr fun M => ?_
  have hc : S.cdfFun M ∈ Ioo (0 : ℝ) 1 := S.cdfFun_mem_Ioo M
  have hmem : Ioo (S.cdfFun M) (1 : ℝ) ∈ 𝓝[<] (1 : ℝ) :=
    Ioo_mem_nhdsLT hc.2
  filter_upwards [hmem] with t ht
  have htmem : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans hc.1 ht.1, ht.2⟩
  have hlt := S.strictMonoOn_quantileFun hc htmem ht.1
  rw [S.quantile_cdfFun] at hlt
  exact hlt.le


theorem rootH_eq_sourceModeU (z : ℂ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    rootH S z t = (-Complex.I / (S.mass : ℂ)) * sourceModeU S z (S.quantileFun t) := by
  have hM : ((S.mass : ℝ) : ℂ) ≠ 0 := by exact_mod_cast S.mass_ne_zero
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [rootH, rootA_eq_sourceModeI S z ht, sourceModeU, rootFactor]
  field_simp
  linear_combination (-(sourceModeI S z (S.quantileFun t))) * hI


/-! ### The endpoint bundle at a zero of the completed transform -/

theorem continuous_sourceModeU {z : ℂ} (hz : |z.im| < 1) :
    Continuous (sourceModeU thetaSource z) := by
  have hI : Continuous (sourceModeI thetaSource z) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_sourceModeI thetaSource (hasShiftedTail_thetaSource hz) x).continuousAt
  have hexp : Continuous fun x : ℝ => Complex.exp (-(Complex.I * z) * (x : ℂ)) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  exact (continuous_const.mul hexp).mul hI

theorem norm_sq_sourceModeU_le {z : ℂ} (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0)
    (x : ℝ) :
    ‖sourceModeU thetaSource z x‖ ^ (2 : ℕ)
      ≤ (thetaBound / (1 - |z.im|)) ^ (2 : ℕ) * Real.exp (-(2 * |x|)) := by
  have hgap : (0 : ℝ) < 1 - |z.im| := by linarith
  have hC : 0 ≤ thetaBound / (1 - |z.im|) := div_nonneg thetaBound_nonneg hgap.le
  have h := norm_sourceModeU_le hz hzero x
  have hsq : ‖sourceModeU thetaSource z x‖ ^ (2 : ℕ)
      ≤ (thetaBound / (1 - |z.im|) * Real.exp (-|x|)) ^ (2 : ℕ) := by
    have hnn := norm_nonneg (sourceModeU thetaSource z x)
    nlinarith [h, hnn]
  refine le_trans hsq (le_of_eq ?_)
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem integrable_norm_sq_sourceModeU {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    Integrable (fun x : ℝ => ‖sourceModeU thetaSource z x‖ ^ (2 : ℕ)) (volume : Measure ℝ) := by
  refine Integrable.mono'
    ((integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic (by norm_num : (0:ℝ) < 2)).const_mul
      ((thetaBound / (1 - |z.im|)) ^ (2 : ℕ))) ?_ ?_
  · exact ((continuous_sourceModeU hz).norm.pow 2).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact norm_sq_sourceModeU_le hz hzero x

theorem tendsto_norm_sq_sourceModeU {z : ℂ} (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0) :
    Tendsto (fun x : ℝ => ‖sourceModeU thetaSource z x‖ ^ (2 : ℕ)) atBot (𝓝 0)
      ∧ Tendsto (fun x : ℝ => ‖sourceModeU thetaSource z x‖ ^ (2 : ℕ)) atTop (𝓝 0) := by
  have hdom : ∀ l : Filter ℝ, Tendsto (fun x : ℝ => -(2 * |x|)) l atBot →
      Tendsto (fun x : ℝ => (thetaBound / (1 - |z.im|)) ^ (2 : ℕ) * Real.exp (-(2 * |x|))) l (𝓝 0) := by
    intro l hl
    simpa using (Real.tendsto_exp_atBot.comp hl).const_mul ((thetaBound / (1 - |z.im|)) ^ (2 : ℕ))
  have hbot : Tendsto (fun x : ℝ => -(2 * |x|)) atBot atBot :=
    tendsto_neg_atTop_atBot.comp (tendsto_abs_atBot_atTop.const_mul_atTop (by norm_num : (0:ℝ) < 2))
  have htop : Tendsto (fun x : ℝ => -(2 * |x|)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (tendsto_abs_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ) < 2))
  exact ⟨squeeze_zero (fun x => sq_nonneg _) (fun x => norm_sq_sourceModeU_le hz hzero x)
      (hdom _ hbot),
    squeeze_zero (fun x => sq_nonneg _) (fun x => norm_sq_sourceModeU_le hz hzero x)
      (hdom _ htop)⟩

/-- **The endpoint hypotheses of the quantile flux identity hold at every zero of the completed
transform.**  No assumption on the source remains. -/
theorem rootModeEndpoints_thetaSource {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) : RootModeEndpoints thetaSource z := by
  have hM : (0 : ℝ) < thetaSource.mass := thetaSource.mass_pos
  have hMne : (thetaSource.mass : ℝ) ≠ 0 := hM.ne'
  have hcont := continuous_sourceModeU hz
  obtain ⟨hbot, htop⟩ := tendsto_norm_sq_sourceModeU hz hzero
  have hIoo : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT one_pos
  have hIoo' : Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT one_pos
  have hnormsq : ∀ t ∈ Ioo (0 : ℝ) 1, ‖rootH thetaSource z t‖ ^ (2 : ℕ)
      = ‖sourceModeU thetaSource z (thetaSource.quantileFun t)‖ ^ (2 : ℕ) / thetaSource.mass ^ (2 : ℕ) := by
    intro t ht
    rw [norm_rootH_eq thetaSource z ht, div_pow]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- energy
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ => ‖sourceModeU thetaSource z x‖ ^ (2 : ℕ) / (thetaSource.mass * thetaSource.k x))
        (volume : Measure ℝ) := by
      refine ((hcont.norm.pow 2).div (continuous_const.mul thetaSource.continuous_k)
        fun x => ?_).aestronglyMeasurable
      exact mul_ne_zero hMne (thetaSource.pos_k x).ne'
    have hiff := thetaSource.integrableOn_comp_quantileFun_iff (g := fun x : ℝ =>
      ‖sourceModeU thetaSource z x‖ ^ (2 : ℕ) / (thetaSource.mass * thetaSource.k x)) hmeas
    have hright : Integrable (fun x : ℝ => thetaSource.normalized x •
        (‖sourceModeU thetaSource z x‖ ^ (2 : ℕ) / (thetaSource.mass * thetaSource.k x)))
        (volume : Measure ℝ) := by
      refine ((integrable_norm_sq_sourceModeU hz hzero).div_const
        (thetaSource.mass ^ (2 : ℕ))).congr ?_
      filter_upwards with x
      have hk : thetaSource.k x ≠ 0 := (thetaSource.pos_k x).ne'
      show ‖sourceModeU thetaSource z x‖ ^ (2 : ℕ) / thetaSource.mass ^ (2 : ℕ)
        = thetaSource.normalized x •
          (‖sourceModeU thetaSource z x‖ ^ (2 : ℕ) / (thetaSource.mass * thetaSource.k x))
      show ‖sourceModeU thetaSource z x‖ ^ (2 : ℕ) / thetaSource.mass ^ (2 : ℕ)
        = (thetaSource.k x / thetaSource.mass) *
          (‖sourceModeU thetaSource z x‖ ^ (2 : ℕ) / (thetaSource.mass * thetaSource.k x))
      field_simp
    refine MeasureTheory.IntegrableOn.congr_fun (hiff.mpr hright) (fun t ht => ?_)
      measurableSet_Ioo
    show ‖sourceModeU thetaSource z (thetaSource.quantileFun t)‖ ^ (2 : ℕ)
        / (thetaSource.mass * thetaSource.k (thetaSource.quantileFun t))
      = quantileSpeed thetaSource t * ‖rootH thetaSource z t‖ ^ (2 : ℕ)
    rw [hnormsq t ht, quantileSpeed]
    have hk : thetaSource.k (thetaSource.quantileFun t) ≠ 0 :=
      (thetaSource.pos_k _).ne'
    field_simp
  · -- value
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ => (-Complex.I / (thetaSource.mass : ℂ)) * sourceModeU thetaSource z x)
        (volume : Measure ℝ) := (continuous_const.mul hcont).aestronglyMeasurable
    have hiff := thetaSource.integrableOn_comp_quantileFun_iff (g := fun x : ℝ =>
      (-Complex.I / (thetaSource.mass : ℂ)) * sourceModeU thetaSource z x) hmeas
    have hbdd : ∀ x : ℝ, ‖thetaSource.normalized x •
        ((-Complex.I / (thetaSource.mass : ℂ)) * sourceModeU thetaSource z x)‖
        ≤ thetaBound / (1 - |z.im|) / thetaSource.mass ^ (2 : ℕ) * thetaSource.k x := by
      intro x
      have hgap : (0 : ℝ) < 1 - |z.im| := by linarith
      have hCnn : 0 ≤ thetaBound / (1 - |z.im|) := div_nonneg thetaBound_nonneg hgap.le
      have hn : 0 ≤ thetaSource.normalized x := div_nonneg (thetaSource.pos_k x).le hM.le
      have hu' : ‖sourceModeU thetaSource z x‖ ≤ thetaBound / (1 - |z.im|) := by
        refine le_trans (norm_sourceModeU_le hz hzero x) ?_
        have hexp : Real.exp (-|x|) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          simp
        nlinarith [Real.exp_pos (-|x|)]
      have hnorm : ‖thetaSource.normalized x •
          ((-Complex.I / (thetaSource.mass : ℂ)) * sourceModeU thetaSource z x)‖
          = thetaSource.normalized x * (‖sourceModeU thetaSource z x‖ / thetaSource.mass) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hn, norm_mul, norm_div, norm_neg,
          Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
        ring
      rw [hnorm]
      calc thetaSource.normalized x * (‖sourceModeU thetaSource z x‖ / thetaSource.mass)
          ≤ thetaSource.normalized x * ((thetaBound / (1 - |z.im|)) / thetaSource.mass) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hu' hM.le) hn
        _ = thetaBound / (1 - |z.im|) / thetaSource.mass ^ (2 : ℕ) * thetaSource.k x := by
            show thetaSource.k x / thetaSource.mass * _ = _
            field_simp
    have hright : Integrable (fun x : ℝ => thetaSource.normalized x •
        ((-Complex.I / (thetaSource.mass : ℂ)) * sourceModeU thetaSource z x))
        (volume : Measure ℝ) := by
      refine Integrable.mono'
        (thetaSource.integrable_k.const_mul
          (thetaBound / (1 - |z.im|) / thetaSource.mass ^ (2 : ℕ))) ?_ ?_
      · refine (Continuous.aestronglyMeasurable ?_)
        have h1 : Continuous thetaSource.normalized :=
          thetaSource.continuous_k.div_const thetaSource.mass
        have h2 : Continuous fun x : ℝ =>
            (-Complex.I / (thetaSource.mass : ℂ)) * sourceModeU thetaSource z x :=
          continuous_const.mul hcont
        exact h1.smul h2
      · filter_upwards with x
        exact hbdd x
    refine MeasureTheory.IntegrableOn.congr_fun (hiff.mpr hright) (fun t ht => ?_)
      measurableSet_Ioo
    exact (rootH_eq_sourceModeU thetaSource z ht).symm
  · -- left endpoint
    have hbase : Tendsto (fun t : ℝ =>
        ‖sourceModeU thetaSource z (thetaSource.quantileFun t)‖ ^ (2 : ℕ) / thetaSource.mass ^ (2 : ℕ))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using
        (hbot.comp (tendsto_quantileFun_nhdsGT_zero thetaSource)).div_const
          (thetaSource.mass ^ (2 : ℕ))
    refine hbase.congr' ?_
    filter_upwards [hIoo] with t ht
    exact (hnormsq t ht).symm
  · -- right endpoint
    have hbase : Tendsto (fun t : ℝ =>
        ‖sourceModeU thetaSource z (thetaSource.quantileFun t)‖ ^ (2 : ℕ) / thetaSource.mass ^ (2 : ℕ))
        (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      simpa using
        (htop.comp (tendsto_quantileFun_nhdsLT_one thetaSource)).div_const
          (thetaSource.mass ^ (2 : ℕ))
    refine hbase.congr' ?_
    filter_upwards [hIoo'] with t ht
    exact (hnormsq t ht).symm


/-- **The quantile flux identity at a zero of the completed transform, unconditionally.**
Both hypotheses of the general flux identity are now theorems about the arithmetic source. -/
theorem rootFlux_identity_thetaSource {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    (∫ t in Ioo (0 : ℝ) 1, -(rootH thetaSource z t)).re
      = -(z.im) * ∫ t in Ioo (0 : ℝ) 1,
          quantileSpeed thetaSource t * ‖rootH thetaSource z t‖ ^ (2 : ℕ) :=
  rootFlux_identity thetaSource (hasShiftedTail_thetaSource hz)
    (rootModeEndpoints_thetaSource hz hzero)


/-! ### The source mode at a divisor point -/

theorem integrable_sourceModeU {z : ℂ} (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0) :
    Integrable (sourceModeU thetaSource z) (volume : Measure ℝ) := by
  have hgap : (0 : ℝ) < 1 - |z.im| := by linarith
  refine Integrable.mono'
    ((integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic (by norm_num : (0:ℝ) < 1)).const_mul
      (thetaBound / (1 - |z.im|))) (continuous_sourceModeU hz).aestronglyMeasurable ?_
  filter_upwards with x
  rw [one_mul]
  exact norm_sourceModeU_le hz hzero x

theorem tendsto_sourceModeU_atBot {z : ℂ} (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0) :
    Tendsto (sourceModeU thetaSource z) atBot (𝓝 0) := by
  have habs : Tendsto (fun x : ℝ => -|x|) atBot atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_abs_atBot_atTop
  have hdom : Tendsto
      (fun x : ℝ => thetaBound / (1 - |z.im|) * Real.exp (-|x|)) atBot (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp habs).const_mul (thetaBound / (1 - |z.im|))
  exact squeeze_zero_norm (fun x => norm_sourceModeU_le hz hzero x) hdom

theorem tendsto_sourceModeU_atTop {z : ℂ} (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0) :
    Tendsto (sourceModeU thetaSource z) atTop (𝓝 0) := by
  have habs : Tendsto (fun x : ℝ => -|x|) atTop atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_abs_atTop_atTop
  have hdom : Tendsto
      (fun x : ℝ => thetaBound / (1 - |z.im|) * Real.exp (-|x|)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp habs).const_mul (thetaBound / (1 - |z.im|))
  exact squeeze_zero_norm (fun x => norm_sourceModeU_le hz hzero x) hdom

/-- **A source solution with any nonzero coefficient forces a zero of the completed Riemann
function.**  This is the forward half of the divisor equivalence, with no hypothesis on the
source. -/
theorem XiC_eq_zero_of_solution_const {α c : ℂ} (hc : c ≠ 0) (hα : |α.im| < 1) {u u' : ℝ → ℂ}
    (hderiv : ∀ x, HasDerivAt u (u' x) x)
    (heq : ∀ x, -Complex.I * u' x + α * u x = c * ((thetaCuspFullSource x : ℝ) : ℂ))
    (hbot : Tendsto (fun x => u x * sourceChar α x) atBot (𝓝 0))
    (htop : Tendsto (fun x => u x * sourceChar α x) atTop (𝓝 0)) :
    XiC α = 0 := by
  have h := HedenmalmHilbertSchmidt.xiC_eq_zero_of_solution_const thetaSource hc hderiv heq
    (hasShiftedTail_thetaSource hα) hbot htop
  rwa [xiC_thetaSource hα] at h



/-- **The total mass of the source mode at a divisor point.**  Integrating the source equation
across the line, with both boundary values zero, gives `∫ u_z = -M/z`. -/
theorem integral_sourceModeU {z : ℂ} (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0)
    (hz0 : z ≠ 0) :
    (∫ x : ℝ, sourceModeU thetaSource z x) = -(thetaSource.mass : ℂ) / z := by
  have hIz : Complex.I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz0
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hu : Integrable (sourceModeU thetaSource z) (volume : Measure ℝ) :=
    integrable_sourceModeU hz hzero
  have hkC : Integrable (fun x : ℝ => ((thetaSource.k x : ℝ) : ℂ)) (volume : Measure ℝ) :=
    thetaSource.integrable_k.ofReal
  have hderiv : ∀ x : ℝ, HasDerivAt (sourceModeU thetaSource z)
      (-(Complex.I * z) * sourceModeU thetaSource z x
        - Complex.I * ((thetaSource.k x : ℝ) : ℂ)) x :=
    hasDerivAt_sourceModeU thetaSource (hasShiftedTail_thetaSource hz)
  have hint : Integrable (fun x : ℝ => -(Complex.I * z) * sourceModeU thetaSource z x
      - Complex.I * ((thetaSource.k x : ℝ) : ℂ)) (volume : Measure ℝ) :=
    (hu.const_mul _).sub (hkC.const_mul _)
  have hzeroInt := MeasureTheory.integral_of_hasDerivAt_of_tendsto hderiv hint
    (tendsto_sourceModeU_atBot hz hzero) (tendsto_sourceModeU_atTop hz hzero)
  rw [sub_zero] at hzeroInt
  rw [MeasureTheory.integral_sub (hu.const_mul _) (hkC.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hzeroInt
  have hmass : (∫ x : ℝ, ((thetaSource.k x : ℝ) : ℂ)) = ((thetaSource.mass : ℝ) : ℂ) := by
    rw [integral_complex_ofReal]
    rfl
  rw [hmass] at hzeroInt
  have hsolve : Complex.I * z * (∫ x : ℝ, sourceModeU thetaSource z x)
      = -(Complex.I * ((thetaSource.mass : ℝ) : ℂ)) := by
    linear_combination -hzeroInt
  have hJ : (∫ x : ℝ, sourceModeU thetaSource z x)
      = -(Complex.I * ((thetaSource.mass : ℝ) : ℂ)) / (Complex.I * z) := by
    rw [eq_div_iff hIz]
    linear_combination hsolve
  rw [hJ]
  have hIne : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp



theorem integrable_sourceModeF {z : ℂ} (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0) :
    Integrable (sourceModeF thetaSource z) (volume : Measure ℝ) := by
  have h := (integrable_sourceModeU hz hzero).const_mul (-z)
  refine h.congr ?_
  filter_upwards with x
  exact (sourceModeF_eq thetaSource x).symm

theorem integral_sourceModeF {z : ℂ} (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0)
    (hz0 : z ≠ 0) :
    (∫ x : ℝ, sourceModeF thetaSource z x) = ((thetaSource.mass : ℝ) : ℂ) := by
  have h : (∫ x : ℝ, sourceModeF thetaSource z x)
      = -z * ∫ x : ℝ, sourceModeU thetaSource z x := by
    rw [← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => sourceModeF_eq thetaSource x)
  rw [h, integral_sourceModeU hz hzero hz0]
  field_simp

/-- **The right mode of the Riemann source is an eigenvector of the source inverse**, with
eigenvalue `-1/z`, at every zero of the completed Riemann function.  No hypothesis on the source
remains. -/
theorem sourceInverse_sourceModeF_eq_smul_theta {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) (hz0 : z ≠ 0) (x : ℝ) :
    sourceInverse thetaSource (sourceModeF thetaSource z) x
      = (-z⁻¹) * sourceModeF thetaSource z x :=
  HedenmalmHilbertSchmidt.sourceInverse_sourceModeF_eq_smul thetaSource hz0
    (hasShiftedTail_thetaSource hz) (integrable_sourceModeF hz hzero)
    (tendsto_sourceModeU_atBot hz hzero) (integral_sourceModeF hz hzero hz0) x


end HedenmalmThetaSource

end

end RHTower
