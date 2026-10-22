import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaAllShiftedTails
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceDeterminantMultiplicity
import GaloisForLFunctions.RHTower.XiHedenmalmThetaBorelHilbert

/-!
# Exact point spectrum of the fixed Hedenmalm theta source inverse

This module proves the missing converse to the explicit divisor-mode construction.  An arbitrary
eigenvector of the fixed compact quantile operator is pulled back through the quantile unitary.
The kernel representative and the quantile normal form then show that its source representative
satisfies the source-inverse eigen-equation almost everywhere.  Subsequent regularity and endpoint
arguments identify the spectral parameter with a zero of the completed theta transform.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmHilbertSchmidt

local instance factTwoNeTopThetaSourceSpectrumExact : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- Every weighted source-space vector remains Lebesgue integrable after multiplication by any
complex source character.  The two `L²` factors are `v / √k` and `√k · exp(izx)`; the
all-shift theorem supplies the second factor for arbitrary `z`. -/
theorem integrable_sourceSpace_mul_sourceChar
    (v : SourceSpace thetaSource) (z : ℂ) :
    Integrable (fun x : ℝ => v x * sourceChar z x) (volume : Measure ℝ) := by
  have hv : MemLp
      (fun x => sqrtWeight (sourceWeight thetaSource) x * v x)
      2 (volume : Measure ℝ) :=
    (memLp_two_withDensity_iff (measurable_sourceWeight thetaSource)
      (sourceWeight_pos thetaSource)).mp (Lp.memLp v)
  have hchar : MemLp
      (fun x : ℝ => ((Real.sqrt (thetaSource.k x) : ℝ) : ℂ) * sourceChar z x)
      2 (volume : Measure ℝ) := by
    have hcont : Continuous
        (fun x : ℝ => ((Real.sqrt (thetaSource.k x) : ℝ) : ℂ) * sourceChar z x) :=
      (Complex.continuous_ofReal.comp
        (Real.continuous_sqrt.comp thetaSource.continuous_k)).mul
          (continuous_sourceChar z)
    refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr ?_
    refine (integrable_exp_mul_thetaCuspFullSource (-2 * z.im)).congr ?_
    filter_upwards with x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), norm_sourceChar, mul_pow,
      Real.sq_sqrt (thetaSource.pos_k x).le, thetaSource_k]
    have hexp : Real.exp (-z.im * x) ^ 2 =
        Real.exp ((-2 * z.im) * x) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hexp]
    ring
  have hprod := MemLp.integrable_mul hv hchar
  refine hprod.congr ?_
  filter_upwards with x
  have hk : (0 : ℝ) < thetaSource.k x := thetaSource.pos_k x
  have hkne : Real.sqrt (thetaSource.k x) ≠ 0 := (Real.sqrt_pos.mpr hk).ne'
  have hkc : ((Real.sqrt (thetaSource.k x) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hkne
  have hsw : sqrtWeight (sourceWeight thetaSource) x =
      (((Real.sqrt (thetaSource.k x))⁻¹ : ℝ) : ℂ) := by
    rw [sqrtWeight]
    norm_cast
    rw [show sourceWeight thetaSource x = (thetaSource.k x)⁻¹ from rfl,
      Real.sqrt_inv]
  show sqrtWeight (sourceWeight thetaSource) x * v x *
      (((Real.sqrt (thetaSource.k x) : ℝ) : ℂ) * sourceChar z x) =
    v x * sourceChar z x
  rw [hsw]
  push_cast
  field_simp [hkc]

/-- The explicit source inverse of any integrable input has a continuous representative. -/
theorem continuous_sourceInverse_of_integrable {g : ℝ → ℂ}
    (hg : Integrable g (volume : Measure ℝ)) :
    Continuous (sourceInverse thetaSource g) := by
  let c : ℂ := (∫ x, g x) / (thetaSource.mass : ℂ)
  let G : ℝ → ℂ := fun x => g x - c * (thetaSource.k x : ℂ)
  have hG : Integrable G (volume : Measure ℝ) := by
    exact hg.sub (thetaSource.integrable_k.ofReal.const_mul c)
  have hsplit : ∀ x : ℝ,
      (∫ y in Iic x, G y) =
        (∫ y in Iic (0 : ℝ), G y) + ∫ y in (0 : ℝ)..x, G y := by
    intro x
    rcases le_total (0 : ℝ) x with hx | hx
    · rw [intervalIntegral.integral_of_le hx, ← MeasureTheory.setIntegral_union
          (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
          hG.integrableOn hG.integrableOn,
        Iic_union_Ioc_eq_Iic hx]
    · rw [intervalIntegral.integral_of_ge hx]
      have hs : (∫ y in Iic (0 : ℝ), G y) =
          (∫ y in Iic x, G y) + ∫ y in Ioc x (0 : ℝ), G y := by
        rw [← MeasureTheory.setIntegral_union
            (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
            hG.integrableOn hG.integrableOn,
          Iic_union_Ioc_eq_Iic hx]
      rw [hs]
      ring
  have hprimitive : Continuous (fun x : ℝ => ∫ y in Iic x, G y) := by
    have hinterval := hG.continuous_primitive 0
    exact (continuous_const.add hinterval).congr (fun x => (hsplit x).symm)
  unfold sourceInverse
  change Continuous (fun x : ℝ => Complex.I * ∫ y in Iic x, G y)
  exact continuous_const.mul hprimitive

/-- For a continuous integrable input, the source inverse differentiates to its centered source
integrand. -/
theorem hasDerivAt_sourceInverse_of_continuous_integrable
    {g : ℝ → ℂ} (hgcont : Continuous g)
    (hg : Integrable g (volume : Measure ℝ)) (x : ℝ) :
    HasDerivAt (sourceInverse thetaSource g)
      (Complex.I *
        (g x - ((∫ y, g y) / (thetaSource.mass : ℂ)) *
          (thetaSource.k x : ℂ))) x := by
  let c : ℂ := (∫ y, g y) / (thetaSource.mass : ℂ)
  let G : ℝ → ℂ := fun y => g y - c * (thetaSource.k y : ℂ)
  have hGcont : Continuous G :=
    hgcont.sub (continuous_const.mul
      (Complex.continuous_ofReal.comp thetaSource.continuous_k))
  have hG : Integrable G (volume : Measure ℝ) :=
    hg.sub (thetaSource.integrable_k.ofReal.const_mul c)
  change HasDerivAt (fun t : ℝ => Complex.I * ∫ y in Iic t, G y)
    (Complex.I * G x) x
  exact (HedenmalmPrimeTranslation.hasDerivAt_setIntegral_Iic hGcont hG x).const_mul
    Complex.I

/-! ### Entire Fourier--Laplace identification -/

/-- The theta Fourier--Laplace integrand is integrable at every complex parameter. -/
theorem integrable_thetaCuspFourierLaplaceIntegrand_all (w : ℂ) :
    Integrable (thetaCuspFourierLaplaceIntegrand w) (volume : Measure ℝ) := by
  have hmajor := integrable_exp_mul_thetaCuspFullSource w.im
  apply Integrable.mono hmajor
  · unfold thetaCuspFourierLaplaceIntegrand
    exact ((Complex.continuous_exp.comp
      (continuous_const.mul continuous_const |>.mul Complex.continuous_ofReal)).mul
        (Complex.continuous_ofReal.comp
          contDiff_thetaCuspFullSource.continuous)).aestronglyMeasurable
  · filter_upwards with x
    have hk : 0 ≤ thetaCuspFullSource x := (thetaCuspFullSource_pos x).le
    rw [thetaCuspFourierLaplaceIntegrand, norm_mul, Complex.norm_exp,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hk)]
    have hre : (-Complex.I * w * (x : ℂ)).re = w.im * x := by
      simp [Complex.mul_re]
    rw [hre]

/-- The first spectral derivative integrand is integrable at every complex parameter. -/
theorem integrable_thetaCuspFourierLaplaceDerivativeIntegrand_all (w : ℂ) :
    Integrable (thetaCuspFourierLaplaceDerivativeIntegrand w)
      (volume : Measure ℝ) := by
  have hmajor :=
    integrable_abs_mul_exp_abs_mul_thetaCuspFullSource |w.im|
  apply Integrable.mono hmajor
  · unfold thetaCuspFourierLaplaceDerivativeIntegrand
      thetaCuspFourierLaplaceIntegrand
    exact ((continuous_const.mul Complex.continuous_ofReal).mul
      ((Complex.continuous_exp.comp
        (continuous_const.mul continuous_const |>.mul Complex.continuous_ofReal)).mul
          (Complex.continuous_ofReal.comp
            contDiff_thetaCuspFullSource.continuous))).aestronglyMeasurable
  · filter_upwards with x
    have hk : 0 ≤ thetaCuspFullSource x := (thetaCuspFullSource_pos x).le
    have him : w.im * x ≤ |w.im| * |x| := by
      calc
        w.im * x ≤ |w.im * x| := le_abs_self _
        _ = |w.im| * |x| := abs_mul _ _
    rw [thetaCuspFourierLaplaceDerivativeIntegrand,
      thetaCuspFourierLaplaceIntegrand, norm_mul, norm_mul, norm_neg,
      Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk,
      Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg
        (mul_nonneg (abs_nonneg x) (Real.exp_pos _).le) hk)]
    have hre : (-Complex.I * w * (x : ℂ)).re = w.im * x := by
      simp [Complex.mul_re]
    rw [hre]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr him) (abs_nonneg x)) hk

/-- The theta Fourier--Laplace transform is complex differentiable at every point. -/
theorem hasDerivAt_thetaCuspFourierLaplace_all (w₀ : ℂ) :
    HasDerivAt thetaCuspFourierLaplace
      (∫ x : ℝ, thetaCuspFourierLaplaceDerivativeIntegrand w₀ x) w₀ := by
  let ε : ℝ := 1
  let B : ℝ := |w₀.im| + 1
  let bound : ℝ → ℝ := fun x =>
    |x| * Real.exp (B * |x|) * thetaCuspFullSource x
  have hε : 0 < ε := by simp [ε]
  have hbound : Integrable bound (volume : Measure ℝ) := by
    exact integrable_abs_mul_exp_abs_mul_thetaCuspFullSource B
  have hFmeas : ∀ w : ℂ,
      AEStronglyMeasurable (thetaCuspFourierLaplaceIntegrand w)
        (volume : Measure ℝ) := by
    intro w
    unfold thetaCuspFourierLaplaceIntegrand
    exact ((Complex.continuous_exp.comp
      (continuous_const.mul continuous_const |>.mul Complex.continuous_ofReal)).mul
        (Complex.continuous_ofReal.comp
          contDiff_thetaCuspFullSource.continuous)).aestronglyMeasurable
  have hdom : ∀ᵐ x : ℝ, ∀ w ∈ Metric.ball w₀ ε,
      ‖thetaCuspFourierLaplaceDerivativeIntegrand w x‖ ≤ bound x := by
    filter_upwards with x
    intro w hw
    have hdist : ‖w - w₀‖ < ε := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hw
    have himdiff : |w.im - w₀.im| ≤ ‖w - w₀‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w - w₀)
    have hwB : |w.im| ≤ B := by
      calc
        |w.im| = |w₀.im + (w.im - w₀.im)| := by ring_nf
        _ ≤ |w₀.im| + |w.im - w₀.im| := abs_add_le _ _
        _ ≤ |w₀.im| + 1 := by dsimp only [ε] at hdist; linarith
        _ = B := rfl
    have him : w.im * x ≤ B * |x| := by
      calc
        w.im * x ≤ |w.im * x| := le_abs_self _
        _ = |w.im| * |x| := abs_mul _ _
        _ ≤ B * |x| := mul_le_mul_of_nonneg_right hwB (abs_nonneg x)
    have hk : 0 ≤ thetaCuspFullSource x := (thetaCuspFullSource_pos x).le
    rw [thetaCuspFourierLaplaceDerivativeIntegrand,
      thetaCuspFourierLaplaceIntegrand, norm_mul, norm_mul, norm_neg,
      Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk]
    have hre : (-Complex.I * w * (x : ℂ)).re = w.im * x := by
      simp [Complex.mul_re]
    rw [hre]
    dsimp only [bound]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr him) (abs_nonneg x)) hk
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := thetaCuspFourierLaplaceIntegrand)
    (F' := thetaCuspFourierLaplaceDerivativeIntegrand)
    (x₀ := w₀) (s := Metric.ball w₀ ε) (bound := bound)
    (Metric.ball_mem_nhds w₀ hε)
    (Filter.Eventually.of_forall hFmeas)
    (integrable_thetaCuspFourierLaplaceIntegrand_all w₀)
    (integrable_thetaCuspFourierLaplaceDerivativeIntegrand_all w₀).1
    hdom hbound
    (by
      filter_upwards with x
      intro w _
      exact hasDerivAt_thetaCuspFourierLaplaceIntegrand w x)
  change HasDerivAt
    (fun w : ℂ => ∫ x : ℝ, thetaCuspFourierLaplaceIntegrand w x)
    (∫ x : ℝ, thetaCuspFourierLaplaceDerivativeIntegrand w₀ x) w₀
  exact hresult.2

theorem differentiable_thetaCuspFourierLaplace_all :
    Differentiable ℂ thetaCuspFourierLaplace :=
  fun w => (hasDerivAt_thetaCuspFourierLaplace_all w).differentiableAt

/-- Analytic continuation upgrades the established strip identity to the whole plane. -/
theorem thetaCuspFourierLaplace_eq_XiC_all (w : ℂ) :
    thetaCuspFourierLaplace w = XiC w := by
  let F : ℂ → ℂ := fun s => thetaCuspFourierLaplace s - XiC s
  have hFdiff : Differentiable ℂ F :=
    differentiable_thetaCuspFourierLaplace_all.sub XiC_differentiable
  have hF : AnalyticOnNhd ℂ F Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hFdiff
  let q : ℕ → ℂ := fun n => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hq_tend : Tendsto q atTop (nhds 0) := by
    have hreal : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [q, Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hq_ne (n : ℕ) : q n ≠ 0 := by
    dsimp only [q]
    norm_cast
    positivity
  have hq_within : Tendsto q atTop (nhdsWithin 0 ({0} : Set ℂ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hq_tend, Filter.Eventually.of_forall (fun n => by simpa using hq_ne n)⟩
  have hq_zero : ∀ n : ℕ, F (q n) = 0 := by
    intro n
    dsimp only [F, q]
    rw [thetaCuspFourierLaplace_ofReal]
    ring
  have hfreq : ∃ᶠ s in nhdsWithin 0 ({0} : Set ℂ)ᶜ, F s = 0 :=
    hq_within.frequently (Filter.Eventually.of_forall hq_zero).frequently
  have hzero : Set.EqOn F 0 Set.univ :=
    hF.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ 0) hfreq
  have hw := hzero (Set.mem_univ w)
  dsimp only [F] at hw
  exact sub_eq_zero.mp hw

/-- The source transform of the theta density is the completed Riemann Xi function on all of
`\mathbb C`, not merely inside the original coarse convergence strip. -/
theorem xiC_thetaSource_all (z : ℂ) : xiC thetaSource z = XiC z := by
  have hrewrite : xiC thetaSource z = thetaCuspFourierLaplace (-z) := by
    rw [xiC, thetaCuspFourierLaplace]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [thetaCuspFourierLaplaceIntegrand, sourceChar, thetaSource_k]
    rw [mul_comm]
    congr 2
    ring
  rw [hrewrite, thetaCuspFourierLaplace_eq_XiC_all, XiC_even]

/-- Pulling an operator eigenvector back through the quantile unitary gives the literal
source-inverse eigen-equation almost everywhere on the source line. -/
theorem sourceInverse_ae_eq_smul_of_thetaCompactSourceInverse_eigen
    {c : ℂ} {f : Lp ℂ 2 unitIntervalMeasure}
    (hf : thetaCompactSourceInverse f = c • f) :
    let v : SourceSpace thetaSource := (quantileUnitary thetaSource).symm f
    sourceInverse thetaSource (fun x => v x) =ᵐ[(volume : Measure ℝ)]
      fun x => c * v x := by
  let v : SourceSpace thetaSource := (quantileUnitary thetaSource).symm f
  have hvf : quantileUnitary thetaSource v = f := by
    simp [v]
  have heigen :
      (thetaCompactSourceInverse f : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
        fun t => c * f t := by
    filter_upwards [Lp.coeFn_smul c f] with t ht
    rw [hf]
    simpa [smul_eq_mul] using ht
  have hquantile := quantileUnitary_ae thetaSource v
  rw [hvf] at hquantile
  change (f : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
    fun t => quantileTransform thetaSource (fun x => v x) t at hquantile
  have hsourceQuantile :
      (fun t => sourceInverse thetaSource (fun x => v x)
        (thetaSource.quantileFun t)) =ᵐ[unitIntervalMeasure]
      fun t => c * v (thetaSource.quantileFun t) := by
    filter_upwards
      [pinnedKernelOperator_ae thetaSource hasFiniteKernelEnergy_thetaSource f,
        heigen, hquantile, ae_unitIntervalMeasure_mem_Ioo]
      with t hoperator heigen_t hquantile_t ht
    have htransform :
        quantileTransform thetaSource
            (sourceInverse thetaSource (fun x => v x)) t =
          c * quantileTransform thetaSource (fun x => v x) t := by
      calc
        quantileTransform thetaSource
            (sourceInverse thetaSource (fun x => v x)) t =
            Complex.I * (quantileSpeed thetaSource t : ℂ) *
              pinnedVolterraFun (quantileUnitary thetaSource v) t :=
          quantileTransform_sourceInverse_eq_pinned thetaSource v ht
        _ = pinnedKernelField thetaSource t f := by
          rw [hvf]
          exact (pinnedKernelField_apply_eq_pinnedVolterraFun thetaSource t f).symm
        _ = (thetaCompactSourceInverse f : ℝ → ℂ) t := by
          exact hoperator.symm
        _ = c * f t := heigen_t
        _ = c * quantileTransform thetaSource (fun x => v x) t := by
          rw [hquantile_t]
    have hk : ((thetaSource.k (thetaSource.quantileFun t) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (thetaSource.pos_k _).ne'
    have hM : ((Real.sqrt thetaSource.mass : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr thetaSource.mass_pos).ne'
    unfold quantileTransform at htransform
    field_simp [hk, hM] at htransform
    exact htransform
  have hlaw := hsourceQuantile.comp_tendsto
    (measurePreserving_cdf_unitInterval thetaSource).quasiMeasurePreserving.tendsto_ae
  have hlaw' :
      sourceInverse thetaSource (fun x => v x) =ᵐ[thetaSource.law]
        fun x => c * v x := by
    filter_upwards [hlaw] with x hx
    change sourceInverse thetaSource (fun y => v y)
      (thetaSource.quantileFun (thetaSource.cdfFun x)) =
        c * v (thetaSource.quantileFun (thetaSource.cdfFun x)) at hx
    rw [thetaSource.quantile_cdfFun] at hx
    exact hx
  exact (thetaSource.law_ae_eq).mp hlaw'

/-- **No spurious point spectrum.**  Every nonzero eigenvector of the fixed compact source inverse
at reciprocal parameter `-z⁻¹` forces the completed theta transform to vanish at `z`. -/
theorem xiC_thetaSource_eq_zero_of_thetaCompactSourceInverse_eigen
    {z : ℂ} (hz : z ≠ 0) {f : Lp ℂ 2 unitIntervalMeasure}
    (hf0 : f ≠ 0)
    (hf : thetaCompactSourceInverse f = (-z⁻¹) • f) :
    xiC thetaSource z = 0 := by
  let v : SourceSpace thetaSource := (quantileUnitary thetaSource).symm f
  let u : ℝ → ℂ := sourceInverse thetaSource (fun x => v x)
  let eig : ℂ := -z⁻¹
  have heig0 : eig ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hz)
  have hvf : quantileUnitary thetaSource v = f := by
    simp [v]
  have hvint : Integrable (fun x => (v x : ℂ)) (volume : Measure ℝ) :=
    integrable_sourceSpace thetaSource v
  have hsource : u =ᵐ[(volume : Measure ℝ)] fun x => eig * v x := by
    simpa only [u, v, eig] using
      (sourceInverse_ae_eq_smul_of_thetaCompactSourceInverse_eigen hf)
  have hucont : Continuous u := by
    exact continuous_sourceInverse_of_integrable hvint
  have huit : Integrable u (volume : Measure ℝ) := by
    refine (hvint.const_mul eig).congr ?_
    exact hsource.symm
  have hvu : (fun x => (v x : ℂ)) =ᵐ[(volume : Measure ℝ)]
      fun x => -z * u x := by
    filter_upwards [hsource] with x hx
    calc
      v x = -z * (eig * v x) := by
        dsimp only [eig]
        field_simp [hz]
      _ = -z * u x := by rw [hx]
  let g : ℝ → ℂ := fun x => -z * u x
  have hgcont : Continuous g := continuous_const.mul hucont
  have hgint : Integrable g (volume : Measure ℝ) := hvint.congr hvu
  have hueq : u = sourceInverse thetaSource g := by
    funext x
    exact sourceInverse_congr_ae thetaSource hvu x
  let m : ℂ := (∫ x, g x) / (thetaSource.mass : ℂ)
  let up : ℝ → ℂ := fun x =>
    Complex.I * (g x - m * (thetaSource.k x : ℂ))
  have huderiv : ∀ x : ℝ, HasDerivAt u (up x) x := by
    intro x
    have h := hasDerivAt_sourceInverse_of_continuous_integrable hgcont hgint x
    rw [← hueq] at h
    simpa only [up, m] using h
  have heq : ∀ x : ℝ,
      -Complex.I * up x + z * u x = -m * (thetaSource.k x : ℂ) := by
    intro x
    have hcancel (A : ℂ) : -Complex.I * (Complex.I * A) = A := by
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      linear_combination (-A) * hI
    dsimp only [up]
    rw [hcancel]
    dsimp only [g]
    ring
  have htilt : Integrable (fun x => u x * sourceChar z x)
      (volume : Measure ℝ) := by
    have hvtilt := integrable_sourceSpace_mul_sourceChar v z
    refine (hvtilt.const_mul eig).congr ?_
    filter_upwards [hsource] with x hx
    rw [hx]
    ring
  have hchar : ∀ x : ℝ, HasDerivAt (sourceChar z)
      (Complex.I * z * sourceChar z x) x := by
    intro x
    have hlin : HasDerivAt (fun t : ℝ => Complex.I * z * ((t : ℝ) : ℂ))
        (Complex.I * z) x := by
      simpa using (hasDerivAt_id x).ofReal_comp.const_mul (Complex.I * z)
    have h := hlin.cexp
    refine h.congr_deriv ?_
    rw [sourceChar]
    ring
  let wp : ℝ → ℂ := fun x =>
    (-m) * Complex.I * ((thetaSource.k x : ℂ) * sourceChar z x)
  have hwderiv : ∀ x : ℝ,
      HasDerivAt (fun t => u t * sourceChar z t) (wp x) x := by
    intro x
    have h := (huderiv x).mul (hchar x)
    refine h.congr_deriv ?_
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have hx := heq x
    dsimp only [wp]
    linear_combination (Complex.I * sourceChar z x) * hx
      + (sourceChar z x * up x) * hI
  have hwp : Integrable wp (volume : Measure ℝ) := by
    exact (integrable_k_sourceChar thetaSource
      (hasShiftedTail_thetaSource_all z)).const_mul ((-m) * Complex.I)
  have hbot : Tendsto (fun x => u x * sourceChar z x) atBot (nhds 0) :=
    MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Iic
      (a := 0) (fun x _ => hwderiv x) hwp.integrableOn htilt.integrableOn
  have htop : Tendsto (fun x => u x * sourceChar z x) atTop (nhds 0) :=
    MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
      (a := 0) (fun x _ => hwderiv x) hwp.integrableOn htilt.integrableOn
  have hm : m ≠ 0 := by
    intro hm0
    have heq0 : ∀ x : ℝ, -Complex.I * up x + z * u x = 0 := by
      intro x
      simpa [hm0] using heq x
    have hzeroDeriv : ∀ x : ℝ,
        HasDerivAt (fun _ : ℝ => (0 : ℂ)) 0 x := fun x => hasDerivAt_const x 0
    have hzeroEq : ∀ x : ℝ,
        -Complex.I * 0 + z * 0 = (0 : ℂ) * (thetaSource.k x : ℂ) := by
      intro x
      ring
    have hdiffBot : Tendsto
        (fun x => (u x - 0) * sourceChar z x) atBot (nhds 0) := by
      simpa using hbot
    have hu0all := HedenmalmPrimeTranslation.eq_of_sourceEquation thetaSource
      huderiv hzeroDeriv
      (fun x => by simpa using heq0 x) hzeroEq hdiffBot
    have hvzeroLeb : (fun x => (v x : ℂ)) =ᵐ[(volume : Measure ℝ)]
        fun _ : ℝ => (0 : ℂ) := by
      filter_upwards [hsource] with x hx
      rw [hu0all x] at hx
      exact (mul_eq_zero.mp hx.symm).resolve_left heig0
    have hvzeroWeighted : (fun x => (v x : ℂ)) =ᵐ[
        (volume : Measure ℝ).withDensity
          (realDensity (sourceWeight thetaSource))] fun _ : ℝ => (0 : ℂ) :=
      (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
        (sourceWeight_pos thetaSource)).mpr hvzeroLeb
    have hv0 : v = 0 := by
      apply Lp.ext
      have hzeroCoe := Lp.coeFn_zero ℂ 2
        ((volume : Measure ℝ).withDensity
          (realDensity (sourceWeight thetaSource)))
      filter_upwards [hvzeroWeighted, hzeroCoe] with x hx h0x
      calc
        v x = 0 := hx
        _ = (0 : SourceSpace thetaSource) x := by simpa using h0x.symm
    apply hf0
    rw [← hvf, hv0, map_zero]
  exact HedenmalmHilbertSchmidt.xiC_eq_zero_of_solution_const thetaSource
    (neg_ne_zero.mpr hm) huderiv heq (hasShiftedTail_thetaSource_all z) hbot htop

/-- Every nonzero reciprocal eigenmode of the fixed compact theta source inverse forces a zero of
the centered completed Riemann Xi function. -/
theorem XiC_eq_zero_of_thetaCompactSourceInverse_eigen
    {z : ℂ} (hz : z ≠ 0) {f : Lp ℂ 2 unitIntervalMeasure}
    (hf0 : f ≠ 0)
    (hf : thetaCompactSourceInverse f = (-z⁻¹) • f) :
    XiC z = 0 := by
  rw [← xiC_thetaSource_all z]
  exact xiC_thetaSource_eq_zero_of_thetaCompactSourceInverse_eigen hz hf0 hf

/-- **Exact divisor theorem for the source determinant.**  The fixed Hilbert--Schmidt determinant
`det₂(I + zB)` vanishes exactly at the centered Xi divisor, with no strip restriction and no
spurious spectral points. -/
theorem thetaSourceEntireDet2_eq_zero_iff_XiC_eq_zero (z : ℂ) :
    thetaSourceEntireDet2 z = 0 ↔ XiC z = 0 := by
  by_cases hz : z = 0
  · subst z
    constructor
    · intro h
      rw [thetaSourceEntireDet2_zero] at h
      exact (one_ne_zero h).elim
    · intro h
      exact (XiC_zero_ne h).elim
  · constructor
    · intro hdet
      obtain ⟨f, hf0, hf⟩ :=
        (thetaSourceEntireDet2_eq_zero_iff_exists_eigenvector hz).mp hdet
      exact XiC_eq_zero_of_thetaCompactSourceInverse_eigen hz hf0
        (by simpa only [thetaKernelOperator_eq_thetaCompactSourceInverse] using hf)
    · intro hXi
      have hstrip : |z.im| < 1 := abs_im_lt_one_of_XiC_eq_zero hXi
      have hsource : xiC thetaSource z = 0 := by
        rw [xiC_thetaSource_all]
        exact hXi
      refine (thetaSourceEntireDet2_eq_zero_iff_exists_eigenvector hz).mpr ?_
      refine ⟨thetaDivisorEigenvector z hstrip hsource,
        thetaDivisorEigenvector_ne_zero z hstrip hsource, ?_⟩
      simpa only [thetaKernelOperator_eq_thetaCompactSourceInverse] using
        thetaCompactSourceInverse_eigen z hstrip hsource

end HedenmalmThetaSource

end

end RHTower
