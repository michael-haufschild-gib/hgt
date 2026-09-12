import GaloisForLFunctions.HTGeometry.SobolevWeightDecay

/-!
# Order-one Fourier decay from an integrable derivative

One integration by parts turns an integrable derivative into decay of the transform: the transform
of `f'` is `2π i ξ` times the transform of `f`, and every transform is bounded by the `L¹` norm of
its input.  So

`‖f̂(ξ)‖ · 2π|ξ| ≤ ‖f'‖₁`   and   `‖f̂(ξ)‖ ≤ ‖f‖₁`,

which are exactly the two hypotheses of the fractional Sobolev criterion.  Combining them puts
every integrable function with integrable derivative in each Sobolev weight below one half — the
threshold, and the reason a bounded-variation profile just misses `H^{1/2}`.
-/

open Real MeasureTheory FourierTransform Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

/-- **Order-one decay.**  The transform of a function with integrable derivative decays like
`1/|ξ|`, with constant the `L¹` norm of the derivative. -/
theorem norm_fourier_mul_le_integral_norm_deriv {f : ℝ → ℂ}
    (hf : Integrable f) (hdiff : Differentiable ℝ f) (hf' : Integrable (deriv f)) (ξ : ℝ) :
    ‖fourier f ξ‖ * (2 * π * |ξ|) ≤ ∫ t, ‖deriv f t‖ := by
  have hkey := congrFun (Real.fourier_deriv hf hdiff hf') ξ
  have hbound : ‖fourier (deriv f) ξ‖ ≤ ∫ t, ‖deriv f t‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  rw [hkey] at hbound
  have hnorm : ‖(2 * (π : ℂ) * Complex.I * (ξ : ℂ)) • fourier f ξ‖ =
      ‖fourier f ξ‖ * (2 * π * |ξ|) := by
    rw [norm_smul]
    have h1 : ‖(2 * (π : ℂ) * Complex.I * (ξ : ℂ))‖ = 2 * π * |ξ| := by
      rw [norm_mul, norm_mul, norm_mul]
      simp [abs_of_nonneg Real.pi_nonneg]
    rw [h1]
    ring
  rw [hnorm] at hbound
  exact hbound

/-- Every transform is bounded by the `L¹` norm of its input. -/
theorem norm_fourierReal_le_integral_norm (f : ℝ → ℂ) (ξ : ℝ) :
    ‖fourier f ξ‖ ≤ ∫ t, ‖f t‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-- **Square-root weighted Fourier decay.** Order-one decay from an integrable derivative is
strictly stronger than the square-root weighted decay required at a fractional Tauberian boundary.
This is the `alpha = 1/2` oscillatory decay step in the Kato--Ikehara argument. -/
theorem tendsto_sqrt_mul_norm_fourier_of_integrable_deriv {f : ℝ → ℂ}
    (hf : Integrable f) (hdiff : Differentiable ℝ f) (hf' : Integrable (deriv f)) :
    Tendsto (fun ξ : ℝ ↦ Real.sqrt ξ * ‖fourier f ξ‖) atTop (nhds 0) := by
  let C : ℝ := ∫ t, ‖deriv f t‖
  have hmajor : Tendsto (fun ξ : ℝ ↦ C / (2 * π * Real.sqrt ξ)) atTop (nhds 0) := by
    have hsqrt : Tendsto (fun ξ : ℝ ↦ Real.sqrt ξ) atTop atTop :=
      Real.tendsto_sqrt_atTop
    have hden : Tendsto (fun ξ : ℝ ↦ 2 * π * Real.sqrt ξ) atTop atTop :=
      hsqrt.const_mul_atTop (by positivity : 0 < 2 * π)
    exact Tendsto.const_div_atTop hden C
  refine squeeze_zero'
    (Eventually.of_forall fun ξ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) ?_ hmajor
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ξ hξ
  have hsqrt : 0 < Real.sqrt ξ := Real.sqrt_pos.2 hξ
  have hpi : 0 < 2 * π := by positivity
  have hdecay := norm_fourier_mul_le_integral_norm_deriv hf hdiff hf' ξ
  dsimp [C]
  calc
    Real.sqrt ξ * ‖fourier f ξ‖ =
        (‖fourier f ξ‖ * (2 * π * |ξ|)) / (2 * π * Real.sqrt ξ) := by
          apply (eq_div_iff (mul_ne_zero hpi.ne' hsqrt.ne')).2
          rw [abs_of_pos hξ]
          calc
            Real.sqrt ξ * ‖fourier f ξ‖ * (2 * π * Real.sqrt ξ) =
                ‖fourier f ξ‖ * (2 * π * Real.sqrt ξ ^ 2) := by ring
            _ = ‖fourier f ξ‖ * (2 * π * ξ) := by rw [Real.sq_sqrt hξ.le]
    _ ≤ (∫ t, ‖deriv f t‖) / (2 * π * Real.sqrt ξ) :=
      div_le_div_of_nonneg_right hdecay (mul_nonneg hpi.le hsqrt.le)

/-! ## Piecewise-smooth cusp decay

Fractional Tauberian boundary remainders have a square-root cusp at the pole.  Their derivative is
integrable on each side but does not exist at the cusp, so the global derivative theorem above is
not applicable.  Splitting the interval at the cusp gives the same order-one Fourier decay; the
finite endpoint terms are harmless.
-/

/-- **Order-one decay on a finite interval.**  Only interior differentiability is required; the
function need merely be continuous at the endpoints. -/
theorem norm_intervalIntegral_exp_mul_le_ibp {a b : ℝ} (hab : a ≤ b)
    {w w' : ℝ → ℂ} {z : ℝ} (hz : z ≠ 0)
    (hw : ContinuousOn w (uIcc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt w (w' x) x)
    (hw' : IntervalIntegrable w' volume a b) :
    ‖∫ x in a..b, w x * Complex.exp (((z * x : ℝ) : ℂ) * Complex.I)‖
      ≤ (‖w b‖ + ‖w a‖ + ∫ x in a..b, ‖w' x‖) / |z| := by
  have hzC : ((z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
  set V : ℝ → ℂ := fun t => Complex.exp (((z : ℂ) * t) * Complex.I) /
    (((z : ℝ) : ℂ) * Complex.I) with hV
  have hVcont : ContinuousOn V (uIcc a b) := by
    apply Continuous.continuousOn
    fun_prop
  have hVderiv : ∀ x ∈ Ioo a b,
      HasDerivAt V (Complex.exp (((z * x : ℝ) : ℂ) * Complex.I)) x := by
    intro x _
    have hlin : HasDerivAt (fun t : ℝ => ((z : ℂ) * t) * Complex.I)
        ((z : ℂ) * Complex.I) x := by
      have hbase : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x :=
        Complex.ofRealCLM.hasDerivAt.congr_deriv (by simp)
      simpa using ((hbase.const_mul (z : ℂ)).mul_const Complex.I)
    have hexp : HasDerivAt (fun t : ℝ => Complex.exp (((z : ℂ) * t) * Complex.I))
        (Complex.exp (((z : ℂ) * x) * Complex.I) * ((z : ℂ) * Complex.I)) x := hlin.cexp
    have hdiv := hexp.div_const (((z : ℝ) : ℂ) * Complex.I)
    have hval : Complex.exp (((z : ℂ) * x) * Complex.I) * ((z : ℂ) * Complex.I) /
        (((z : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((z * x : ℝ) : ℂ) * Complex.I) := by
      rw [mul_div_assoc, div_self (mul_ne_zero hzC Complex.I_ne_zero), mul_one]
      push_cast
      ring_nf
    rwa [hval] at hdiv
  have hVnorm : ∀ x : ℝ, ‖V x‖ = 1 / |z| := by
    intro x
    rw [hV]
    simp only [norm_div, norm_mul]
    rw [show ((z : ℂ) * x) = (((z * x : ℝ) : ℂ)) from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      mul_one]
  have hexpInt : IntervalIntegrable (fun x : ℝ =>
      Complex.exp (((z * x : ℝ) : ℂ) * Complex.I)) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hderiv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt w (w' x) x := by
    simpa [min_eq_left hab, max_eq_right hab] using hderiv
  have hVderiv' : ∀ x ∈ Ioo (min a b) (max a b),
      HasDerivAt V (Complex.exp (((z * x : ℝ) : ℂ) * Complex.I)) x := by
    simpa [min_eq_left hab, max_eq_right hab] using hVderiv
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hw hVcont hderiv'
    hVderiv' hw' hexpInt]
  have hbound : ‖w b * V b - w a * V a - ∫ x in a..b, w' x * V x‖
      ≤ ‖w b‖ * (1 / |z|) + ‖w a‖ * (1 / |z|)
        + (∫ x in a..b, ‖w' x‖) * (1 / |z|) := by
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖w b * V b - w a * V a‖ ≤
        ‖w b‖ * (1 / |z|) + ‖w a‖ * (1 / |z|) := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul, hVnorm, hVnorm]
    have h2 : ‖∫ x in a..b, w' x * V x‖ ≤
        (∫ x in a..b, ‖w' x‖) * (1 / |z|) := by
      refine (intervalIntegral.norm_integral_le_abs_integral_norm).trans ?_
      have hcongr : (∫ x in a..b, ‖w' x * V x‖) =
          ∫ x in a..b, ‖w' x‖ * (1 / |z|) := by
        refine intervalIntegral.integral_congr ?_
        intro x _
        dsimp only
        rw [norm_mul, hVnorm]
      rw [hcongr, intervalIntegral.integral_mul_const, abs_of_nonneg]
      have hnn : 0 ≤ ∫ x in a..b, ‖w' x‖ :=
        intervalIntegral.integral_nonneg hab fun _ _ => norm_nonneg _
      positivity
    linarith
  refine hbound.trans ?_
  rw [div_eq_mul_one_div]
  ring_nf
  exact le_of_eq rfl

/-- **Order-one decay across one cusp.**  Split at `c`; no derivative is required there. -/
theorem norm_intervalIntegral_exp_mul_le_piecewise_ibp {a c b : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) {w wLeft' wRight' : ℝ → ℂ} {z : ℝ} (hz : z ≠ 0)
    (hwLeft : ContinuousOn w (uIcc a c)) (hwRight : ContinuousOn w (uIcc c b))
    (hderivLeft : ∀ x ∈ Ioo a c, HasDerivAt w (wLeft' x) x)
    (hderivRight : ∀ x ∈ Ioo c b, HasDerivAt w (wRight' x) x)
    (hwLeft' : IntervalIntegrable wLeft' volume a c)
    (hwRight' : IntervalIntegrable wRight' volume c b) :
    ‖∫ x in a..b, w x * Complex.exp (((z * x : ℝ) : ℂ) * Complex.I)‖ ≤
      (‖w b‖ + 2 * ‖w c‖ + ‖w a‖ + (∫ x in a..c, ‖wLeft' x‖) +
        (∫ x in c..b, ‖wRight' x‖)) / |z| := by
  have hexp : Continuous (fun x : ℝ => Complex.exp (((z * x : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  have hIntLeft : IntervalIntegrable
      (fun x : ℝ => w x * Complex.exp (((z * x : ℝ) : ℂ) * Complex.I)) volume a c :=
    (hwLeft.mul hexp.continuousOn).intervalIntegrable
  have hIntRight : IntervalIntegrable
      (fun x : ℝ => w x * Complex.exp (((z * x : ℝ) : ℂ) * Complex.I)) volume c b :=
    (hwRight.mul hexp.continuousOn).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals hIntLeft hIntRight]
  calc
    ‖(∫ x in a..c, w x * Complex.exp (((z * x : ℝ) : ℂ) * Complex.I)) +
        ∫ x in c..b, w x * Complex.exp (((z * x : ℝ) : ℂ) * Complex.I)‖ ≤
        ‖∫ x in a..c, w x * Complex.exp (((z * x : ℝ) : ℂ) * Complex.I)‖ +
          ‖∫ x in c..b, w x * Complex.exp (((z * x : ℝ) : ℂ) * Complex.I)‖ :=
      norm_add_le _ _
    _ ≤ (‖w c‖ + ‖w a‖ + ∫ x in a..c, ‖wLeft' x‖) / |z| +
        (‖w b‖ + ‖w c‖ + ∫ x in c..b, ‖wRight' x‖) / |z| :=
      add_le_add
        (norm_intervalIntegral_exp_mul_le_ibp hac hz hwLeft hderivLeft hwLeft')
        (norm_intervalIntegral_exp_mul_le_ibp hcb hz hwRight hderivRight hwRight')
    _ = (‖w b‖ + 2 * ‖w c‖ + ‖w a‖ + (∫ x in a..c, ‖wLeft' x‖) +
        (∫ x in c..b, ‖wRight' x‖)) / |z| := by ring

/-- A continuous one-cusp profile with integrable derivatives on both sides has the
square-root-weighted Fourier decay used at a fractional Tauberian boundary. -/
theorem tendsto_sqrt_mul_norm_intervalIntegral_exp_mul_of_piecewise_ibp {a c b : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) {w wLeft' wRight' : ℝ → ℂ}
    (hwLeft : ContinuousOn w (uIcc a c)) (hwRight : ContinuousOn w (uIcc c b))
    (hderivLeft : ∀ x ∈ Ioo a c, HasDerivAt w (wLeft' x) x)
    (hderivRight : ∀ x ∈ Ioo c b, HasDerivAt w (wRight' x) x)
    (hwLeft' : IntervalIntegrable wLeft' volume a c)
    (hwRight' : IntervalIntegrable wRight' volume c b) :
    Tendsto (fun z : ℝ => Real.sqrt z *
      ‖∫ x in a..b, w x * Complex.exp (((z * x : ℝ) : ℂ) * Complex.I)‖)
      atTop (nhds 0) := by
  let C : ℝ := ‖w b‖ + 2 * ‖w c‖ + ‖w a‖ + (∫ x in a..c, ‖wLeft' x‖) +
    (∫ x in c..b, ‖wRight' x‖)
  have hmajor : Tendsto (fun z : ℝ => C / Real.sqrt z) atTop (nhds 0) := by
    exact Tendsto.const_div_atTop Real.tendsto_sqrt_atTop C
  refine squeeze_zero'
    (Eventually.of_forall fun z => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) ?_ hmajor
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
  have hsqrt : 0 < Real.sqrt z := Real.sqrt_pos.2 hz
  have hdecay := norm_intervalIntegral_exp_mul_le_piecewise_ibp hac hcb hz.ne' hwLeft
    hwRight hderivLeft hderivRight hwLeft' hwRight' (z := z)
  change Real.sqrt z *
      ‖∫ x in a..b, w x * Complex.exp (((z * x : ℝ) : ℂ) * Complex.I)‖ ≤
    C / Real.sqrt z
  calc
    Real.sqrt z *
        ‖∫ x in a..b, w x * Complex.exp (((z * x : ℝ) : ℂ) * Complex.I)‖ ≤
        Real.sqrt z * (C / |z|) := mul_le_mul_of_nonneg_left hdecay (Real.sqrt_nonneg _)
    _ = C / Real.sqrt z := by
      rw [abs_of_pos hz]
      field_simp
      rw [Real.sq_sqrt hz.le]
      ring

private theorem aestronglyMeasurable_verticalCpow (q : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => ((t : ℂ) * Complex.I) ^ q) := by
  apply Measurable.aestronglyMeasurable
  apply measurable_of_continuousOn_compl_singleton (0 : ℝ)
  apply continuousOn_of_forall_continuousAt
  intro t ht
  refine (continuousAt_cpow_const ?_).comp ?_
  · rw [Complex.mem_slitPlane_iff]
    right
    simpa using ht
  · fun_prop

/-- The inverse square-root singularity on a vertical complex ray is locally integrable. -/
theorem intervalIntegrable_verticalCpow_negHalf (a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => ((t : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))) volume a b := by
  rw [← IntervalIntegrable.intervalIntegrable_norm_iff
    (aestronglyMeasurable_verticalCpow (-(1 / 2 : ℂ))).restrict]
  have h := (intervalIntegral.intervalIntegrable_cpow'
    (a := a) (b := b) (r := (-(1 / 2 : ℂ))) (by norm_num)).norm
  refine h.congr fun t _ => ?_
  symm
  change ‖((t : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))‖ =
    ‖(t : ℂ) ^ (-(1 / 2 : ℂ))‖
  rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_real, Complex.norm_cpow_real]
  simp

/-- Square-root cusp on a vertical ray, multiplied by a regular complex factor. -/
noncomputable def verticalCpowCusp (H : ℂ → ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) * Complex.I) ^ (1 / 2 : ℂ) * H (1 + (t : ℂ) * Complex.I)

private noncomputable def verticalCpowCuspDeriv (H : ℂ → ℂ) (t : ℝ) : ℂ :=
  ((1 / 2 : ℂ) * ((t : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) * Complex.I) *
      H (1 + (t : ℂ) * Complex.I) +
    ((t : ℂ) * Complex.I) ^ (1 / 2 : ℂ) *
      (deriv H (1 + (t : ℂ) * Complex.I) * Complex.I)

private theorem verticalCpowCusp_hasDerivAt {H : ℂ → ℂ} {t : ℝ} (ht : t ≠ 0)
    (hH : DifferentiableAt ℂ H (1 + (t : ℂ) * Complex.I)) :
    HasDerivAt (verticalCpowCusp H) (verticalCpowCuspDeriv H t) t := by
  have hslit : (t : ℂ) * Complex.I ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    simpa using ht
  have hline : HasDerivAt (fun z : ℂ => z * Complex.I) Complex.I (t : ℂ) := by
    simpa using (hasDerivAt_id (t : ℂ)).mul_const Complex.I
  have hpow := hline.cpow_const (c := (1 / 2 : ℂ)) hslit
  have harg : HasDerivAt (fun z : ℂ => 1 + z * Complex.I) Complex.I (t : ℂ) := by
    exact hline.const_add (1 : ℂ)
  have hHline := hH.hasDerivAt.comp (t : ℂ) harg
  have hprod := hpow.mul hHline
  convert! hprod.comp_ofReal using 1
  simp only [verticalCpowCuspDeriv, Function.comp_apply]
  rw [show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by ring]

private theorem continuous_verticalCpowHalf :
    Continuous (fun t : ℝ => ((t : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro t
  refine (Complex.continuousAt_cpow_const_of_re_pos ?_ (by norm_num)).comp ?_
  · left
    simp
  · fun_prop

/-- An analytic factor times a vertical square-root cusp has the local Fourier decay required at a
fractional Tauberian boundary. -/
theorem tendsto_sqrt_mul_norm_intervalIntegral_verticalCpowCusp {δ : ℝ} (hδ : 0 < δ)
    {H : ℂ → ℂ}
    (hHcont : ContinuousOn (fun t : ℝ => H (1 + (t : ℂ) * Complex.I)) (uIcc (-δ) δ))
    (hHdcont : ContinuousOn
      (fun t : ℝ => deriv H (1 + (t : ℂ) * Complex.I)) (uIcc (-δ) δ))
    (hHdiff : ∀ t ∈ uIcc (-δ) δ, t ≠ 0 →
      DifferentiableAt ℂ H (1 + (t : ℂ) * Complex.I)) :
    Tendsto (fun z : ℝ => Real.sqrt z *
      ‖∫ t in (-δ)..δ, verticalCpowCusp H t *
        Complex.exp (((z * t : ℝ) : ℂ) * Complex.I)‖) atTop (nhds 0) := by
  have hpowCont : ContinuousOn
      (fun t : ℝ => ((t : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) (uIcc (-δ) δ) :=
    continuous_verticalCpowHalf.continuousOn
  have hwCont : ContinuousOn (verticalCpowCusp H) (uIcc (-δ) δ) := by
    exact hpowCont.mul hHcont
  have hsing := intervalIntegrable_verticalCpow_negHalf (-δ) δ
  have hsingH : IntervalIntegrable
      (fun t : ℝ => ((t : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
        H (1 + (t : ℂ) * Complex.I)) volume (-δ) δ :=
    hsing.mul_continuousOn hHcont
  have hfirst : IntervalIntegrable
      (fun t : ℝ => ((1 / 2 : ℂ) *
        ((t : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) * Complex.I) *
        H (1 + (t : ℂ) * Complex.I)) volume (-δ) δ := by
    have h := hsingH.const_mul ((1 / 2 : ℂ) * Complex.I)
    convert h using 1
    funext t
    ring
  have hsecondCont : ContinuousOn
      (fun t : ℝ => ((t : ℂ) * Complex.I) ^ (1 / 2 : ℂ) *
        (deriv H (1 + (t : ℂ) * Complex.I) * Complex.I)) (uIcc (-δ) δ) := by
    exact hpowCont.mul (hHdcont.mul continuousOn_const)
  have hDint : IntervalIntegrable (verticalCpowCuspDeriv H) volume (-δ) δ := by
    exact hfirst.add hsecondCont.intervalIntegrable
  have hleftSub : uIcc (-δ) 0 ⊆ uIcc (-δ) δ := by
    rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
    intro t ht
    exact ⟨ht.1, ht.2.trans hδ.le⟩
  have hrightSub : uIcc 0 δ ⊆ uIcc (-δ) δ := by
    rw [uIcc_of_le hδ.le, uIcc_of_le (by linarith)]
    intro t ht
    exact ⟨(neg_nonpos.mpr hδ.le).trans ht.1, ht.2⟩
  apply tendsto_sqrt_mul_norm_intervalIntegral_exp_mul_of_piecewise_ibp
      (a := -δ) (c := 0) (b := δ) (w := verticalCpowCusp H)
      (wLeft' := verticalCpowCuspDeriv H) (wRight' := verticalCpowCuspDeriv H)
      (by linarith) hδ.le
  · exact hwCont.mono hleftSub
  · exact hwCont.mono hrightSub
  · intro t ht
    apply verticalCpowCusp_hasDerivAt ht.2.ne
    apply hHdiff t
    · rw [uIcc_of_le (by linarith)]
      exact ⟨ht.1.le, ht.2.le.trans hδ.le⟩
    · exact ht.2.ne
  · intro t ht
    apply verticalCpowCusp_hasDerivAt ht.1.ne'
    apply hHdiff t
    · rw [uIcc_of_le (by linarith)]
      exact ⟨(neg_nonpos.mpr hδ.le).trans ht.1.le, ht.2.le⟩
    · exact ht.1.ne'
  · exact hDint.mono hleftSub le_rfl
  · exact hDint.mono hrightSub le_rfl

/-- **Fractional Sobolev membership from an integrable derivative.**  An integrable function whose
derivative is integrable lies in every Sobolev weight strictly below one half.  The exponent is
sharp for this hypothesis: order-one decay is exactly the borderline. -/
theorem memSobolevWeight_of_integrable_deriv {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1 / 2)
    {f : ℝ → ℂ} (hf : Integrable f) (hdiff : Differentiable ℝ f) (hf' : Integrable (deriv f)) :
    MemSobolevWeight s (fourier f) := by
  have hM : (0 : ℝ) ≤ ∫ t, ‖f t‖ := integral_nonneg fun _ => norm_nonneg _
  have hK : (0 : ℝ) ≤ (∫ t, ‖deriv f t‖) / (2 * π) := by
    have hpi : (0 : ℝ) < 2 * π := by positivity
    exact div_nonneg (integral_nonneg fun _ => norm_nonneg _) hpi.le
  refine memSobolevWeight_of_decay hs0 hs hM hK ?_ (fun ξ => norm_fourierReal_le_integral_norm f ξ) ?_
  · exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop) hf).aestronglyMeasurable
  · intro ξ hξ
    have hpi : (0 : ℝ) < 2 * π := by positivity
    have hmain := norm_fourier_mul_le_integral_norm_deriv hf hdiff hf' ξ
    rw [le_div_iff₀ hpi]
    calc ‖fourier f ξ‖ * |ξ| * (2 * π) = ‖fourier f ξ‖ * (2 * π * |ξ|) := by ring
      _ ≤ ∫ t, ‖deriv f t‖ := hmain

/-! ## Half-period translation -/

/-- **Half-period translation flips the transform.**  At frequency `ξ` the shift by `1/(2ξ)`
multiplies the transform by `fourierChar (1/2) = e^{iπ} = -1`.  This is the step that gives
order-one decay from an `L¹` modulus of continuity alone, with no differentiability and no bounded
variation. -/
theorem fourier_translate_half (f : ℝ → ℂ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    fourier (fun x => f (x + 1 / (2 * ξ))) ξ = -fourier f ξ := by
  have hval := congrFun (VectorFourier.fourierIntegral_comp_add_right (E := ℂ) Real.fourierChar
    (volume : Measure ℝ) (innerₗ ℝ) f (1 / (2 * ξ))) ξ
  have hin : ((innerₗ ℝ) (1 / (2 * ξ)) ξ : ℝ) = 1 / 2 := by
    simp only [innerₗ]
    simp [innerₛₗ, mul_comm]
    field_simp
  rw [hin] at hval
  have hph : ((Real.fourierChar ((1 : ℝ) / 2) : Circle) : ℂ) = -1 := by
    rw [Real.fourierChar_apply, show (2 * π * (1 / 2) : ℝ) = π by ring]
    exact Complex.exp_pi_mul_I
  have hgoal : fourier (fun x => f (x + 1 / (2 * ξ))) ξ
      = (Real.fourierChar ((1 : ℝ) / 2) : Circle) • fourier f ξ := hval
  rw [hgoal, Circle.smul_def, hph]
  ring

/-- **Decay from the `L¹` modulus of continuity.**  Twice the transform is the transform of the
half-period difference, so it is bounded by that difference's `L¹` norm.  This needs neither
differentiability nor bounded variation. -/
theorem two_mul_norm_fourier_le_translationDistance (f : ℝ → ℂ) (hf : Integrable f) {ξ : ℝ}
    (hξ : ξ ≠ 0) :
    2 * ‖fourier f ξ‖ ≤ ∫ x, ‖f x - f (x + 1 / (2 * ξ))‖ := by
  have htr := fourier_translate_half f hξ
  set h : ℝ := 1/(2*ξ) with hh
  have hft : Integrable (fun x => f (x + h)) := hf.comp_add_right h
  have hneg : Integrable (fun x => -f (x + h)) := hft.neg
  have hadd := congrFun (VectorFourier.fourierIntegral_add (E := ℂ) (e := Real.fourierChar)
    (μ := (volume : Measure ℝ)) (L := innerₗ ℝ) Real.continuous_fourierChar (by fun_prop)
    hf hneg) ξ
  have hnegf : fourier (fun x => -f (x + h)) ξ = -fourier (fun x => f (x + h)) ξ := by
    have := congrFun (VectorFourier.fourierIntegral_const_smul (E := ℂ) Real.fourierChar
      (volume : Measure ℝ) (innerₗ ℝ) (fun x => f (x + h)) (-1 : ℂ)) ξ
    have hs : ((-1 : ℂ) • (fun x => f (x + h))) = (fun x => -f (x + h)) := by
      funext x; simp
    rw [hs] at this
    simp only [Pi.smul_apply, neg_smul, one_smul] at this
    exact this
  have hsub : fourier (fun x => f x - f (x + h)) ξ = 2 * fourier f ξ := by
    have hrw : (fun x => f x - f (x + h)) = (fun x => f x + -f (x + h)) := by
      funext x; ring
    rw [hrw]
    have h2 : fourier (fun x => f x + -f (x + h)) ξ
        = fourier f ξ + fourier (fun x => -f (x + h)) ξ := hadd
    rw [h2, hnegf, htr]
    ring
  have hbd : ‖fourier (fun x => f x - f (x + h)) ξ‖ ≤ ∫ x, ‖f x - f (x + h)‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  rw [hsub] at hbd
  simpa using hbd

/-! ## The symbol of the difference operator

Translating multiplies the transform by a character, so the first difference has Fourier symbol
`1 − e^{2πihξ}`.  Subtraction must be routed through `fourierIntegral_add` together with
`fourierIntegral_const_smul` at `-1`: this toolchain has no `fourierIntegral_sub`.
-/

/-- The transform of a translate is the character times the transform. -/
theorem fourier_translate (f : ℝ → ℂ) (h ξ : ℝ) :
    fourier (fun x => f (x + h)) ξ
      = ((Real.fourierChar (h * ξ) : Circle) : ℂ) * fourier f ξ := by
  have hval := congrFun (VectorFourier.fourierIntegral_comp_add_right (E := ℂ) Real.fourierChar
    (volume : Measure ℝ) (innerₗ ℝ) f h) ξ
  have hin : ((innerₗ ℝ) h ξ : ℝ) = h * ξ := by
    simp only [innerₗ]
    simp [innerₛₗ, mul_comm]
  rw [hin] at hval
  have hgoal : fourier (fun x => f (x + h)) ξ
      = (Real.fourierChar (h * ξ) : Circle) • fourier f ξ := hval
  rw [hgoal, Circle.smul_def, smul_eq_mul]

/-- **The symbol of the first difference.**  The transform of `f − f(·+h)` is `(1 − e^{2πihξ})`
times the transform of `f`. -/
theorem fourier_sub_translate (f : ℝ → ℂ) (hf : Integrable f) (h ξ : ℝ) :
    fourier (fun x => f x - f (x + h)) ξ
      = (1 - ((Real.fourierChar (h * ξ) : Circle) : ℂ)) * fourier f ξ := by
  have hft : Integrable (fun x => f (x + h)) := hf.comp_add_right h
  have hneg : Integrable (fun x => -f (x + h)) := hft.neg
  have hadd := congrFun (VectorFourier.fourierIntegral_add (E := ℂ) (e := Real.fourierChar)
    (μ := (volume : Measure ℝ)) (L := innerₗ ℝ) Real.continuous_fourierChar (by fun_prop)
    hf hneg) ξ
  have hnegf : fourier (fun x => -f (x + h)) ξ = -fourier (fun x => f (x + h)) ξ := by
    have hsm := congrFun (VectorFourier.fourierIntegral_const_smul (E := ℂ) Real.fourierChar
      (volume : Measure ℝ) (innerₗ ℝ) (fun x => f (x + h)) (-1 : ℂ)) ξ
    have hs : ((-1 : ℂ) • (fun x => f (x + h))) = (fun x => -f (x + h)) := by
      funext x; simp
    rw [hs] at hsm
    simp only [Pi.smul_apply, neg_smul, one_smul] at hsm
    exact hsm
  have hrw : (fun x => f x - f (x + h)) = (fun x => f x + -f (x + h)) := by
    funext x; ring
  rw [hrw]
  have h2 : fourier (fun x => f x + -f (x + h)) ξ
      = fourier f ξ + fourier (fun x => -f (x + h)) ξ := hadd
  rw [h2, hnegf, fourier_translate f h ξ]
  ring

end GaloisForLFunctions.HTGeometry
