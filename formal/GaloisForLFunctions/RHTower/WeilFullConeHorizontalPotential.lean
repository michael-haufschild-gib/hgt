import GaloisForLFunctions.RHTower.WeilConeSingularDeficitEnvelope

/-!
# Horizontal integrals of a Weil-positive system: the potential identity

Let `lam` be full-cone Weil-positive with boundary measure `μ_lam` and Herglotz continuation
`Φ_lam` (`weilContinuation`) on `Re s > 1/2`.  For `1/2 < a ≤ b` and every height `t`,

`∫_a^b Re Φ_lam(u + it) du = ½ ∫ log(((b − ½)² + (r − t)²) / ((a − ½)² + (r − t)²)) dμ_lam(r)`

(`integral_re_weilContinuation_eq`).  Since `Φ_lam = A + 1/(s−1) − D_lam` and
`d/du log|F(u + it)| = −Re D_lam(u + it)` for the system's zeta function `F`, this is the exact
modulus law of `F` between two vertical lines.  It isolates the measure-dependent
damping factor `exp(−½∫log((η'² + x²)/(η² + x²)) dμ_lam)`, whose precision governs mean
values of `F` near the critical line.

**Proof.**  `Re Φ_lam(u + it) = (u − ½)∫ dμ_lam(r)/((u − ½)² + (r − t)²)` (Poisson representation).
Tonelli exchanges the `u`- and `r`-integrals, and
`∫_a^b (u − ½)/((u − ½)² + x²) du = ½ log(((b−½)² + x²)/((a−½)² + x²))`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real NNReal ENNReal

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz

theorem re_weilContinuation_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    (weilContinuation hW s).re =
      (s.re - 1 / 2) * (∫⁻ r, poissonDensity (s - 1 / 2) r ∂boundaryMeasure hW).toReal := by
  have h2 : (weilFunction lam 2 - herglotzFunction hW (2 - 1 / 2)).re = 0 := by
    rw [Complex.sub_re, re_herglotzFunction_eq hW (by norm_num)]
    ring
  unfold weilContinuation
  rw [Complex.add_re, h2, add_zero, re_herglotzFunction hW (by norm_num; linarith)]
  simp

theorem lintegral_poissonDensity_lt_top {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {w : ℂ}
    (hw : 0 < w.re) : (∫⁻ r, poissonDensity w r ∂boundaryMeasure hW) < ⊤ := by
  have hfin := (integrable_herglotzKernel hW hw).re.lintegral_lt_top
  have hpt : ∀ r, poissonDensity w r =
      ENNReal.ofReal (1 / w.re) * ENNReal.ofReal (herglotzKernel w r).re := by
    intro r
    rw [re_herglotzKernel hw, ← ENNReal.ofReal_mul (by positivity), ← mul_assoc,
      one_div_mul_cancel hw.ne', one_mul]
    unfold poissonDensity
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_pow, coe_nnnorm]
  rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- The Poisson representation in `ℝ≥0∞` form, on every line `Re s > 1/2`. -/
theorem ofReal_re_weilContinuation_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (u t : ℝ)
    (hu : 1 / 2 < u) :
    ENNReal.ofReal (weilContinuation hW ((u : ℂ) + t * I)).re =
      ∫⁻ r, ENNReal.ofReal ((u - 1 / 2) / ((u - 1 / 2) ^ 2 + (r - t) ^ 2))
        ∂boundaryMeasure hW := by
  have hs : 1 / 2 < ((u : ℂ) + t * I).re := by simpa using hu
  have hw : 0 < ((u : ℂ) + t * I - 1 / 2).re := by simp; linarith
  rw [re_weilContinuation_eq hW hs, ENNReal.ofReal_mul (by simp; linarith),
    ENNReal.ofReal_toReal (lintegral_poissonDensity_lt_top hW hw).ne,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun r => ?_
  rw [← ENNReal.ofReal_toReal (poissonDensity_ne_top _ r), poissonDensity_toReal,
    ← ENNReal.ofReal_mul (by simp; linarith)]
  congr 1
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.sub_re, Complex.add_im, Complex.mul_im, Complex.sub_im]
  norm_num
  ring

/-- `∫_a^b (u − ½)/((u − ½)² + x²) du = ½ log(((b−½)² + x²)/((a−½)² + x²))`. -/
theorem integral_poisson_abscissa {a b : ℝ} (ha : 1 / 2 < a) (hab : a ≤ b) (x : ℝ) :
    ∫ u in a..b, (u - 1 / 2) / ((u - 1 / 2) ^ 2 + x ^ 2) =
      Real.log (((b - 1 / 2) ^ 2 + x ^ 2) / ((a - 1 / 2) ^ 2 + x ^ 2)) / 2 := by
  have hpos : ∀ u ∈ uIcc a b, 0 < (u - 1 / 2) ^ 2 + x ^ 2 := by
    intro u hu
    rw [uIcc_of_le hab] at hu
    have : 0 < u - 1 / 2 := by linarith [hu.1]
    positivity
  have hderiv : ∀ u ∈ uIcc a b, HasDerivAt (fun u => Real.log ((u - 1 / 2) ^ 2 + x ^ 2) / 2)
      ((u - 1 / 2) / ((u - 1 / 2) ^ 2 + x ^ 2)) u := by
    intro u hu
    have hne := (hpos u hu).ne'
    have h := (((((hasDerivAt_id' u).sub_const (1 / 2)).pow 2).add_const (x ^ 2)).log
      hne).div_const 2
    refine h.congr_deriv ?_
    simp only [Pi.pow_apply]
    field_simp
    ring
  have hcont : ContinuousOn (fun u => (u - 1 / 2) / ((u - 1 / 2) ^ 2 + x ^ 2)) (uIcc a b) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun u hu => (hpos u hu).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable),
    Real.log_div (hpos b right_mem_uIcc).ne' (hpos a left_mem_uIcc).ne']
  ring

theorem sFinite_boundaryMeasure {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    SFinite (boundaryMeasure hW) := by
  haveI : ∀ j, IsFiniteMeasure (mollifierMeasure hW j) := fun j =>
    isFiniteMeasure_mollifierMeasure hW j
  unfold boundaryMeasure
  infer_instance

/-- **The horizontal potential identity (`ℝ≥0∞` form).** -/
theorem lintegral_re_weilContinuation_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {a b : ℝ}
    (ha : 1 / 2 < a) (hab : a ≤ b) (t : ℝ) :
    ∫⁻ u in Ioc a b, ENNReal.ofReal (weilContinuation hW ((u : ℂ) + t * I)).re =
      ∫⁻ r, ENNReal.ofReal (Real.log (((b - 1 / 2) ^ 2 + (r - t) ^ 2) /
        ((a - 1 / 2) ^ 2 + (r - t) ^ 2)) / 2) ∂boundaryMeasure hW := by
  haveI := sFinite_boundaryMeasure hW
  set f : ℝ → ℝ → ℝ≥0∞ := fun u r =>
    ENNReal.ofReal ((u - 1 / 2) / ((u - 1 / 2) ^ 2 + (r - t) ^ 2)) with hf
  rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun u => ∫⁻ r, f u r ∂boundaryMeasure hW)
    fun u hu => ofReal_re_weilContinuation_eq hW u t (by linarith [hu.1])]
  have hmeas : AEMeasurable (Function.uncurry f) ((volume.restrict (Ioc a b)).prod (boundaryMeasure hW)) := by
    refine Measurable.aemeasurable ?_
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [lintegral_lintegral_swap hmeas]
  refine lintegral_congr fun r => ?_
  have hint : IntegrableOn (fun u => (u - 1 / 2) / ((u - 1 / 2) ^ 2 + (r - t) ^ 2)) (Ioc a b) := by
    have hc : ContinuousOn (fun u => (u - 1 / 2) / ((u - 1 / 2) ^ 2 + (r - t) ^ 2)) (Icc a b) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) fun u hu => by
        have : 0 < u - 1 / 2 := by linarith [hu.1]
        positivity
    exact (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu => by
      have : 0 < u - 1 / 2 := by linarith [hu.1]
      positivity)),
    ← intervalIntegral.integral_of_le hab, integral_poisson_abscissa ha hab]

/-- **The horizontal potential identity.**  For `1/2 < a ≤ b` and every height `t`,
`∫_a^b Re Φ_lam(u + it) du = ½ ∫ log(((b−½)² + (r−t)²)/((a−½)² + (r−t)²)) dμ_lam(r)`. -/
theorem integral_re_weilContinuation_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {a b : ℝ}
    (ha : 1 / 2 < a) (hab : a ≤ b) (t : ℝ) :
    ∫ u in a..b, (weilContinuation hW ((u : ℂ) + t * I)).re =
      ∫ r, Real.log (((b - 1 / 2) ^ 2 + (r - t) ^ 2) / ((a - 1 / 2) ^ 2 + (r - t) ^ 2)) / 2
        ∂boundaryMeasure hW := by
  have hnn : ∀ u ∈ Ioc a b, 0 ≤ (weilContinuation hW ((u : ℂ) + t * I)).re := fun u hu =>
    re_weilContinuation_nonneg hW (by simp; linarith [hu.1])
  have hlog_nn : ∀ r : ℝ, 0 ≤ Real.log (((b - 1 / 2) ^ 2 + (r - t) ^ 2) /
      ((a - 1 / 2) ^ 2 + (r - t) ^ 2)) / 2 := by
    intro r
    have h0 : 0 < (a - 1 / 2) ^ 2 + (r - t) ^ 2 := by
      have : 0 < a - 1 / 2 := by linarith
      positivity
    have h1 : (a - 1 / 2) ^ 2 ≤ (b - 1 / 2) ^ 2 := by nlinarith
    have : 1 ≤ ((b - 1 / 2) ^ 2 + (r - t) ^ 2) / ((a - 1 / 2) ^ 2 + (r - t) ^ 2) := by
      rw [le_div_iff₀ h0]; linarith
    have := Real.log_nonneg this
    linarith
  have hcont : ContinuousOn (fun u : ℝ => (weilContinuation hW ((u : ℂ) + t * I)).re) (Icc a b) := by
    refine Complex.continuous_re.comp_continuousOn ?_
    refine (differentiableOn_weilContinuation hW).continuousOn.comp (by fun_prop) fun u hu => ?_
    show 1 / 2 < ((u : ℂ) + t * I).re
    simp
    linarith [hu.1]
  have hmeas : Measurable fun r : ℝ => Real.log (((b - 1 / 2) ^ 2 + (r - t) ^ 2) /
      ((a - 1 / 2) ^ 2 + (r - t) ^ 2)) / 2 := by fun_prop
  rw [intervalIntegral.integral_of_le hab, integral_eq_lintegral_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hnn))
    ((hcont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc),
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hlog_nn)
    hmeas.aestronglyMeasurable, lintegral_re_weilContinuation_eq hW ha hab t]

/-- **The modulus law of a producer's zeta function.**  Let `g` be a holomorphic logarithm of the
zeta function `F` of a full-cone producer near the horizontal segment `[σ, σ'] + it`, i.e.
`g' = −(A − Φ_lam + 1/(s−1))` there, with `A` ζ's archimedean datum.  Then
`log|F(σ'+it)| − log|F(σ+it)| = −∫_σ^{σ'} Re(A + 1/(s−1)) du
  + ½∫ log(((σ'−½)² + (r−t)²)/((σ−½)² + (r−t)²)) dμ_lam(r)`. -/
theorem re_logZeta_sub_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {g : ℂ → ℂ} {σ σ' t : ℝ}
    (hσ : 1 / 2 < σ) (hσσ' : σ ≤ σ')
    (hg : ∀ u ∈ Icc σ σ', HasDerivAt g
      (-(zetaArchimedeanDatum ((u : ℂ) + t * I) - weilContinuation hW ((u : ℂ) + t * I) +
        1 / ((u : ℂ) + t * I - 1))) ((u : ℂ) + t * I))
    (hcont : ContinuousOn (fun u : ℝ => (zetaArchimedeanDatum ((u : ℂ) + t * I) +
      1 / ((u : ℂ) + t * I - 1)).re) (Icc σ σ')) :
    (g ((σ' : ℂ) + t * I)).re - (g ((σ : ℂ) + t * I)).re =
      -(∫ u in σ..σ', (zetaArchimedeanDatum ((u : ℂ) + t * I) + 1 / ((u : ℂ) + t * I - 1)).re) +
        ∫ r, Real.log (((σ' - 1 / 2) ^ 2 + (r - t) ^ 2) / ((σ - 1 / 2) ^ 2 + (r - t) ^ 2)) / 2
          ∂boundaryMeasure hW := by
  have hΦc : ContinuousOn (fun u : ℝ => (weilContinuation hW ((u : ℂ) + t * I)).re)
      (Icc σ σ') := by
    refine Complex.continuous_re.comp_continuousOn ?_
    refine (differentiableOn_weilContinuation hW).continuousOn.comp (by fun_prop) fun u hu => ?_
    show 1 / 2 < ((u : ℂ) + t * I).re
    simp
    linarith [hu.1]
  have hderiv : ∀ u ∈ uIcc σ σ', HasDerivAt (fun u : ℝ => (g ((u : ℂ) + t * I)).re)
      ((weilContinuation hW ((u : ℂ) + t * I)).re -
        (zetaArchimedeanDatum ((u : ℂ) + t * I) + 1 / ((u : ℂ) + t * I - 1)).re) u := by
    intro u hu
    rw [uIcc_of_le hσσ'] at hu
    have h1 := (hg u hu).comp_add_const (u : ℂ) (t * I)
    have h2 := h1.real_of_complex
    convert h2 using 1
    simp only [Complex.neg_re, Complex.sub_re, Complex.add_re]
    ring
  have hint : IntervalIntegrable (fun u : ℝ => (weilContinuation hW ((u : ℂ) + t * I)).re -
      (zetaArchimedeanDatum ((u : ℂ) + t * I) + 1 / ((u : ℂ) + t * I - 1)).re) volume σ σ' :=
    ((hΦc.sub hcont).mono (by rw [uIcc_of_le hσσ'])).intervalIntegrable
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    intervalIntegral.integral_sub (hΦc.mono (by rw [uIcc_of_le hσσ'])).intervalIntegrable
      (hcont.mono (by rw [uIcc_of_le hσσ'])).intervalIntegrable,
    integral_re_weilContinuation_eq hW hσ hσσ' t]
  ring

end RHTower.WeilSpectral

end
