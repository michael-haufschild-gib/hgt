import GaloisForLFunctions.RHTower.WeilConeSoundararajanMoments
import GaloisForLFunctions.RHTower.GammaVerticalPhaseSecondOrder
import GaloisForLFunctions.RHTower.WeilProducerPerronExplicitFormula

/-!
# Riemann–von Mangoldt on the Weil cone

Let `lam` be full-cone Weil-positive with boundary measure `μ = μ_lam`.  For `ζ` (when RH holds)
`μ` counts the zeros, `μ({γ}) = ord_{½+iγ} ξ`.

**Theorem** (`exists_abs_integral_countKernel_sub_le`).  There is `C` with

`|∫ K_T dμ − ((T/2) log(T/2π) − T/2)| ≤ C`  for `T ≥ 4`,

where `K_T(r) = arctan((T − r)/η) + arctan(r/η)`, `η = 3/2`.  The kernel `K_T` is `π` times the
indicator of `[0, T]`, smoothed at scale `η`.  So every Weil-positive system has the
Riemann–von Mangoldt main term `(T/2π) log(T/2πe)` in its smoothed spectral counting, with bounded
error.

**Proof.**  The Poisson representation `Re Φ_lam(2 + it) = ∫ η/(η² + (r − t)²) dμ(r)`, integrated
over `t ∈ [0, T]` (Tonelli), gives `∫_0^T Re Φ_lam(2 + it) dt = ∫ K_T dμ`
(`setIntegral_re_weilContinuation_eq`).  On `Re s = 2`,
`Φ_lam = ½ψ(s/2) − ½ log π + 1/s + 1/(s − 1) − Σ lam(n) n^{−s}`.  The digamma term carries the main
term by `|Re ψ(1 + iu) − log u| ≤ 8/u²`.  The rational terms integrate to arctangents, and the
Dirichlet series is the derivative of `Σ lam(n) n^{−s}/log n`, which is bounded on `Re s = 2`.
-/

open Complex Set Filter MeasureTheory Topology

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz

/-- The smoothed counting kernel `K_T(r) = arctan((T − r)/η) + arctan(r/η)`, `η = 3/2`. -/
def countKernel (T r : ℝ) : ℝ := Real.arctan ((T - r) / (3 / 2)) + Real.arctan (r / (3 / 2))

theorem continuous_countKernel (T : ℝ) : Continuous (countKernel T) := by
  unfold countKernel; fun_prop

theorem countKernel_nonneg {T : ℝ} (hT : 0 ≤ T) (r : ℝ) : 0 ≤ countKernel T r := by
  unfold countKernel
  have h : Real.arctan (-(r / (3 / 2))) ≤ Real.arctan ((T - r) / (3 / 2)) :=
    Real.arctan_strictMono.monotone (by linarith)
  rw [Real.arctan_neg] at h
  linarith

/-- `∫_0^T η/(η² + (r − t)²) dt = K_T(r)`. -/
theorem integral_poissonKernel_eq (T r : ℝ) :
    ∫ t in (0 : ℝ)..T, (3 / 2 : ℝ) / ((3 / 2) ^ 2 + (r - t) ^ 2) = countKernel T r := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) T, HasDerivAt (fun t => Real.arctan ((t - r) / (3 / 2)))
      ((3 / 2 : ℝ) / ((3 / 2) ^ 2 + (r - t) ^ 2)) t := by
    intro t _
    have h := (Real.hasDerivAt_arctan ((t - r) / (3 / 2))).comp t
      (((hasDerivAt_id t).sub_const r).div_const (3 / 2))
    refine h.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_const.div (by fun_prop) (fun t => by positivity) : Continuous fun t : ℝ =>
      (3 / 2 : ℝ) / ((3 / 2) ^ 2 + (r - t) ^ 2)).intervalIntegrable _ _)]
  unfold countKernel
  rw [show (0 - r) / (3 / 2 : ℝ) = -(r / (3 / 2)) by ring, Real.arctan_neg]
  ring

/-- **Tonelli.**  `∫_{(0,T]} Re Φ_lam(2 + it) dt = ∫ K_T dμ_lam`. -/
theorem setIntegral_re_weilContinuation_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {T : ℝ}
    (hT : 0 ≤ T) :
    ∫ t in Ioc 0 T, (weilContinuation hW ((2 : ℂ) + t * I)).re =
      ∫ r, countKernel T r ∂boundaryMeasure hW := by
  set μ := boundaryMeasure hW
  haveI := sFinite_boundaryMeasure hW
  set g : ℝ → ℝ → ℝ := fun t r => (3 / 2 : ℝ) / ((3 / 2) ^ 2 + (r - t) ^ 2) with hg
  have hg0 : ∀ t r, 0 ≤ g t r := fun t r => by simp only [hg]; positivity
  have hpt : ∀ t : ℝ, ENNReal.ofReal (weilContinuation hW ((2 : ℂ) + t * I)).re =
      ∫⁻ r, ENNReal.ofReal (g t r) ∂μ := by
    intro t
    have h := ofReal_re_weilContinuation_eq hW 2 t (by norm_num)
    push_cast at h
    rw [h]
    refine lintegral_congr fun r => ?_
    simp only [hg]
    norm_num
  -- the left side as a lintegral
  have hre0 : ∀ t : ℝ, 0 ≤ (weilContinuation hW ((2 : ℂ) + t * I)).re := fun t =>
    re_weilContinuation_nonneg hW (by simp; norm_num)
  have hcontΦ : Continuous fun t : ℝ => (weilContinuation hW ((2 : ℂ) + t * I)).re := by
    refine Complex.continuous_re.comp ?_
    exact (differentiableOn_weilContinuation hW).continuousOn.comp_continuous (by fun_prop)
      fun t => show (1 / 2 : ℝ) < ((2 : ℂ) + t * I).re by simp; norm_num
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hre0)
    hcontΦ.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (countKernel_nonneg hT))
      (continuous_countKernel T).aestronglyMeasurable]
  congr 1
  simp_rw [hpt]
  -- swap
  have hmeas : Measurable (Function.uncurry fun (t : ℝ) (r : ℝ) => ENNReal.ofReal (g t r)) :=
    ENNReal.measurable_ofReal.comp (by simp only [hg]; fun_prop)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  refine lintegral_congr fun r => ?_
  have hint : IntegrableOn (fun t => g t r) (Ioc 0 T) :=
    ((continuous_const.div (by fun_prop) (fun t => by positivity) : Continuous fun t =>
      g t r).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun t => hg0 t r),
    ← intervalIntegral.integral_of_le hT]
  simp only [hg]
  rw [integral_poissonKernel_eq]

/-! ### The explicit side on `Re s = 2` -/

theorem re_weilContinuation_two_add {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (t : ℝ) :
    (weilContinuation hW ((2 : ℂ) + t * I)).re =
      (Complex.digamma ((1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re / 2 - Real.log Real.pi / 2 +
        2 / (4 + t ^ 2) + 1 / (1 + t ^ 2) - (LSeries (lamC lam) ((2 : ℂ) + t * I)).re := by
  rw [weilContinuation_eq hW (by norm_num), weilFunction]
  have e1 : ((2 : ℂ) + t * I) / 2 = (1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    push_cast; ring_nf
  have e2 : ((1 : ℂ) / ((2 : ℂ) + t * I)).re = 2 / (4 + t ^ 2) := by
    rw [Complex.div_re]; simp [Complex.normSq]; ring_nf
  have e3 : ((1 : ℂ) / ((2 : ℂ) + t * I - 1)).re = 1 / (1 + t ^ 2) := by
    rw [show (2 : ℂ) + t * I - 1 = 1 + t * I by ring, Complex.div_re]
    simp [Complex.normSq]; ring_nf
  have e4 : (Complex.digamma ((1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I) / 2).re =
      (Complex.digamma ((1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re / 2 := by
    rw [Complex.div_ofNat_re]
  have e5 : ((Real.log Real.pi : ℂ) / 2).re = Real.log Real.pi / 2 := by
    rw [Complex.div_ofNat_re, Complex.ofReal_re]
  rw [e1, Complex.sub_re, Complex.add_re, Complex.add_re, Complex.sub_re, e2, e3, e4, e5]


/-! ### The integrals -/

theorem norm_LSeries_le_tsum_two {f : ℕ → ℂ} (hf : LSeriesSummable f 2) {s : ℂ}
    (hs : s.re = 2) : ‖LSeries f s‖ ≤ ∑' n, ‖LSeries.term f 2 n‖ := by
  have heq : ∀ n, ‖LSeries.term f s n‖ = ‖LSeries.term f 2 n‖ := fun n => by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hs]; simp
  unfold LSeries
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr heq))
  exact hf.norm.congr fun n => (heq n).symm

/-- The Dirichlet part integrates to a bounded quantity: it is the derivative of
`Σ lam(n) n^{−s}/log n` along `Re s = 2`. -/
theorem exists_abs_integral_re_LSeries_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ M : ℝ, ∀ T : ℝ, |∫ t in (0 : ℝ)..T, (LSeries (lamC lam) ((2 : ℂ) + t * I)).re| ≤ M := by
  have habs := abscissaOfAbsConv_lamLogC_le hW
  have habsC := abscissaOfAbsConv_lamC_le hW
  have hlt : ∀ t : ℝ, LSeries.abscissaOfAbsConv (lamLogC lam) < (((2 : ℂ) + t * I).re : ℝ) := by
    intro t
    refine habs.trans_lt ?_
    simp only [Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
    exact_mod_cast (by norm_num : (1 : ℝ) < 2)
  have hltC : ∀ t : ℝ, LSeries.abscissaOfAbsConv (lamC lam) < (((2 : ℂ) + t * I).re : ℝ) := by
    intro t
    refine habsC.trans_lt ?_
    simp only [Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
    exact_mod_cast (by norm_num : (1 : ℝ) < 2)
  have hsum2 : LSeriesSummable (lamLogC lam) 2 :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      refine habs.trans_lt ?_; simp only [Complex.re_ofNat]
      exact_mod_cast (by norm_num : (1 : ℝ) < 2))
  set M₀ : ℝ := ∑' n, ‖LSeries.term (lamLogC lam) 2 n‖ with hM₀
  refine ⟨2 * M₀, fun T => ?_⟩
  set f : ℝ → ℂ := fun t => LSeries (lamLogC lam) ((2 : ℂ) + t * I) with hf
  have hfd : ∀ t : ℝ, HasDerivAt f (-(LSeries (lamC lam) ((2 : ℂ) + t * I)) * I) t := by
    intro t
    have h := ((LSeries_hasDerivAt (hlt t)).comp_add_const (2 : ℂ) ((t : ℂ) * I))
    have h2 : HasDerivAt (fun x : ℝ => (2 : ℂ) + (x : ℂ) * I) I t := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const I).comp_ofReal.const_add 2
    have h3 := (LSeries_hasDerivAt (hlt t)).comp_of_eq (x := (t : ℝ)) h2 rfl
    rw [logMul_lamLogC] at h3
    exact h3
  have hcont : Continuous fun t : ℝ => LSeries (lamC lam) ((2 : ℂ) + t * I) :=
    (LSeries_differentiableOn (lamC lam)).continuousOn.comp_continuous (by fun_prop) hltC
  have hint : IntervalIntegrable (fun t : ℝ => -(LSeries (lamC lam) ((2 : ℂ) + t * I)) * I)
      volume 0 T := ((hcont.neg).mul continuous_const).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hfd t) hint
  have hre : ∫ t in (0 : ℝ)..T, (LSeries (lamC lam) ((2 : ℂ) + t * I)).re =
      (∫ t in (0 : ℝ)..T, LSeries (lamC lam) ((2 : ℂ) + t * I)).re := by
    have h := Complex.reCLM.intervalIntegral_comp_comm (hcont.intervalIntegrable (μ := volume) 0 T)
    simpa only [Complex.reCLM_apply] using h
  have h1 : -(∫ t in (0 : ℝ)..T, LSeries (lamC lam) ((2 : ℂ) + t * I)) * I = f T - f 0 := by
    rw [← hFTC, intervalIntegral.integral_mul_const, intervalIntegral.integral_neg]
  have hval : ∫ t in (0 : ℝ)..T, LSeries (lamC lam) ((2 : ℂ) + t * I) = I * (f T - f 0) := by
    linear_combination I * h1 + (∫ t in (0 : ℝ)..T, LSeries (lamC lam) ((2 : ℂ) + t * I)) *
      Complex.I_sq
  rw [hre, hval]
  have hfb : ∀ t : ℝ, ‖f t‖ ≤ M₀ := fun t =>
    norm_LSeries_le_tsum_two hsum2 (by simp)
  calc |(I * (f T - f 0)).re| ≤ ‖I * (f T - f 0)‖ := Complex.abs_re_le_norm _
    _ = ‖f T - f 0‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ ‖f T‖ + ‖f 0‖ := norm_sub_le _ _
    _ ≤ 2 * M₀ := by linarith [hfb T, hfb 0]


theorem continuous_re_digamma_one_add (c : ℝ) :
    Continuous fun t : ℝ => (Complex.digamma ((1 : ℂ) + ((c * t : ℝ) : ℂ) * I)).re := by
  refine Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun t => ?_)
  have h := (RHTower.differentiableAt_digamma_of_re_pos
    (z := (1 : ℂ) + ((c * t : ℝ) : ℂ) * I) (by simp)).continuousAt
  exact h.comp (f := fun t : ℝ => (1 : ℂ) + ((c * t : ℝ) : ℂ) * I) (by fun_prop)

/-- `∫_0^T ½ Re ψ(1 + it/2) dt = ½(T log(T/2) − T) + O(1)`. -/
theorem exists_abs_integral_re_digamma_sub_le :
    ∃ C : ℝ, ∀ T : ℝ, 4 ≤ T →
      |(∫ t in (0 : ℝ)..T, (Complex.digamma ((1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re / 2) -
        (T * Real.log (T / 2) - T) / 2| ≤ C := by
  have hA : Continuous fun t : ℝ => (Complex.digamma ((1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re := by
    have h := continuous_re_digamma_one_add (1 / 2)
    refine h.congr fun t => ?_
    rw [show (1 / 2 : ℝ) * t = t / 2 by ring]
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 4)
    (hA.div_const 2).continuousOn
  refine ⟨4 * |K| + 4 + |(4 * Real.log 2 - 4) / 2|, fun T hT => ?_⟩
  set A : ℝ → ℝ := fun t => (Complex.digamma ((1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re / 2 with hAdef
  have hAc : Continuous A := hA.div_const 2
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hAc.intervalIntegrable (μ := volume) 0 4) (hAc.intervalIntegrable 4 T)
  -- the piece on `[0, 4]`
  have h04 : |∫ t in (0 : ℝ)..4, A t| ≤ 4 * |K| := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 4) (C := |K|)
      (f := A) fun t ht => by
        rw [uIoc_of_le (by norm_num)] at ht
        exact (hK t ⟨ht.1.le, ht.2⟩).trans (le_abs_self K)
    rw [Real.norm_eq_abs] at h
    have h' : |∫ t in (0 : ℝ)..4, A t| ≤ |K| * 4 := by simpa using h
    linarith
  -- the piece on `[4, T]`
  have hlogD : ∀ t ∈ uIcc (4 : ℝ) T, HasDerivAt (fun t => (t * Real.log (t / 2) - t) / 2)
      (Real.log (t / 2) / 2) t := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have h1 : HasDerivAt (fun t : ℝ => Real.log (t / 2)) (1 / 2 / (t / 2)) t :=
      ((hasDerivAt_id t).div_const 2).log (by simp; exact ht0)
    have h2 := ((hasDerivAt_id t).mul h1).sub (hasDerivAt_id t)
    refine (h2.div_const 2).congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hlogI : ∫ t in (4 : ℝ)..T, Real.log (t / 2) / 2 =
      (T * Real.log (T / 2) - T) / 2 - (4 * Real.log 2 - 4) / 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hlogD]
    · norm_num
    · refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.div_const (ContinuousOn.log (continuousOn_id.div_const 2) ?_) 2
      intro t ht
      rw [uIcc_of_le hT] at ht
      simp only [id]
      linarith [ht.1]
  have hdiff : |∫ t in (4 : ℝ)..T, (A t - Real.log (t / 2) / 2)| ≤ 4 := by
    have hbound : ∀ t ∈ uIoc (4 : ℝ) T, ‖A t - Real.log (t / 2) / 2‖ ≤ 16 / t ^ 2 := by
      intro t ht
      rw [uIoc_of_le hT] at ht
      have ht2 : 2 ≤ t / 2 := by linarith [ht.1]
      have h := abs_re_digamma_one_sub_log_le ht2
      simp only [hAdef, Real.norm_eq_abs]
      rw [show (Complex.digamma ((1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re / 2 - Real.log (t / 2) / 2 =
        ((Complex.digamma ((1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re - Real.log (t / 2)) / 2 by ring,
        abs_div, abs_two]
      have e : 8 / (t / 2) ^ 2 / 2 = 16 / t ^ 2 := by field_simp; ring
      rw [← e]
      exact div_le_div_of_nonneg_right h (by norm_num)
    have hint : IntervalIntegrable (fun t : ℝ => 16 / t ^ 2) volume 4 T := by
      refine ContinuousOn.intervalIntegrable ?_
      intro t ht
      rw [uIcc_of_le hT] at ht
      have htp : (0 : ℝ) < t := by linarith [ht.1]
      have : t ^ 2 ≠ 0 := by positivity
      exact (continuousAt_const.div (continuousAt_id.pow 2) this).continuousWithinAt
    have h := intervalIntegral.norm_integral_le_of_norm_le hT
      (Eventually.of_forall fun t ht => hbound t (by rw [uIoc_of_le hT]; exact ht)) hint
    have hval : ∫ t in (4 : ℝ)..T, 16 / t ^ 2 = 4 - 16 / T := by
      have hd : ∀ t ∈ uIcc (4 : ℝ) T, HasDerivAt (fun t : ℝ => -16 / t) (16 / t ^ 2) t := by
        intro t ht
        rw [uIcc_of_le hT] at ht
        have ht0 : t ≠ 0 := by linarith [ht.1]
        have h := (hasDerivAt_inv ht0).const_mul (-16 : ℝ)
        have e : (fun x : ℝ => -16 / x) = fun x => -16 * x⁻¹ := by
          funext x; rw [div_eq_mul_inv]
        rw [e]
        refine h.congr_deriv ?_
        field_simp
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
      ring
    rw [Real.norm_eq_abs, hval] at h
    have : 0 < 16 / T := by positivity
    linarith
  have hsub := intervalIntegral.integral_sub (hAc.intervalIntegrable (μ := volume) 4 T)
    (show IntervalIntegrable (fun t : ℝ => Real.log (t / 2) / 2) volume 4 T by
      refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.div_const (ContinuousOn.log (continuousOn_id.div_const 2) ?_) 2
      intro t ht
      rw [uIcc_of_le hT] at ht
      simp only [id]
      linarith [ht.1])
  show |(∫ t in (0 : ℝ)..T, A t) - _| ≤ _
  rw [← hsplit]
  rw [hsub, hlogI] at hdiff
  have habs := abs_nonneg ((4 * Real.log 2 - 4) / 2)
  rw [abs_le] at hdiff h04 ⊢
  have := le_abs_self ((4 * Real.log 2 - 4) / 2)
  have := neg_abs_le ((4 * Real.log 2 - 4) / 2)
  constructor <;> linarith [hdiff.1, hdiff.2, h04.1, h04.2]


/-! ### Riemann–von Mangoldt -/

/-- **Smoothed Riemann–von Mangoldt on the Weil cone.**  For every full-cone Weil-positive `lam`
there is `C` with `|∫ K_T dμ_lam − ((T/2) log(T/2π) − T/2)| ≤ C` for all `T ≥ 4`, where
`K_T(r) = arctan((T − r)/η) + arctan(r/η)`, `η = 3/2`, is `π` times a smoothed indicator of
`[0, T]`. -/
theorem exists_abs_integral_countKernel_sub_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, ∀ T : ℝ, 4 ≤ T →
      |(∫ r, countKernel T r ∂boundaryMeasure hW) -
        (T / 2 * Real.log (T / (2 * Real.pi)) - T / 2)| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := exists_abs_integral_re_digamma_sub_le
  obtain ⟨M, hM⟩ := exists_abs_integral_re_LSeries_le hW
  refine ⟨C₁ + Real.pi + M, fun T hT => ?_⟩
  have hT0 : 0 ≤ T := by linarith
  rw [← setIntegral_re_weilContinuation_eq hW hT0, ← intervalIntegral.integral_of_le hT0]
  simp_rw [re_weilContinuation_two_add hW]
  -- the pieces
  set A : ℝ → ℝ := fun t => (Complex.digamma ((1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re / 2 with hA
  set B : ℝ → ℝ := fun t => 2 / (4 + t ^ 2) with hB
  set C : ℝ → ℝ := fun t => 1 / (1 + t ^ 2) with hC
  set D : ℝ → ℝ := fun t => (LSeries (lamC lam) ((2 : ℂ) + t * I)).re with hD
  have hAc : Continuous A := by
    have h := (continuous_re_digamma_one_add (1 / 2)).div_const 2
    refine h.congr fun t => ?_
    simp only [hA]; rw [show (1 / 2 : ℝ) * t = t / 2 by ring]
  have hBc : Continuous B := continuous_const.div (by fun_prop) fun t => by positivity
  have hCc : Continuous C := continuous_const.div (by fun_prop) fun t => by positivity
  have hDc : Continuous D := by
    have hltC : ∀ t : ℝ, LSeries.abscissaOfAbsConv (lamC lam) <
        (((2 : ℂ) + t * I).re : ℝ) := by
      intro t
      refine (abscissaOfAbsConv_lamC_le hW).trans_lt ?_
      simp only [Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.ofReal_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
      exact_mod_cast (by norm_num : (1 : ℝ) < 2)
    exact Complex.continuous_re.comp
      ((LSeries_differentiableOn (lamC lam)).continuousOn.comp_continuous (by fun_prop) hltC)
  have hsplit : ∫ t in (0 : ℝ)..T, (A t - Real.log Real.pi / 2 + B t + C t - D t) =
      (∫ t in (0 : ℝ)..T, A t) - Real.log Real.pi / 2 * T + (∫ t in (0 : ℝ)..T, B t) +
        (∫ t in (0 : ℝ)..T, C t) - (∫ t in (0 : ℝ)..T, D t) := by
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_sub, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    · ring
    all_goals first
      | exact hAc.intervalIntegrable _ _
      | exact continuous_const.intervalIntegrable _ _
      | exact hBc.intervalIntegrable _ _
      | exact hCc.intervalIntegrable _ _
      | exact hDc.intervalIntegrable _ _
      | exact (hAc.sub continuous_const).intervalIntegrable _ _
      | exact ((hAc.sub continuous_const).add hBc).intervalIntegrable _ _
      | exact (((hAc.sub continuous_const).add hBc).add hCc).intervalIntegrable _ _
  rw [hsplit]
  -- the arctangent integrals
  have hBI : 0 ≤ ∫ t in (0 : ℝ)..T, B t ∧ ∫ t in (0 : ℝ)..T, B t ≤ Real.pi / 2 := by
    have hd : ∀ t ∈ uIcc (0 : ℝ) T, HasDerivAt (fun t => Real.arctan (t / 2)) (B t) t := by
      intro t _
      have h := (Real.hasDerivAt_arctan (t / 2)).comp t ((hasDerivAt_id t).div_const 2)
      refine h.congr_deriv ?_
      simp only [hB]
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hBc.intervalIntegrable _ _)]
    simp only [zero_div, Real.arctan_zero, sub_zero]
    exact ⟨Real.arctan_nonneg.mpr (by linarith), (Real.arctan_lt_pi_div_two _).le⟩
  have hCI : 0 ≤ ∫ t in (0 : ℝ)..T, C t ∧ ∫ t in (0 : ℝ)..T, C t ≤ Real.pi / 2 := by
    have hd : ∀ t ∈ uIcc (0 : ℝ) T, HasDerivAt Real.arctan (C t) t := by
      intro t _
      have h := Real.hasDerivAt_arctan t
      simpa only [hC] using h
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hCc.intervalIntegrable _ _)]
    simp only [Real.arctan_zero, sub_zero]
    exact ⟨Real.arctan_nonneg.mpr hT0, (Real.arctan_lt_pi_div_two _).le⟩
  have hAI := hC₁ T hT
  have hDI := hM T
  have hmain : (T * Real.log (T / 2) - T) / 2 - Real.log Real.pi / 2 * T =
      T / 2 * Real.log (T / (2 * Real.pi)) - T / 2 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by norm_num),
      Real.log_mul (by norm_num) Real.pi_pos.ne']
    ring
  rw [abs_le] at hAI hDI ⊢
  constructor <;> nlinarith [hAI.1, hAI.2, hDI.1, hDI.2, hBI.1, hBI.2, hCI.1, hCI.2, hmain]

end RHTower.WeilSpectral
