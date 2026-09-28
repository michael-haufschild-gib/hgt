import GaloisForLFunctions.RHTower.ChronologicalTailSeparation
import GaloisForLFunctions.HTGeometry.WeierstrassApprox

/-!
# The heat transform of a continuous tail profile is injective

For `0 < θ < 1` and `f` continuous on `[θ, 1]`, if the heat transform
`F_f(u) = ∫_θ¹ f(x) h(xu) dx` vanishes on the sampling interval `[1, 2]`, then `f = 0` on `[θ, 1]`.

Vanishing on `[1, 2]` propagates to all `u > 0` (analyticity in `u`).  The Mellin transform in `u`
factors as the positive Bose bracket times `∫_θ¹ f(x) x^{-s} dx`, so this moment vanishes for
`0 < s < 1`; it is an entire function of `s`, hence vanishes identically, and at `s = -n` it is the
`n`-th polynomial moment.  All polynomial moments of the real and imaginary parts vanish, and
Weierstrass approximation gives `∫ (Re f)² = ∫ (Im f)² = 0`.
-/

open Complex Set MeasureTheory Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

namespace RHTower

/-- **Vanishing moments.**  A continuous real function on `[a, b]` all of whose polynomial moments
vanish is zero there. -/
theorem eqOn_zero_of_moments_eq_zero {a b : ℝ} (hlt : a < b) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) (h : ∀ n : ℕ, ∫ x in a..b, g x * x ^ n = 0) :
    EqOn g 0 (Icc a b) := by
  have hab : a ≤ b := hlt.le
  have hpoly : ∀ p : Polynomial ℝ, ∫ x in a..b, g x * p.eval x = 0 := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      have hi : ∀ r : Polynomial ℝ, IntervalIntegrable (fun x => g x * r.eval x) volume a b :=
        fun r => (hg.mul r.continuous.continuousOn).intervalIntegrable_of_Icc hab
      simp only [Polynomial.eval_add, mul_add]
      rw [intervalIntegral.integral_add (hi p) (hi q), hp, hq, add_zero]
    | monomial n c =>
      simp only [Polynomial.eval_monomial]
      have : (fun x => g x * (c * x ^ n)) = fun x => c * (g x * x ^ n) := by
        funext x; ring
      rw [this, intervalIntegral.integral_const_mul, h n, mul_zero]
  have hsq : ∫ x in a..b, g x ^ 2 = 0 := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM a ⟨le_refl a, hab⟩)
    refine le_antisymm ?_ (intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set η := ε / ((b - a + 1) * (M + 1)) with hη
    have hηpos : 0 < η := by positivity
    obtain ⟨p, hp⟩ := HTGeometry.exists_poly_approx ⟨fun x : Icc a b => g x,
      hg.restrict⟩ hηpos
    have hdiff : ∫ x in a..b, g x ^ 2 = ∫ x in a..b, g x * (g x - p.eval x) := by
      have hi1 : IntervalIntegrable (fun x => g x * g x) volume a b :=
        (hg.mul hg).intervalIntegrable_of_Icc hab
      have hi2 : IntervalIntegrable (fun x => g x * p.eval x) volume a b :=
        (hg.mul p.continuous.continuousOn).intervalIntegrable_of_Icc hab
      have : (fun x => g x * (g x - p.eval x)) = fun x => g x * g x - g x * p.eval x := by
        funext x; ring
      rw [this, intervalIntegral.integral_sub hi1 hi2, hpoly p, sub_zero]
      congr 1; funext x; ring
    rw [hdiff, zero_add]
    have hbound : ∀ x ∈ Set.uIoc a b, ‖g x * (g x - p.eval x)‖ ≤ M * η := by
      intro x hx
      have hx' : x ∈ Icc a b := by
        rw [Set.uIoc_of_le hab] at hx; exact ⟨hx.1.le, hx.2⟩
      rw [norm_mul]
      have h1 : ‖g x‖ ≤ M := hM x hx'
      have h2 : ‖g x - p.eval x‖ ≤ η := by
        have := hp ⟨x, hx'⟩
        rw [Real.norm_eq_abs]; exact this.le
      exact mul_le_mul h1 h2 (norm_nonneg _) hM0
    calc ∫ x in a..b, g x * (g x - p.eval x)
        ≤ ‖∫ x in a..b, g x * (g x - p.eval x)‖ := le_abs_self _
      _ ≤ M * η * |b - a| := intervalIntegral.norm_integral_le_of_norm_le_const hbound
      _ ≤ ε := by
          rw [abs_of_nonneg (by linarith), hη]
          have hden : 0 < (b - a + 1) * (M + 1) := by positivity
          rw [show M * (ε / ((b - a + 1) * (M + 1))) * (b - a)
            = ε * (M * (b - a)) / ((b - a + 1) * (M + 1)) by ring]
          rw [div_le_iff₀ hden]
          have hMba : M * (b - a) ≤ (b - a + 1) * (M + 1) := by nlinarith
          nlinarith
  intro x hx
  by_contra hne
  have hsq_cont : ContinuousOn (fun x => g x ^ 2) (Icc a b) := hg.pow 2
  have hpos : 0 < ∫ x in a..b, g x ^ 2 := by
    rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall
      fun y => sq_nonneg (g y)) ((hsq_cont.intervalIntegrable_of_Icc hab))]
    refine ⟨hlt, ?_⟩
    have hgx : g x ^ 2 ≠ 0 := pow_ne_zero 2 hne
    -- a neighbourhood of `x` inside the interval on which `g ≠ 0`
    have hU : ∀ᶠ y in 𝓝[Icc a b] x, g y ^ 2 ≠ 0 :=
      (hsq_cont x hx).eventually_ne hgx
    obtain ⟨V, hVo, hxV, hVsub⟩ := mem_nhdsWithin.mp hU
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hVo x hxV
    set I := Ioo (max a (x - r)) (min b (x + r)) with hI
    have hxa : a ≤ x := hx.1
    have hxb : x ≤ b := hx.2
    have hIpos : max a (x - r) < min b (x + r) :=
      max_lt (lt_min hlt (by linarith)) (lt_min (by linarith) (by linarith))
    have hIsub : I ⊆ Function.support (fun y => g y ^ 2) ∩ Ioc a b := by
      intro y hy
      have hyab : y ∈ Icc a b := ⟨(le_max_left _ _).trans hy.1.le, hy.2.le.trans (min_le_left _ _)⟩
      have hyball : y ∈ Metric.ball x r := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor
        · linarith [(le_max_right a (x - r)).trans_lt hy.1]
        · linarith [hy.2.trans_le (min_le_right b (x + r))]
      exact ⟨hVsub ⟨hball hyball, hyab⟩, (le_max_left _ _).trans_lt hy.1,
        hy.2.le.trans (min_le_left _ _)⟩
    calc (0 : ENNReal) < volume I := by rw [hI, Real.volume_Ioo]; simpa using hIpos
      _ ≤ volume (Function.support (fun y => g y ^ 2) ∩ Ioc a b) := measure_mono hIsub
  rw [hsq] at hpos
  exact lt_irrefl 0 hpos

/-- Points `1/2 + 1/(n+4)` accumulate at `1/2` inside `(0, 1)`. -/
theorem frequently_nhdsNE_half_of_forall_Ioo {p : ℂ → Prop}
    (h : ∀ s : ℝ, 0 < s → s < 1 → p (s : ℂ)) : ∃ᶠ w in 𝓝[≠] ((1 / 2 : ℝ) : ℂ), p w := by
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 4)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 4)) atTop atTop :=
      tendsto_atTop_add_const_right _ 4 tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 4)⁻¹) atTop (𝓝 0) := h1.inv_tendsto_atTop
    simpa [one_div] using h2
  have htend : Tendsto (fun n : ℕ => ((1 / 2 + 1 / ((n : ℝ) + 4) : ℝ) : ℂ)) atTop
      (𝓝[≠] ((1 / 2 : ℝ) : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · refine (Complex.continuous_ofReal.tendsto _).comp ?_
      simpa using tendsto_const_nhds.add hinv
    · filter_upwards with n
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcontra
      have := Complex.ofReal_injective hcontra
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 4) := by positivity
      linarith
  refine htend.frequently (Frequently.of_forall fun n => h _ (by positivity) ?_)
  have hn : (4 : ℝ) ≤ (n : ℝ) + 4 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have : 1 / ((n : ℝ) + 4) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hn
  linarith

/-- **Injectivity of the tail heat transform.**  If `F_f` vanishes on `[1, 2]` for `f` continuous on
`[θ, 1]`, then `f = 0` on `[θ, 1]`. -/
theorem eqOn_zero_of_boseTransform_tailProfile_eq_zero {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {f : ℝ → ℂ} (hf : ContinuousOn f (Icc θ 1))
    (h : ∀ t : ℝ, t ∈ Icc (1 : ℝ) 2 → boseTransform (tailProfile θ f) (t : ℂ) = 0) :
    EqOn f 0 (Icc θ 1) := by
  classical
  set F : ℝ → ℂ := (Icc θ 1).indicator f with hFdef
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  set C := max C₀ 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  have hFb : ∀ x, ‖F x‖ ≤ C := by
    intro x
    by_cases hx : x ∈ Icc θ 1
    · rw [hFdef, Set.indicator_of_mem hx]; exact (hC₀ x hx).trans (le_max_left _ _)
    · rw [hFdef, Set.indicator_of_notMem hx, norm_zero]; exact hC0
  have hFm : Measurable F := by
    have : F = (Icc θ 1).piecewise f 0 := by
      rw [hFdef, Set.piecewise_eq_indicator]
    rw [this]
    exact ContinuousOn.measurable_piecewise hf continuousOn_const measurableSet_Icc
  have hprof : ∀ x ∈ Ioo (0 : ℝ) 1, tailProfile θ F x = tailProfile θ f x := by
    intro x hx
    unfold tailProfile
    split_ifs with hθx
    · rw [hFdef, Set.indicator_of_mem (show x ∈ Icc θ 1 from ⟨hθx, hx.2.le⟩)]
    · rfl
  have hgm : Measurable (tailProfile θ F) := by
    unfold tailProfile
    exact Measurable.ite (measurableSet_le measurable_const measurable_id) hFm measurable_const
  have hgb : ∀ x, ‖tailProfile θ F x‖ ≤ C := by
    intro x; unfold tailProfile; split_ifs
    · exact hFb x
    · rw [norm_zero]; exact hC0
  have hgint : IntegrableOn (tailProfile θ F) (Ioo (0 : ℝ) 1) :=
    Measure.integrableOn_of_bounded (M := C) (by rw [Real.volume_Ioo]; simp)
      hgm.aestronglyMeasurable (Eventually.of_forall hgb)
  have htrans : ∀ u : ℂ, boseTransform (tailProfile θ F) u = boseTransform (tailProfile θ f) u := by
    intro u
    exact setIntegral_congr_fun measurableSet_Ioo fun x hx => by rw [hprof x hx]
  have hzero : ∀ t : ℝ, 0 < t → boseTransform (tailProfile θ F) (t : ℂ) = 0 :=
    fun t ht => boseTransform_ofReal_eq_zero hgint (fun s hs => by rw [htrans]; exact h s hs) ht
  -- the real moments on `(0, 1)`
  have hmomReal : ∀ s : ℝ, 0 < s → s < 1 → tailMomentE θ F (s : ℂ) = 0 := by
    intro s hs0 hs1
    have hint : IntegrableOn (fun x : ℝ => ‖tailProfile θ F x‖ * x ^ (-s)) (Ioo (0 : ℝ) 1) := by
      refine Measure.integrableOn_of_bounded (M := C * θ ^ (-s)) (by rw [Real.volume_Ioo]; simp)
        ((hgm.norm.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
      rw [ae_restrict_iff' measurableSet_Ioo]
      refine Eventually.of_forall fun x hx => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _)
        (Real.rpow_nonneg hx.1.le _))]
      unfold tailProfile
      split_ifs with hθx
      · refine mul_le_mul (hFb x) ?_ (Real.rpow_nonneg hx.1.le _) hC0
        exact Real.rpow_le_rpow_of_nonpos hθ0 hθx (by linarith)
      · rw [norm_zero, zero_mul]; positivity
    have hm := mellin_boseTransform hs0 hs1 hgm hint
    have hlhs : ∫ u in Ioi (0 : ℝ), ((u ^ (s - 1) : ℝ) : ℂ) * boseTransform (tailProfile θ F) (u : ℂ)
        = 0 := by
      rw [← integral_zero ℝ ℂ]
      refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      simp [hzero u hu]
    rw [hlhs] at hm
    have hbr : ((boseBracket s : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (boseBracket_pos hs0 hs1).ne'
    have hmom : ∫ x in Ioo (0 : ℝ) 1, tailProfile θ F x * ((x ^ (-s) : ℝ) : ℂ) = 0 :=
      (mul_eq_zero.mp hm.symm).resolve_left hbr
    rw [tailMomentE, ← hmom]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [Real.rpow_def_of_pos hx.1]
    push_cast
    ring_nf
  -- analytic continuation of the moment
  have hent : Differentiable ℂ (tailMomentE θ F) :=
    differentiable_tailMomentE hθ0 hθ1.le hC0 hFm hFb
  have hall : EqOn (tailMomentE θ F) 0 univ :=
    (hent.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (mem_univ _) (frequently_nhdsNE_half_of_forall_Ioo hmomReal)
  -- the polynomial moments
  have hpolymom : ∀ n : ℕ, ∫ x in θ..1, f x * (x : ℂ) ^ n = 0 := by
    intro n
    have h1 := hall (mem_univ (-(n : ℂ)))
    simp only [Pi.zero_apply, tailMomentE] at h1
    have h2 : ∫ x in Ioo (0 : ℝ) 1, tailProfile θ F x * Complex.exp (((Real.log x : ℝ) : ℂ) * (-(-(n : ℂ))))
        = ∫ x in Ioo (0 : ℝ) 1, (Ico θ 1).indicator (fun x => f x * (x : ℂ) ^ n) x := by
      refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have hexp : Complex.exp (((Real.log x : ℝ) : ℂ) * (-(-(n : ℂ)))) = (x : ℂ) ^ n := by
        rw [neg_neg, mul_comm, Complex.exp_nat_mul, ← Complex.ofReal_exp, Real.exp_log hx.1]
      rw [hexp]
      unfold tailProfile
      split_ifs with hθx
      · rw [hFdef, Set.indicator_of_mem (show x ∈ Icc θ 1 from ⟨hθx, hx.2.le⟩),
          Set.indicator_of_mem (show x ∈ Ico θ 1 from ⟨hθx, hx.2⟩)]
      · rw [Set.indicator_of_notMem (fun hmem => hθx hmem.1), zero_mul]
    rw [h2, setIntegral_indicator measurableSet_Ico,
      show Ioo (0 : ℝ) 1 ∩ Ico θ 1 = Ico θ 1 from inter_eq_right.mpr fun x hx =>
        ⟨lt_of_lt_of_le hθ0 hx.1, hx.2⟩,
      integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hθ1.le] at h1
    exact h1
  -- real and imaginary parts
  have hcont_re : ContinuousOn (fun x => (f x).re) (Icc θ 1) := Complex.continuous_re.comp_continuousOn hf
  have hcont_im : ContinuousOn (fun x => (f x).im) (Icc θ 1) := Complex.continuous_im.comp_continuousOn hf
  have hint_n : ∀ n : ℕ, IntervalIntegrable (fun x => f x * (x : ℂ) ^ n) volume θ 1 := fun n =>
    (hf.mul ((Complex.continuous_ofReal.pow n).continuousOn)).intervalIntegrable_of_Icc hθ1.le
  have hre : ∀ n : ℕ, ∫ x in θ..1, (f x).re * x ^ n = 0 := by
    intro n
    have := congrArg Complex.re (hpolymom n)
    rw [Complex.zero_re, ← Complex.reCLM_apply,
      ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hint_n n)] at this
    simpa [← Complex.ofReal_pow] using this
  have him : ∀ n : ℕ, ∫ x in θ..1, (f x).im * x ^ n = 0 := by
    intro n
    have := congrArg Complex.im (hpolymom n)
    rw [Complex.zero_im, ← Complex.imCLM_apply,
      ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hint_n n)] at this
    simpa [← Complex.ofReal_pow] using this
  intro x hx
  have h1 := eqOn_zero_of_moments_eq_zero hθ1 hcont_re hre hx
  have h2 := eqOn_zero_of_moments_eq_zero hθ1 hcont_im him hx
  exact Complex.ext (by simpa using h1) (by simpa using h2)

end RHTower
