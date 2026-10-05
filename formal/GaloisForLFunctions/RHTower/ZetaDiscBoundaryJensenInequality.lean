import GaloisForLFunctions.RHTower.ZetaHalfPlaneDiscJensen

/-!
# Jensen's inequality for `(s - 1) ζ(s)` on the boundary circle

With `G(w) = (s - 1) ζ(s)` at `s = 1/(1 - w)`, the function `θ ↦ log |G(e^{iθ})|` is integrable on
`[0, 2π]` and, for finitely many zeros `u` of `G` in the open unit disc,

`Σ_u log (1/|u|) ≤ (1/2π) ∫_0^{2π} log |G(e^{iθ})| dθ`.

The proof is a reverse Fatou argument.  Jensen's formula on the circles of radius `r_n → 1`
gives `∫ log |G(r_n e^{iθ})| dθ ≥ 2π Σ_u log (r_n/|u|)`.  The growth bound
`log |G(w)| ≤ A - 2 log |1 - w|` and `|1 - r e^{iθ}| ≥ |sin θ|` dominate all these functions by
the integrable `A - 2 log |sin θ|`, while `limsup_n log |G(r_n e^{iθ})| ≤ log |G(e^{iθ})|` for every
`θ ∈ (0, 2π)`.  Fatou's lemma for the nonnegative differences then gives integrability and the
inequality on the boundary.
-/

open Complex Metric Real MeasureTheory Filter Topology

namespace RHTower

noncomputable section

theorem measurable_zetaDisc : Measurable zetaDisc :=
  differentiable_zetaEntire.continuous.measurable.comp
    ((measurable_const.sub measurable_id).inv)

theorem circleMap_zero_ne_one {r θ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hθ : θ ∈ Set.Ioo 0 (2 * π)) : circleMap 0 r θ ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [circleMap, zero_add, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero,
    Complex.one_re] at hre
  have hc : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hc0 : 0 < Real.cos θ := by
    by_contra hneg
    push Not at hneg
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hr0 hneg]
  have hcos : Real.cos θ = 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hr1 hc0.le]
  rw [Real.cos_eq_one_iff_of_lt_of_lt (by linarith [hθ.1, Real.pi_pos]) hθ.2] at hcos
  exact (ne_of_gt hθ.1) hcos

/-- `log |sin θ| ≤ log |1 - r e^{iθ}|` for `r ≥ 0` and `0 < θ < 2π`. -/
theorem log_sin_le_log_norm_one_sub_circleMap {r θ : ℝ} (hr0 : 0 ≤ r)
    (hθ : θ ∈ Set.Ioo 0 (2 * π)) :
    Real.log (Real.sin θ) ≤ Real.log ‖1 - circleMap 0 r θ‖ := by
  have hre : (circleMap 0 r θ).re = r * Real.cos θ := by
    simp [circleMap, Complex.exp_ofReal_mul_I_re]
  have him : (circleMap 0 r θ).im = r * Real.sin θ := by
    simp [circleMap, Complex.exp_ofReal_mul_I_im]
  have hsq : ‖1 - circleMap 0 r θ‖ ^ 2
      = (Real.cos θ - r) ^ 2 + Real.sin θ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, hre, him]
    have := Real.sin_sq_add_cos_sq θ
    linear_combination (r ^ 2 - 1) * this
  rw [← Real.log_abs (Real.sin θ)]
  rcases eq_or_ne (Real.sin θ) 0 with hs | hs
  · rw [hs, abs_zero, Real.log_zero]
    have hc2 : Real.cos θ ^ 2 = 1 := by
      have := Real.sin_sq_add_cos_sq θ
      rw [hs] at this
      linarith
    have hc1 : Real.cos θ ≠ 1 := by
      intro h
      rw [Real.cos_eq_one_iff_of_lt_of_lt (by linarith [hθ.1, Real.pi_pos]) hθ.2] at h
      exact (ne_of_gt hθ.1) h
    have hcm : Real.cos θ = -1 := by
      have : (Real.cos θ - 1) * (Real.cos θ + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (by linarith) hc1
      · linarith
    apply Real.log_nonneg
    have : 1 ≤ ‖1 - circleMap 0 r θ‖ ^ 2 := by rw [hsq, hcm, hs]; nlinarith
    nlinarith [norm_nonneg (1 - circleMap 0 r θ)]
  · refine Real.log_le_log (abs_pos.mpr hs) ?_
    have h1 : |Real.sin θ| ^ 2 ≤ ‖1 - circleMap 0 r θ‖ ^ 2 := by
      rw [hsq, sq_abs]; nlinarith
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).mp h1


/-- **Jensen's inequality on the boundary circle.**  Let `Φ` be measurable, analytic off `1`, with
`Φ(0) ≠ 0` and `log |Φ(w)| ≤ A - 2 log |1 - w|` on the closed unit disc minus `1`.  Then
`θ ↦ log |Φ(e^{iθ})|` is integrable and, for finitely many zeros `u` of `Φ` in the open disc,
`Σ_u log (1/|u|) + log |Φ(0)| ≤ (1/2π) ∫_0^{2π} log |Φ(e^{iθ})| dθ`. -/
theorem circleIntegrable_and_sum_log_add_le_circleAverage {Φ : ℂ → ℂ}
    (hdiff : DifferentiableOn ℂ Φ {1}ᶜ) (hmeas : Measurable Φ) (h0 : Φ 0 ≠ 0)
    (hgrowth : ∃ A : ℝ, ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 1 → Real.log ‖Φ w‖ ≤ A - 2 * Real.log ‖1 - w‖)
    {U : Finset ℂ} (hU : ∀ u ∈ U, Φ u = 0 ∧ ‖u‖ < 1) :
    CircleIntegrable (fun w => Real.log ‖Φ w‖) 0 1 ∧
      ∑ u ∈ U, Real.log (1 / ‖u‖) + Real.log ‖Φ 0‖
        ≤ circleAverage (fun w => Real.log ‖Φ w‖) 0 1 := by
  obtain ⟨A, hA⟩ := hgrowth
  have hanAt : ∀ w : ℂ, w ≠ 1 → AnalyticAt ℂ Φ w := fun w hw =>
    hdiff.analyticAt (isOpen_compl_singleton.mem_nhds hw)
  have hπ : 0 < 2 * π := by positivity
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (2 * π)) with hμ
  set F : ℝ → ℝ := fun θ => A - 2 * Real.log (Real.sin θ) with hF
  set rr : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2) with hrr
  have hrr0 : ∀ n, 0 < rr n := by
    intro n
    have : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 2)]; linarith [n.cast_nonneg (α := ℝ)]
    simp only [hrr]; linarith
  have hrr1 : ∀ n, rr n < 1 := by
    intro n
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    simp only [hrr]; linarith
  have hrr_tend : Tendsto rr atTop (𝓝 1) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n : ℕ => 1 - 1 / (((n + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub h
    rw [sub_zero] at h2
    refine h2.congr fun n => ?_
    simp only [hrr]; push_cast; ring
  set fn : ℕ → ℝ → ℝ := fun n θ => Real.log ‖Φ (circleMap 0 (rr n) θ)‖ with hfn
  set f : ℝ → ℝ := fun θ => Real.log ‖Φ (circleMap 0 1 θ)‖ with hf
  have hae : ∀ᵐ θ ∂μ, θ ∈ Set.Ioo 0 (2 * π) := by
    rw [hμ, ae_restrict_iff' measurableSet_Ioc]
    have h2 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 2 * π := by
      rw [ae_iff]; simp
    filter_upwards [h2] with θ hθ hmem using ⟨hmem.1, lt_of_le_of_ne hmem.2 hθ⟩
  have hFdom : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ θ ∈ Set.Ioo 0 (2 * π),
      Real.log ‖Φ (circleMap 0 r θ)‖ ≤ F θ := by
    intro r hr0 hr1 θ hθ
    have hw : ‖circleMap 0 r θ‖ ≤ 1 := by simp [abs_of_nonneg hr0, hr1]
    have h1 := hA _ hw (circleMap_zero_ne_one hr0 hr1 hθ)
    have h2 := log_sin_le_log_norm_one_sub_circleMap hr0 hθ
    simp only [hF]
    linarith
  have hFint : Integrable F μ := by
    have h1 : IntervalIntegrable (Real.log ∘ Real.sin) volume 0 (2 * π) :=
      intervalIntegrable_log_sin
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hπ.le] at h1
    have h2 : Integrable (fun θ => A - 2 * Real.log (Real.sin θ)) μ :=
      (integrable_const A).sub (h1.const_mul 2)
    exact h2
  have hfnint : ∀ n, Integrable (fn n) μ := by
    intro n
    have h := MeromorphicOn.circleIntegrable_log_norm (c := 0) (R := rr n) (f := Φ)
      (fun w hw => by
        refine (hanAt _ ?_).meromorphicAt
        rintro rfl
        rw [mem_sphere, dist_zero_right, norm_one, abs_of_pos (hrr0 n)] at hw
        exact (hrr1 n).ne hw.symm)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hπ.le).mp h
  have hJn : ∀ n, (∀ u ∈ U, ‖u‖ < rr n) →
      2 * π * (∑ u ∈ U, Real.log (rr n / ‖u‖) + Real.log ‖Φ 0‖) ≤ ∫ θ, fn n θ ∂μ := by
    intro n hn
    have hball : AnalyticOnNhd ℂ Φ (closedBall 0 (rr n)) := by
      intro w hw
      refine hanAt w ?_
      rintro rfl
      rw [mem_closedBall, dist_zero_right, norm_one] at hw
      linarith [hrr1 n]
    have h := sum_log_div_norm_add_log_le_circleAverage (hrr0 n) hball h0
      (fun u hu => (hU u hu).1) hn
    rw [circleAverage_def, intervalIntegral.integral_of_le hπ.le, smul_eq_mul] at h
    calc 2 * π * (∑ u ∈ U, Real.log (rr n / ‖u‖) + Real.log ‖Φ 0‖)
        ≤ 2 * π * ((2 * π)⁻¹ * ∫ θ in Set.Ioc 0 (2 * π), fn n θ) :=
          mul_le_mul_of_nonneg_left h hπ.le
      _ = ∫ θ, fn n θ ∂μ := by rw [← mul_assoc, mul_inv_cancel₀ hπ.ne', one_mul]
  have hev : ∀ᶠ n in atTop, ∀ u ∈ U, ‖u‖ < rr n := by
    rw [Filter.eventually_all_finset]
    intro u hu
    exact hrr_tend.eventually (lt_mem_nhds (hU u hu).2)
  set J : ℝ := ∑ u ∈ U, Real.log (1 / ‖u‖) + Real.log ‖Φ 0‖ with hJ
  have hJtend : Tendsto (fun n => (∑ u ∈ U, Real.log (rr n / ‖u‖) + Real.log ‖Φ 0‖)) atTop
      (𝓝 J) := by
    refine Tendsto.add_const _ (tendsto_finsetSum _ fun u hu => ?_)
    have hu0 : u ≠ 0 := by
      rintro rfl; exact h0 (hU 0 hu).1
    have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    exact (Real.continuousAt_log (by positivity : 1 / ‖u‖ ≠ 0)).tendsto.comp
      (hrr_tend.div_const ‖u‖)
  have hFJ : 2 * π * J ≤ ∫ θ, F θ ∂μ := by
    have hle : ∀ n, ∫ θ, fn n θ ∂μ ≤ ∫ θ, F θ ∂μ := fun n =>
      integral_mono_ae (hfnint n) hFint
        (hae.mono fun θ hθ => hFdom _ (hrr0 n).le (hrr1 n).le θ hθ)
    exact le_of_tendsto (hJtend.const_mul (2 * π)) (hev.mono fun n hn => (hJn n hn).trans (hle n))
  set g : ℕ → ℝ → ENNReal := fun n θ => ENNReal.ofReal (F θ - fn n θ) with hg
  have hpt : ∀ᵐ θ ∂μ, ENNReal.ofReal (F θ - f θ) ≤ liminf (fun n => g n θ) atTop := by
    filter_upwards [hae] with θ hθ
    have hw1 : circleMap 0 1 θ ≠ 1 := circleMap_zero_ne_one zero_le_one le_rfl hθ
    have hcont : Tendsto (fun n => Φ (circleMap 0 (rr n) θ)) atTop
        (𝓝 (Φ (circleMap 0 1 θ))) := by
      have hc : Continuous (fun r : ℝ => circleMap 0 r θ) := by unfold circleMap; fun_prop
      exact (hanAt _ hw1).continuousAt.tendsto.comp ((hc.tendsto 1).comp hrr_tend)
    rcases eq_or_ne (Φ (circleMap 0 1 θ)) 0 with h0 | h0
    · have hfθ : f θ = 0 := by simp only [hf, h0, norm_zero, Real.log_zero]
      refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
      have hn0 : Tendsto (fun n => ‖Φ (circleMap 0 (rr n) θ)‖) atTop (𝓝 0) := by
        have := hcont.norm
        rwa [h0, norm_zero] at this
      filter_upwards [hn0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
      apply ENNReal.ofReal_le_ofReal
      have : fn n θ ≤ 0 := Real.log_nonpos (norm_nonneg _) hn.le
      rw [hfθ]
      linarith
    · have hlog : Tendsto (fun n => fn n θ) atTop (𝓝 (f θ)) :=
        (Real.continuousAt_log (norm_ne_zero_iff.mpr h0)).tendsto.comp hcont.norm
      have hgt : Tendsto (fun n => g n θ) atTop (𝓝 (ENNReal.ofReal (F θ - f θ))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.sub hlog)
      rw [hgt.liminf_eq]
  have hFmeas : Measurable F :=
    measurable_const.sub (measurable_const.mul (Real.measurable_log.comp Real.measurable_sin))
  have hgmeas : ∀ n, Measurable (g n) := by
    intro n
    refine ENNReal.measurable_ofReal.comp (hFmeas.sub ?_)
    exact Real.measurable_log.comp
      (hmeas.comp (continuous_circleMap 0 (rr n)).measurable).norm
  have hlint_n : ∀ n, (∀ u ∈ U, ‖u‖ < rr n) →
      ∫⁻ θ, g n θ ∂μ ≤ ENNReal.ofReal (∫ θ, F θ ∂μ
        - 2 * π * (∑ u ∈ U, Real.log (rr n / ‖u‖) + Real.log ‖Φ 0‖)) := by
    intro n hn
    show ∫⁻ θ, ENNReal.ofReal (F θ - fn n θ) ∂μ ≤ _
    have hint : Integrable (fun θ => F θ - fn n θ) μ := hFint.sub (hfnint n)
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (hae.mono fun θ hθ => sub_nonneg.mpr (hFdom _ (hrr0 n).le (hrr1 n).le θ hθ))]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_sub hFint (hfnint n)]
    linarith [hJn n hn]
  have hfatou : ∫⁻ θ, ENNReal.ofReal (F θ - f θ) ∂μ ≤ ENNReal.ofReal (∫ θ, F θ ∂μ - 2 * π * J) := by
    calc ∫⁻ θ, ENNReal.ofReal (F θ - f θ) ∂μ
        ≤ ∫⁻ θ, liminf (fun n => g n θ) atTop ∂μ := lintegral_mono_ae hpt
      _ ≤ liminf (fun n => ∫⁻ θ, g n θ ∂μ) atTop := lintegral_liminf_le hgmeas
      _ ≤ liminf (fun n => ENNReal.ofReal (∫ θ, F θ ∂μ
            - 2 * π * (∑ u ∈ U, Real.log (rr n / ‖u‖) + Real.log ‖Φ 0‖))) atTop :=
          Filter.liminf_le_liminf (hev.mono fun n hn => hlint_n n hn)
      _ = ENNReal.ofReal (∫ θ, F θ ∂μ - 2 * π * J) :=
          ((ENNReal.continuous_ofReal.tendsto _).comp
            (tendsto_const_nhds.sub (hJtend.const_mul (2 * π)))).liminf_eq
  have hfF : ∀ᵐ θ ∂μ, f θ ≤ F θ := hae.mono fun θ hθ => hFdom 1 zero_le_one le_rfl θ hθ
  have hfmeas : AEStronglyMeasurable f μ :=
    (Real.measurable_log.comp
      (hmeas.comp (continuous_circleMap 0 1).measurable).norm).aestronglyMeasurable
  have hdiff_int : Integrable (fun θ => F θ - f θ) μ := by
    refine ⟨hFint.aestronglyMeasurable.sub hfmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (hfF.mono fun θ h => sub_nonneg.mpr h)]
    exact lt_of_le_of_lt hfatou ENNReal.ofReal_lt_top
  have hfint : Integrable f μ :=
    (hFint.sub hdiff_int).congr (Filter.Eventually.of_forall fun θ => by simp)
  have hdiff_le : ∫ θ, (F θ - f θ) ∂μ ≤ ∫ θ, F θ ∂μ - 2 * π * J := by
    rw [integral_eq_lintegral_of_nonneg_ae (hfF.mono fun θ h => sub_nonneg.mpr h)
      hdiff_int.aestronglyMeasurable]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfatou
    rwa [ENNReal.toReal_ofReal (by linarith [hFJ])] at this
  have hmain : 2 * π * J ≤ ∫ θ, f θ ∂μ := by
    rw [integral_sub hFint hfint] at hdiff_le
    linarith
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hπ.le).mpr hfint, ?_⟩
  rw [circleAverage_def, intervalIntegral.integral_of_le hπ.le, smul_eq_mul]
  rw [le_inv_mul_iff₀ hπ]
  exact hmain

/-- **Jensen's inequality on the boundary circle for `G`.**  `θ ↦ log |G(e^{iθ})|` is integrable,
and `Σ_u log (1/|u|) ≤ (1/2π) ∫_0^{2π} log |G(e^{iθ})| dθ` for finitely many zeros `u` of `G` in
the open unit disc. -/
theorem circleIntegrable_and_sum_log_le_circleAverage_zetaDisc {U : Finset ℂ}
    (hU : ∀ u ∈ U, zetaDisc u = 0 ∧ ‖u‖ < 1) :
    CircleIntegrable (fun w => Real.log ‖zetaDisc w‖) 0 1 ∧
      ∑ u ∈ U, Real.log (1 / ‖u‖) ≤ circleAverage (fun w => Real.log ‖zetaDisc w‖) 0 1 := by
  obtain ⟨A, _, hA⟩ := exists_log_norm_zetaDisc_le
  have h := circleIntegrable_and_sum_log_add_le_circleAverage differentiableOn_zetaDisc
    measurable_zetaDisc (by rw [zetaDisc_zero]; exact one_ne_zero) ⟨A, hA⟩ hU
  rwa [zetaDisc_zero, norm_one, Real.log_one, add_zero] at h

end

end RHTower
