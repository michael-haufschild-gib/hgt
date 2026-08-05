import GaloisForLFunctions.HTGeometry.KleinGordonTimeBandDifference

/-!
# The band approximation of a moving background is faithful, and uniform on a window

The compressed moving background `P_RW(t)P_R` converges to `W(t)` strongly at each time and never in
norm, so the Lipschitz estimate is again useless and the sharp estimate of the previous file is what
carries the limit. The argument is the autonomous one with the time carried along: the discrepancy
`(P_RW(s)P_R − W(s))u(s)` vanishes pointwise and is dominated by `2‖W‖‖u(s)‖` on the interval, so its
accumulated value vanishes, and the difference estimate turns that into

`u_R(t) → u(t)`   for every time,

uniformly on every finite observation window, since the bound is monotone in its endpoint.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section ApproximationT

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- **The accumulated discrepancy of the moving compressions vanishes.** -/
theorem tendsto_integral_kgBandOpT_sub (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (u : ℝ → Lp ℂ 2 (volume : Measure E)) (hu : Continuous u) (t : ℝ) :
    Tendsto (fun R : ℝ => ∫ s in (0 : ℝ)..t, ‖(kgBandOpT W R s - W s) (u s)‖) atTop (𝓝 0) := by
  have hbound : IntervalIntegrable (fun s : ℝ => 2 * b * ‖u s‖) volume 0 t :=
    (continuous_const.mul hu.norm).intervalIntegrable 0 t
  have hWu : Continuous fun s : ℝ => W s (u s) :=
    continuous_of_strong_comp hWb hWs continuous_id hu
  have hmeas : ∀ R : ℝ, AEStronglyMeasurable
      (fun s : ℝ => ‖(kgBandOpT W R s - W s) (u s)‖) (volume.restrict (Set.uIoc 0 t)) := by
    intro R
    have hBu : Continuous fun s : ℝ => kgBandOpT W R s (u s) :=
      continuous_of_strong_comp (norm_kgBandOpT_le hb0 hWb R)
        (continuous_kgBandOpT_apply hWs R) continuous_id hu
    refine ((hBu.sub hWu).norm.congr fun s => ?_).aestronglyMeasurable
    simp only [Pi.sub_apply, sub_apply]
  have hdom : ∀ R : ℝ, ∀ᵐ s : ℝ, s ∈ Set.uIoc 0 t →
      ‖‖(kgBandOpT W R s - W s) (u s)‖‖ ≤ 2 * b * ‖u s‖ := by
    intro R
    filter_upwards with s _
    have h1 : ‖(kgBandOpT W R s - W s) (u s)‖
        ≤ ‖kgBandOpT W R s (u s)‖ + ‖W s (u s)‖ := by
      rw [sub_apply]
      exact norm_sub_le _ _
    have h2 : ‖kgBandOpT W R s (u s)‖ ≤ b * ‖u s‖ :=
      (kgBandOpT W R s).le_of_opNorm_le (norm_kgBandOpT_le hb0 hWb R s) _
    have h3 : ‖W s (u s)‖ ≤ b * ‖u s‖ := (W s).le_of_opNorm_le (hWb s) _
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    linarith
  have hlim : ∀ᵐ s : ℝ, s ∈ Set.uIoc 0 t →
      Tendsto (fun R : ℝ => ‖(kgBandOpT W R s - W s) (u s)‖) atTop (𝓝 0) := by
    filter_upwards with s _
    have h0 := (tendsto_iff_norm_sub_tendsto_zero).mp (tendsto_kgBandOpT_apply W s (u s))
    refine h0.congr fun R => ?_
    rw [sub_apply]
  have hres := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun s : ℝ => 2 * b * ‖u s‖) (l := (atTop : Filter ℝ))
    (F := fun R : ℝ => fun s : ℝ => ‖(kgBandOpT W R s - W s) (u s)‖) (f := fun _ : ℝ => (0 : ℝ))
    (Eventually.of_forall hmeas) (Eventually.of_forall hdom) hbound hlim
  simpa using hres

/-- **One cut-off bounds the whole window**, for a moving background. -/
theorem norm_kgFieldMildT_band_sub_le_endpoint (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (x y : Lp ℂ 2 (volume : Measure E)) (R : ℝ) {T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) t
        - kgFieldMildT W x y t‖
      ≤ (‖kgLowPassOp R x - x‖ + ‖kgLowPassOp R y - y‖
          + ∫ s in (0 : ℝ)..T, ‖(kgBandOpT W R s - W s) (kgFieldMildT W x y s)‖)
        * Real.exp (b * T) := by
  have hcu : Continuous (kgFieldMildT W x y) := continuous_kgFieldMildT hb0 hWb hWs x y
  have hWu : Continuous fun s : ℝ => W s (kgFieldMildT W x y s) :=
    continuous_of_strong_comp hWb hWs continuous_id hcu
  have hBu : Continuous fun s : ℝ => kgBandOpT W R s (kgFieldMildT W x y s) :=
    continuous_of_strong_comp (norm_kgBandOpT_le hb0 hWb R)
      (continuous_kgBandOpT_apply hWs R) continuous_id hcu
  have hsrc : Continuous fun s : ℝ => ‖(kgBandOpT W R s - W s) (kgFieldMildT W x y s)‖ := by
    refine (hBu.sub hWu).norm.congr fun s => ?_
    simp only [Pi.sub_apply, sub_apply]
  have hI : IntervalIntegrable
      (fun s : ℝ => ‖(kgBandOpT W R s - W s) (kgFieldMildT W x y s)‖) volume 0 T :=
    hsrc.intervalIntegrable 0 T
  have hmono : (∫ s in (0 : ℝ)..t, ‖(kgBandOpT W R s - W s) (kgFieldMildT W x y s)‖)
      ≤ ∫ s in (0 : ℝ)..T, ‖(kgBandOpT W R s - W s) (kgFieldMildT W x y s)‖ :=
    intervalIntegral.integral_mono_interval le_rfl ht0 htT
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) hI
  have hIT0 : (0 : ℝ)
      ≤ ∫ s in (0 : ℝ)..T, ‖(kgBandOpT W R s - W s) (kgFieldMildT W x y s)‖ :=
    intervalIntegral.integral_nonneg (ht0.trans htT) fun _ _ => norm_nonneg _
  have hexp : Real.exp (b * t) ≤ Real.exp (b * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htT hb0)
  have hkey := norm_kgFieldMildT_sub_general_le hb0
    (fun r => norm_kgBandOpT_le hb0 hWb R r) (continuous_kgBandOpT_apply hWs R) hWb hWs
    (kgLowPassOp R x) (kgLowPassOp R y) x y ht0
  refine hkey.trans ?_
  refine mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by positivity)

/-- **The band solutions converge to the true solution** in a moving background, forwards in time. -/
theorem tendsto_kgFieldMildT_band_of_nonneg (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (x y : Lp ℂ 2 (volume : Measure E)) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun R : ℝ => kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) t)
      atTop (𝓝 (kgFieldMildT W x y t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hcu : Continuous (kgFieldMildT W x y) := continuous_kgFieldMildT hb0 hWb hWs x y
  have hle : ∀ R : ℝ,
      ‖kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) t
          - kgFieldMildT W x y t‖
        ≤ (‖kgLowPassOp R x - x‖ + ‖kgLowPassOp R y - y‖
            + ∫ s in (0 : ℝ)..t, ‖(kgBandOpT W R s - W s) (kgFieldMildT W x y s)‖)
          * Real.exp (b * t) := fun R =>
    norm_kgFieldMildT_band_sub_le_endpoint hb0 hWb hWs x y R ht le_rfl
  have h1 : Tendsto (fun R : ℝ => ‖kgLowPassOp R x - x‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).mp (tendsto_kgLowPassOp_apply x)
  have h2 : Tendsto (fun R : ℝ => ‖kgLowPassOp R y - y‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).mp (tendsto_kgLowPassOp_apply y)
  have h3 := tendsto_integral_kgBandOpT_sub hb0 hWb hWs (kgFieldMildT W x y) hcu t
  have hsum : Tendsto (fun R : ℝ => (‖kgLowPassOp R x - x‖ + ‖kgLowPassOp R y - y‖
      + ∫ s in (0 : ℝ)..t, ‖(kgBandOpT W R s - W s) (kgFieldMildT W x y s)‖)
        * Real.exp (b * t)) atTop (𝓝 0) := by
    have hadd := (h1.add h2).add h3
    have hmul := hadd.mul_const (Real.exp (b * t))
    simpa using hmul
  exact squeeze_zero (fun _ => norm_nonneg _) hle hsum

/-- **The band solutions converge to the true solution** in a moving background, at every time. -/
theorem tendsto_kgFieldMildT_band (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    Tendsto (fun R : ℝ => kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) t)
      atTop (𝓝 (kgFieldMildT W x y t)) := by
  rcases le_total (0 : ℝ) t with ht | ht
  · exact tendsto_kgFieldMildT_band_of_nonneg hb0 hWb hWs x y ht
  · have hneg : (0 : ℝ) ≤ -t := by linarith
    have hVb : ∀ r : ℝ, ‖W (-r)‖ ≤ b := fun r => hWb (-r)
    have hVs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W (-r) z := fun z =>
      (hWs z).comp continuous_neg
    have hkey := tendsto_kgFieldMildT_band_of_nonneg hb0 hVb hVs x (-y) hneg
    have hrefl : ∀ R : ℝ,
        kgFieldMildT (kgBandOpT (fun r : ℝ => W (-r)) R) (kgLowPassOp R x)
            (-(kgLowPassOp R y)) (-t)
          = kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) t := by
      intro R
      have hRb : ∀ r : ℝ, ‖kgBandOpT W R r‖ ≤ b := norm_kgBandOpT_le hb0 hWb R
      have hRs : ∀ z : Lp ℂ 2 (volume : Measure E),
          Continuous fun r : ℝ => kgBandOpT W R r z := continuous_kgBandOpT_apply hWs R
      have h := kgFieldMildT_neg hb0 hRb hRs (kgLowPassOp R x) (kgLowPassOp R y) (-t)
      rw [neg_neg] at h
      exact h.symm
    have hrefl0 : kgFieldMildT (fun r : ℝ => W (-r)) x (-y) (-t) = kgFieldMildT W x y t := by
      have h := kgFieldMildT_neg hb0 hWb hWs x y (-t)
      rw [neg_neg] at h
      exact h.symm
    rw [← hrefl0]
    refine hkey.congr fun R => ?_
    rw [← hrefl R, map_neg]

/-- **The band approximation of a moving background is uniform on a finite observation window.** -/
theorem tendstoUniformlyOn_kgFieldMildT_band (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (x y : Lp ℂ 2 (volume : Measure E)) (T : ℝ) :
    TendstoUniformlyOn
      (fun R : ℝ => fun t : ℝ =>
        kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) t)
      (kgFieldMildT W x y) atTop (Set.Icc 0 T) := by
  have hcu : Continuous (kgFieldMildT W x y) := continuous_kgFieldMildT hb0 hWb hWs x y
  have h1 : Tendsto (fun R : ℝ => ‖kgLowPassOp R x - x‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).mp (tendsto_kgLowPassOp_apply x)
  have h2 : Tendsto (fun R : ℝ => ‖kgLowPassOp R y - y‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).mp (tendsto_kgLowPassOp_apply y)
  have h3 := tendsto_integral_kgBandOpT_sub hb0 hWb hWs (kgFieldMildT W x y) hcu T
  have hg : Tendsto (fun R : ℝ => (‖kgLowPassOp R x - x‖ + ‖kgLowPassOp R y - y‖
      + ∫ s in (0 : ℝ)..T, ‖(kgBandOpT W R s - W s) (kgFieldMildT W x y s)‖)
        * Real.exp (b * T)) atTop (𝓝 0) := by
    have hadd := (h1.add h2).add h3
    have hmul := hadd.mul_const (Real.exp (b * T))
    simpa using hmul
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hg.eventually_lt_const hε] with R hR t ht
  have hle := norm_kgFieldMildT_band_sub_le_endpoint hb0 hWb hWs x y R ht.1 ht.2
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt hle hR

end ApproximationT

end GaloisForLFunctions.HTGeometry
