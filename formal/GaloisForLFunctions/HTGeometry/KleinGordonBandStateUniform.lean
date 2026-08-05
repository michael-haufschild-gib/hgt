import GaloisForLFunctions.HTGeometry.KleinGordonStateDifference

/-!
# The state converges uniformly on an observation window

Statement 246 makes the field approximation uniform on a window; statements 243–244 make the state and
the energy converge, but only at each time separately, because they were obtained by dominated
convergence on the Duhamel integrals and that gives nothing uniform.

The state estimate of the previous file repairs this in one stroke. Its right-hand side is the same
monotone expression as in the field case — an accumulated norm and an increasing exponential — so its
value at the endpoint majorises the error over the whole window, and the majorant is exactly the one
already shown to vanish. Hence the state, and with it the gradient, the velocity and the energy,
converges uniformly on `[0, T]`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section BandStateUniform

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- **One cut-off bounds the state over the whole window.** -/
theorem norm_kgFieldState_band_sub_le_endpoint (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g y : Lp ℂ 2 (volume : Measure E)) (R : ℝ) {T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖kgFieldState (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t
        - kgFieldState W₀ g y t‖
      ≤ (‖kgLowPassOp R g - g‖ + ‖kgLowPassOp R y - y‖
          + ∫ s in (0 : ℝ)..T,
              ‖(kgBandOp W₀ R - W₀) (kgFieldMild W₀ (kgFreqInvOp g) y s)‖) * Real.exp (b * T) := by
  have hcu : Continuous (kgFieldMild W₀ (kgFreqInvOp g) y) :=
    continuous_kgFieldMild hb0 hW _ _
  have hsrc : Continuous fun s : ℝ =>
      ‖(kgBandOp W₀ R - W₀) (kgFieldMild W₀ (kgFreqInvOp g) y s)‖ :=
    (((kgBandOp W₀ R - W₀).continuous.comp hcu)).norm
  have hI : IntervalIntegrable
      (fun s : ℝ => ‖(kgBandOp W₀ R - W₀) (kgFieldMild W₀ (kgFreqInvOp g) y s)‖) volume 0 T :=
    hsrc.intervalIntegrable 0 T
  have hmono : (∫ s in (0 : ℝ)..t, ‖(kgBandOp W₀ R - W₀) (kgFieldMild W₀ (kgFreqInvOp g) y s)‖)
      ≤ ∫ s in (0 : ℝ)..T, ‖(kgBandOp W₀ R - W₀) (kgFieldMild W₀ (kgFreqInvOp g) y s)‖ :=
    intervalIntegral.integral_mono_interval le_rfl ht0 htT
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) hI
  have hIT0 : (0 : ℝ)
      ≤ ∫ s in (0 : ℝ)..T, ‖(kgBandOp W₀ R - W₀) (kgFieldMild W₀ (kgFreqInvOp g) y s)‖ :=
    intervalIntegral.integral_nonneg (ht0.trans htT) fun _ _ => norm_nonneg _
  have hexp : Real.exp (b * t) ≤ Real.exp (b * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htT hb0)
  have hdata : ‖kgPair E (kgLowPassOp R g - g, kgLowPassOp R y - y)‖
      ≤ ‖kgLowPassOp R g - g‖ + ‖kgLowPassOp R y - y‖ :=
    norm_kgPair_le (E := E) (kgLowPassOp R g - g, kgLowPassOp R y - y)
  have hkey := norm_kgFieldState_sub_general_le hb0 (norm_kgBandOp_le hb0 hW R) hW
    (kgLowPassOp R g) (kgLowPassOp R y) g y ht0
  refine hkey.trans ?_
  refine mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by positivity)

/-- **The state converges uniformly on a finite observation window.** -/
theorem tendstoUniformlyOn_kgFieldState_band (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g y : Lp ℂ 2 (volume : Measure E)) (T : ℝ) :
    TendstoUniformlyOn
      (fun R : ℝ => fun t : ℝ =>
        kgFieldState (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t)
      (kgFieldState W₀ g y) atTop (Set.Icc 0 T) := by
  have hcu : Continuous (kgFieldMild W₀ (kgFreqInvOp g) y) :=
    continuous_kgFieldMild hb0 hW _ _
  have h1 : Tendsto (fun R : ℝ => ‖kgLowPassOp R g - g‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).mp (tendsto_kgLowPassOp_apply g)
  have h2 : Tendsto (fun R : ℝ => ‖kgLowPassOp R y - y‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).mp (tendsto_kgLowPassOp_apply y)
  have h3 := tendsto_integral_kgBandOp_sub hb0 hW (kgFieldMild W₀ (kgFreqInvOp g) y) hcu T
  have hg : Tendsto (fun R : ℝ => (‖kgLowPassOp R g - g‖ + ‖kgLowPassOp R y - y‖
      + ∫ s in (0 : ℝ)..T, ‖(kgBandOp W₀ R - W₀) (kgFieldMild W₀ (kgFreqInvOp g) y s)‖)
        * Real.exp (b * T)) atTop (𝓝 0) := by
    have hadd := (h1.add h2).add h3
    have hmul := hadd.mul_const (Real.exp (b * T))
    simpa using hmul
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hg.eventually_lt_const hε] with R hR t ht
  have hle := norm_kgFieldState_band_sub_le_endpoint hb0 hW g y R ht.1 ht.2
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt hle hR

/-- **The gradient converges uniformly on a finite observation window.** -/
theorem tendstoUniformlyOn_kgFieldGrad_band (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g y : Lp ℂ 2 (volume : Measure E)) (T : ℝ) :
    TendstoUniformlyOn
      (fun R : ℝ => fun t : ℝ =>
        kgFieldGrad (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t)
      (kgFieldGrad W₀ g y) atTop (Set.Icc 0 T) := by
  have hstate := tendstoUniformlyOn_kgFieldState_band hb0 hW g y T
  rw [Metric.tendstoUniformlyOn_iff] at hstate ⊢
  intro ε hε
  filter_upwards [hstate ε hε] with R hR t ht
  refine lt_of_le_of_lt ?_ (hR t ht)
  rw [dist_eq_norm, dist_eq_norm]
  have hfst : kgFieldGrad W₀ g y t
      - kgFieldGrad (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t
      = (kgFieldState W₀ g y t
          - kgFieldState (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t).fst := by
    rw [← kgFst_apply, map_sub]
    rfl
  rw [hfst]
  exact WithLp.norm_fst_le _ _

/-- **The velocity converges uniformly on a finite observation window.** -/
theorem tendstoUniformlyOn_kgFieldVel_band (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g y : Lp ℂ 2 (volume : Measure E)) (T : ℝ) :
    TendstoUniformlyOn
      (fun R : ℝ => fun t : ℝ =>
        kgFieldVel (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t)
      (kgFieldVel W₀ g y) atTop (Set.Icc 0 T) := by
  have hstate := tendstoUniformlyOn_kgFieldState_band hb0 hW g y T
  rw [Metric.tendstoUniformlyOn_iff] at hstate ⊢
  intro ε hε
  filter_upwards [hstate ε hε] with R hR t ht
  refine lt_of_le_of_lt ?_ (hR t ht)
  rw [dist_eq_norm, dist_eq_norm]
  have hsnd : kgFieldVel W₀ g y t
      - kgFieldVel (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t
      = (kgFieldState W₀ g y t
          - kgFieldState (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t).snd := by
    rw [← kgSnd_apply, map_sub]
    rfl
  rw [hsnd]
  exact WithLp.norm_snd_le _ _

end BandStateUniform

end GaloisForLFunctions.HTGeometry
