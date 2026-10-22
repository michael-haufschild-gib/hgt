import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonBandStateConvergence

/-!
# The band approximation is uniform on a finite observation window

Statement 236 is a limit at each fixed time. A measurement is made over a window, not at a point, so
what an experiment needs is one cut-off that works for the whole window at once.

The estimate of statement 234 gives it for free. Its right-hand side is monotone in the time: the
integrand is a norm, so the accumulated term grows with the endpoint, and the exponential grows with
it too. Evaluating the bound at the right endpoint of the window therefore majorises the error at
every time in the window by a single quantity, and that quantity tends to zero. Hence

`sup_{0 ≤ t ≤ T} ‖u_R(t) − u(t)‖ → 0`   as `R → ∞`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Uniform

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- **One cut-off bounds the whole window.** The error of the band solution at every time of
`[0, T]` is majorised by the value of the estimate of statement 234 at the endpoint `T`. -/
theorem norm_kgFieldMild_band_sub_le_endpoint (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (x y : Lp ℂ 2 (volume : Measure E)) (R : ℝ) {T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) t
        - kgFieldMild W₀ x y t‖
      ≤ (‖kgLowPassOp R x - x‖ + ‖kgLowPassOp R y - y‖
          + ∫ s in (0 : ℝ)..T, ‖(kgBandOp W₀ R - W₀) (kgFieldMild W₀ x y s)‖)
        * Real.exp (b * T) := by
  have hcu : Continuous (kgFieldMild W₀ x y) := continuous_kgFieldMild hb0 hW x y
  have hsrc : Continuous fun s : ℝ => ‖(kgBandOp W₀ R - W₀) (kgFieldMild W₀ x y s)‖ :=
    (((kgBandOp W₀ R - W₀).continuous.comp hcu)).norm
  have hI : IntervalIntegrable
      (fun s : ℝ => ‖(kgBandOp W₀ R - W₀) (kgFieldMild W₀ x y s)‖) volume 0 T :=
    hsrc.intervalIntegrable 0 T
  have hmono : (∫ s in (0 : ℝ)..t, ‖(kgBandOp W₀ R - W₀) (kgFieldMild W₀ x y s)‖)
      ≤ ∫ s in (0 : ℝ)..T, ‖(kgBandOp W₀ R - W₀) (kgFieldMild W₀ x y s)‖ :=
    intervalIntegral.integral_mono_interval le_rfl ht0 htT
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) hI
  have hIT0 : (0 : ℝ) ≤ ∫ s in (0 : ℝ)..T, ‖(kgBandOp W₀ R - W₀) (kgFieldMild W₀ x y s)‖ :=
    intervalIntegral.integral_nonneg (ht0.trans htT) fun _ _ => norm_nonneg _
  have hexp : Real.exp (b * t) ≤ Real.exp (b * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htT hb0)
  have hkey := norm_kgFieldMild_sub_general_le hb0 (norm_kgBandOp_le hb0 hW R) hW
    (kgLowPassOp R x) (kgLowPassOp R y) x y ht0
  refine hkey.trans ?_
  refine mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by positivity)

/-- **The band approximation is uniform on a finite observation window.** One cut-off suffices for
the whole window: the band solutions converge to the true solution uniformly on `[0, T]`. -/
theorem tendstoUniformlyOn_kgFieldMild_band (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (x y : Lp ℂ 2 (volume : Measure E)) (T : ℝ) :
    TendstoUniformlyOn
      (fun R : ℝ => fun t : ℝ =>
        kgFieldMild (kgBandOp W₀ R) (kgLowPassOp R x) (kgLowPassOp R y) t)
      (kgFieldMild W₀ x y) atTop (Set.Icc 0 T) := by
  have hcu : Continuous (kgFieldMild W₀ x y) := continuous_kgFieldMild hb0 hW x y
  have h1 : Tendsto (fun R : ℝ => ‖kgLowPassOp R x - x‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).mp (tendsto_kgLowPassOp_apply x)
  have h2 : Tendsto (fun R : ℝ => ‖kgLowPassOp R y - y‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).mp (tendsto_kgLowPassOp_apply y)
  have h3 := tendsto_integral_kgBandOp_sub hb0 hW (kgFieldMild W₀ x y) hcu T
  have hg : Tendsto (fun R : ℝ => (‖kgLowPassOp R x - x‖ + ‖kgLowPassOp R y - y‖
      + ∫ s in (0 : ℝ)..T, ‖(kgBandOp W₀ R - W₀) (kgFieldMild W₀ x y s)‖)
        * Real.exp (b * T)) atTop (𝓝 0) := by
    have hadd := (h1.add h2).add h3
    have hmul := hadd.mul_const (Real.exp (b * T))
    simpa using hmul
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hg.eventually_lt_const hε] with R hR t ht
  have hle := norm_kgFieldMild_band_sub_le_endpoint hb0 hW x y R ht.1 ht.2
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt hle hR

end Uniform

end GaloisForLFunctions.HTGeometry
