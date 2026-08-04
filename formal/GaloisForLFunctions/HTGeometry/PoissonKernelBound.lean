import Mathlib

/-!
# A uniform bound for the Poisson kernel

On the ball of radius `r` inside the circle of radius `R`, the Poisson kernel is at most
`(R + r)/(R - r)`.  This is the quantitative input that converts the Poisson representation of a
harmonic function into the classical comparison between the maximum modulus and the circle average:
`log M(r) ≤ ((R+r)/(R-r)) · m(R)`.
-/

open Complex Metric InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

/-- **The Poisson kernel at a point.** -/
theorem poissonKernel_le_of_mem {c w z : ℂ} {R : ℝ} (hz : z ∈ sphere c R) (hw : w ∈ ball c R) :
    poissonKernel c w z ≤ (R + ‖w - c‖) / (R - ‖w - c‖) := by
  have h := re_herglotzRieszKernel_le hz hw
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  simpa [herglotzRieszKernel] using h

/-- The comparison `(R + a)/(R - a) ≤ (R + r)/(R - r)` for `0 ≤ a ≤ r < R`. -/
theorem div_add_sub_mono {R a r : ℝ} (ha : 0 ≤ a) (har : a ≤ r) (hrR : r < R) :
    (R + a) / (R - a) ≤ (R + r) / (R - r) := by
  have hRa : 0 < R - a := by linarith
  have hRr : 0 < R - r := by linarith
  rw [div_le_div_iff₀ hRa hRr]
  nlinarith [ha, har, hrR]

/-- **The Poisson kernel on a smaller ball.** -/
theorem poissonKernel_le {c w z : ℂ} {R r : ℝ} (hz : z ∈ sphere c R) (hw : w ∈ ball c R)
    (hwr : ‖w - c‖ ≤ r) (hrR : r < R) :
    poissonKernel c w z ≤ (R + r) / (R - r) :=
  le_trans (poissonKernel_le_of_mem hz hw) (div_add_sub_mono (norm_nonneg _) hwr hrR)

/-! ## The Poisson representation of `log ‖f‖` -/

/-- `log ‖f‖` is harmonic wherever `f` is analytic and nonzero. -/
theorem harmonicOnNhd_log_norm {f : ℂ → ℂ} {S : Set ℂ}
    (hf : AnalyticOnNhd ℂ f S) (h0 : ∀ z ∈ S, f z ≠ 0) :
    HarmonicOnNhd (fun z => Real.log ‖f z‖) S :=
  fun z hz => (hf z hz).harmonicAt_log_norm (h0 z hz)

/-- **The Poisson representation of the log-modulus.**  For a zero-free analytic function, the
log-modulus at an interior point is the Poisson-weighted average of its boundary values. -/
theorem circleAverage_poissonKernel_log_norm {f : ℂ → ℂ} {c w : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (h0 : ∀ z ∈ closedBall c R, f z ≠ 0)
    (hw : w ∈ ball c R) :
    Real.circleAverage (poissonKernel c w • fun z => Real.log ‖f z‖) c R = Real.log ‖f w‖ :=
  HarmonicOnNhd.circleAverage_poissonKernel_smul (harmonicOnNhd_log_norm hf h0) hw

/-! ## The Poisson upper bound -/

/-- The Poisson kernel is nonnegative on the sphere, from the lower Herglotz--Riesz estimate. -/
theorem poissonKernel_nonneg {c w z : ℂ} {R : ℝ} (hz : z ∈ sphere c R) (hw : w ∈ ball c R) :
    0 ≤ poissonKernel c w z := by
  have h := le_re_herglotzRieszKernel hz hw
  have hR : 0 < R := by
    rcases Metric.nonempty_ball.mp ⟨w, hw⟩ with h'
    exact h'
  have hwR : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  have hnum : 0 ≤ R - ‖w - c‖ := by linarith
  have hden : 0 < R + ‖w - c‖ := by
    have := norm_nonneg (w - c)
    linarith
  have hfrac : 0 ≤ (R - ‖w - c‖) / (R + ‖w - c‖) := div_nonneg hnum (le_of_lt hden)
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  simpa [herglotzRieszKernel] using le_trans hfrac h

/-- The Poisson kernel is continuous on the sphere, away from the interior point. -/
theorem continuousOn_poissonKernel {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R) :
    ContinuousOn (poissonKernel c w) (sphere c R) := by
  have hne : ∀ z ∈ sphere c R, ‖(z - c) - (w - c)‖ ^ 2 ≠ 0 := by
    intro z hz
    have hzc : ‖z - c‖ = R := by simpa [mem_sphere_iff_norm] using hz
    have hwc : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
    have hzw : z - w ≠ 0 := by
      intro hcon
      have : z = w := by
        have := sub_eq_zero.mp hcon
        exact this
      rw [this] at hzc
      linarith
    have hsub : (z - c) - (w - c) = z - w := by ring
    rw [hsub]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hzw)
  have hnum : ContinuousOn (fun z : ℂ => ‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) (sphere c R) := by
    fun_prop
  have hden : ContinuousOn (fun z : ℂ => ‖(z - c) - (w - c)‖ ^ 2) (sphere c R) := by
    fun_prop
  have heq : poissonKernel c w
      = fun z => (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖(z - c) - (w - c)‖ ^ 2 := by
    funext z
    exact poissonKernel_def c w z
  rw [heq]
  exact hnum.div hden hne

/-- The Poisson-weighted circle average of a continuous function is bounded by the maximal kernel
weight times the circle average of its positive part. -/
theorem circleAverage_poissonKernel_smul_le {c w : ℂ} {R r : ℝ} {u : ℂ → ℝ}
    (hw : w ∈ ball c R) (hwr : ‖w - c‖ ≤ r) (hrR : r < R)
    (hu : ContinuousOn u (sphere c R)) :
    Real.circleAverage (poissonKernel c w • u) c R
      ≤ (R + r) / (R - r) * Real.circleAverage (fun z => max (u z) 0) c R := by
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hwr
  have hR0 : 0 < R := lt_of_le_of_lt hr0 hrR
  have habs : |R| = R := abs_of_pos hR0
  have hK0 : 0 ≤ (R + r) / (R - r) := by
    have : 0 < R - r := by linarith
    positivity
  have hint₁ : CircleIntegrable (poissonKernel c w • u) c R :=
    ((continuousOn_poissonKernel hw).smul hu).circleIntegrable (le_of_lt hR0)
  have hmaxcont : Continuous fun t : ℝ => max t 0 := continuous_id.max continuous_const
  have hpos : ContinuousOn (fun z => max (u z) 0) (sphere c R) := hmaxcont.comp_continuousOn hu
  have hint₂ : CircleIntegrable (fun z => (R + r) / (R - r) * max (u z) 0) c R :=
    (continuousOn_const.mul hpos).circleIntegrable (le_of_lt hR0)
  have hpt : ∀ z ∈ sphere c |R|,
      (poissonKernel c w • u) z ≤ (R + r) / (R - r) * max (u z) 0 := by
    intro z hz
    rw [habs] at hz
    have hker0 : 0 ≤ poissonKernel c w z := poissonKernel_nonneg hz hw
    have hkerK : poissonKernel c w z ≤ (R + r) / (R - r) := poissonKernel_le hz hw hwr hrR
    have hval : (poissonKernel c w • u) z = poissonKernel c w z * u z := rfl
    rw [hval]
    rcases le_total 0 (u z) with hu0 | hu0
    · have hmax : max (u z) 0 = u z := max_eq_left hu0
      rw [hmax]
      exact mul_le_mul_of_nonneg_right hkerK hu0
    · have hmax : max (u z) 0 = 0 := max_eq_right hu0
      rw [hmax, mul_zero]
      exact mul_nonpos_of_nonneg_of_nonpos hker0 hu0
  calc Real.circleAverage (poissonKernel c w • u) c R
      ≤ Real.circleAverage (fun z => (R + r) / (R - r) * max (u z) 0) c R :=
        Real.circleAverage_mono hint₁ hint₂ hpt
    _ = (R + r) / (R - r) * Real.circleAverage (fun z => max (u z) 0) c R := by
        have hsmul : (fun z => (R + r) / (R - r) * max (u z) 0)
            = ((R + r) / (R - r)) • (fun z => max (u z) 0) := by
          funext z
          simp [Pi.smul_apply, smul_eq_mul]
        rw [hsmul, Real.circleAverage_smul, smul_eq_mul]

/-- **The Poisson upper bound for a zero-free analytic function.**  The log-modulus at an interior
point is at most the maximal Poisson weight times the proximity average on the boundary circle.
This is the quantitative form of `log M(r) ≤ ((R + r)/(R - r)) · m(R)` in the zero-free case. -/
theorem log_norm_le_poisson_proximity {f : ℂ → ℂ} {c w : ℂ} {R r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (h0 : ∀ z ∈ closedBall c R, f z ≠ 0)
    (hw : w ∈ ball c R) (hwr : ‖w - c‖ ≤ r) (hrR : r < R) :
    Real.log ‖f w‖
      ≤ (R + r) / (R - r) * Real.circleAverage (fun z => Real.posLog ‖f z‖) c R := by
  have hsub : sphere c R ⊆ closedBall c R := sphere_subset_closedBall
  have hfc : ContinuousOn f (sphere c R) := (hf.mono hsub).continuousOn
  have hu : ContinuousOn (fun z => Real.log ‖f z‖) (sphere c R) := by
    intro z hz
    have hz' : z ∈ closedBall c R := hsub hz
    exact (hfc z hz).norm.log (norm_ne_zero_iff.mpr (h0 z hz'))
  have hmax : (fun z => max (Real.log ‖f z‖) 0) = fun z => Real.posLog ‖f z‖ := by
    funext z
    rw [Real.posLog, max_comm]
  have hrep := circleAverage_poissonKernel_log_norm hf h0 hw
  have hbound := circleAverage_poissonKernel_smul_le (u := fun z => Real.log ‖f z‖) hw hwr hrR hu
  rw [hmax] at hbound
  rw [← hrep]
  exact hbound

/-- **The Poisson upper bound across a zero factorization.**  If `f = ∏ (· - a)^{m a} · g` on a
closed ball with `g` zero-free there, the log-modulus of `f` at an interior point is bounded by the
zero contribution plus the Poisson bound for `g`. -/
theorem log_norm_le_of_factor {f g : ℂ → ℂ} {c w : ℂ} {R r : ℝ} {T : Finset ℂ} {m : ℂ → ℕ}
    (hR : 1 ≤ R)
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hgfree : ∀ z ∈ closedBall c R, g z ≠ 0)
    (hTmem : ∀ a ∈ T, a ∈ closedBall c R)
    (hfac : ∀ z ∈ closedBall c R, f z = (∏ a ∈ T, (z - a) ^ (m a)) * g z)
    (hw : w ∈ ball c R) (hwr : ‖w - c‖ ≤ r) (hrR : r < R) :
    Real.log ‖f w‖ ≤ (∑ a ∈ T, (m a : ℝ)) * Real.log (2 * R)
      + (R + r) / (R - r) * Real.circleAverage (fun z => Real.posLog ‖g z‖) c R := by
  classical
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hwball : w ∈ closedBall c R := ball_subset_closedBall hw
  have hwc : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hwr
  have hK0 : 0 ≤ (R + r) / (R - r) := by
    have : 0 < R - r := by linarith
    positivity
  have hN0 : 0 ≤ ∑ a ∈ T, (m a : ℝ) := Finset.sum_nonneg fun a _ => Nat.cast_nonneg _
  have hlog2R : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  -- the Poisson bound for the zero-free factor
  have hgw := log_norm_le_poisson_proximity hg hgfree hw hwr hrR
  have hmnn : 0 ≤ Real.circleAverage (fun z => Real.posLog ‖g z‖) c R := by
    refine Real.circleAverage_nonneg_of_nonneg ?_
    intro x _
    exact Real.posLog_nonneg
  -- each zero is at distance at most `2R` from the interior point
  have hdist : ∀ a ∈ T, ‖w - a‖ ≤ 2 * R := by
    intro a ha
    have hac : ‖a - c‖ ≤ R := mem_closedBall_iff_norm.mp (hTmem a ha)
    calc ‖w - a‖ = ‖(w - c) - (a - c)‖ := by ring_nf
      _ ≤ ‖w - c‖ + ‖a - c‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  have hnorm : ‖f w‖ = (∏ a ∈ T, ‖w - a‖ ^ (m a)) * ‖g w‖ := by
    rw [hfac w hwball, norm_mul, norm_prod]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro a _
    rw [norm_pow]
  by_cases hfw : f w = 0
  · rw [hfw]
    simp only [norm_zero, Real.log_zero]
    have : 0 ≤ (R + r) / (R - r) * Real.circleAverage (fun z => Real.posLog ‖g z‖) c R :=
      mul_nonneg hK0 hmnn
    nlinarith [hN0, hlog2R]
  · have hgwne : ‖g w‖ ≠ 0 := norm_ne_zero_iff.mpr (hgfree w hwball)
    have hprodne : (∏ a ∈ T, ‖w - a‖ ^ (m a)) ≠ 0 := by
      intro hcon
      apply hfw
      have : ‖f w‖ = 0 := by rw [hnorm, hcon, zero_mul]
      exact norm_eq_zero.mp this
    have hfactorne : ∀ a ∈ T, ‖w - a‖ ^ (m a) ≠ 0 :=
      fun a ha => Finset.prod_ne_zero_iff.mp hprodne a ha
    have hlogbound : ∀ a ∈ T, Real.log ‖w - a‖ ≤ Real.log (2 * R) := by
      intro a ha
      rcases eq_or_lt_of_le (norm_nonneg (w - a)) with h | h
      · rw [← h, Real.log_zero]
        exact hlog2R
      · exact Real.log_le_log h (hdist a ha)
    have hlogsplit : Real.log ‖f w‖
        = ∑ a ∈ T, (m a : ℝ) * Real.log ‖w - a‖ + Real.log ‖g w‖ := by
      rw [hnorm, Real.log_mul hprodne hgwne]
      congr 1
      rw [Real.log_prod (fun a ha => hfactorne a ha)]
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [Real.log_pow]
    have hzero : ∑ a ∈ T, (m a : ℝ) * Real.log ‖w - a‖
        ≤ (∑ a ∈ T, (m a : ℝ)) * Real.log (2 * R) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum ?_
      intro a ha
      exact mul_le_mul_of_nonneg_left (hlogbound a ha) (Nat.cast_nonneg _)
    rw [hlogsplit]
    linarith [hzero, hgw]

end GaloisForLFunctions.HTGeometry
