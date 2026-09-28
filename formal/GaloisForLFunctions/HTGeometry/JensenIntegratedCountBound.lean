import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Jensen's formula with an integrated lower count

For an entire `f` with `f(c) ≠ 0`, Jensen's formula writes the circle average of `log|f|` as
`log|f(c)| + Σ_u m_u log(R/|c - u|)` over the zeros in `closedBall c R`. A layer-cake comparison
turns any lower count `φ(r) ≤ n_f(c, r)` on `[r₀, R]` into
`log|f(c)| + ∫_{r₀}^R φ(r)/r dr ≤ circleAverage log|f|`.

The angular average of the height on the circle `|z - c| = R` is at most `|Im c| + (2/π) R`, from
`∫₀^{2π} |sin θ| dθ = 4`; this is the sharp angular constant in divisor-capacity arguments.
-/

open MeasureTheory Set Metric Filter

namespace HTGeometry

noncomputable section

/-- `∫_{r₀}^R 1_{r ≥ d} r⁻¹ dr ≤ log(R/d)` for `0 < d ≤ R` and `0 < r₀ ≤ R`. -/
theorem integral_indicator_inv_le {d r₀ R : ℝ} (hd : 0 < d) (hdR : d ≤ R)
    (hR : r₀ ≤ R) :
    ∫ r in r₀..R, (Ici d).indicator (fun r : ℝ => r⁻¹) r ≤ Real.log (R / d) := by
  set a := max d r₀ with ha
  have ha0 : 0 < a := lt_max_of_lt_left hd
  have haR : a ≤ R := max_le hdR hR
  have hint : IntegrableOn (fun r : ℝ => r⁻¹) (Icc a R) :=
    (continuousOn_inv₀.mono fun r hr => (ha0.trans_le hr.1).ne').integrableOn_Icc
  rw [intervalIntegral.integral_of_le hR, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  calc ∫ r in Ici d ∩ Ioc r₀ R, r⁻¹ ≤ ∫ r in Icc a R, r⁻¹ := by
        refine setIntegral_mono_set hint ?_ ?_
        · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
          exact (inv_pos.mpr (ha0.trans_le hr.1)).le
        · refine LE.le.eventuallyLE fun r hr => ?_
          simp only [mem_inter_iff, mem_Ici, mem_Ioc] at hr
          exact ⟨max_le hr.1 hr.2.1.le, hr.2.2⟩
    _ = Real.log (R / a) := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le haR,
          integral_inv_of_pos ha0 (ha0.trans_le haR)]
    _ ≤ Real.log (R / d) := by
        refine Real.log_le_log (div_pos (ha0.trans_le haR) ha0) ?_
        exact div_le_div_of_nonneg_left (ha0.trans_le haR).le hd (le_max_left _ _)

theorem intervalIntegrable_indicator_inv {d r₀ R : ℝ} (hr₀ : 0 < r₀) (hR : r₀ ≤ R) :
    IntervalIntegrable ((Ici d).indicator (fun r : ℝ => r⁻¹)) volume r₀ R := by
  have h : IntervalIntegrable (fun r : ℝ => r⁻¹) volume r₀ R :=
    intervalIntegral.intervalIntegrable_inv (fun r hr => by
      rw [uIcc_of_le hR] at hr; exact (hr₀.trans_le hr.1).ne') continuousOn_id
  rw [intervalIntegrable_iff] at h ⊢
  exact h.indicator measurableSet_Ici

/-- **Layer-cake lower bound.** For weights `m_i ≥ 0` at distances `d_i ∈ (0, R]`, a lower count
`φ(r) ≤ Σ_{d_i ≤ r} m_i` on `[r₀, R]` gives `∫_{r₀}^R φ(r)/r dr ≤ Σ_i m_i log(R/d_i)`. -/
theorem integral_div_le_sum_log {ι : Type*} (S : Finset ι) (m d : ι → ℝ) {r₀ R : ℝ}
    (hr₀ : 0 < r₀) (hR : r₀ ≤ R) (hm : ∀ i ∈ S, 0 ≤ m i) (hd : ∀ i ∈ S, 0 < d i)
    (hdR : ∀ i ∈ S, d i ≤ R) {φ : ℝ → ℝ}
    (hφi : IntervalIntegrable (fun r => φ r / r) volume r₀ R)
    (hφ : ∀ r ∈ Icc r₀ R, φ r ≤ ∑ i ∈ S with d i ≤ r, m i) :
    ∫ r in r₀..R, φ r / r ≤ ∑ i ∈ S, m i * Real.log (R / d i) := by
  have hI : ∀ i ∈ S, IntervalIntegrable (fun r => m i * (Ici (d i)).indicator
      (fun r : ℝ => r⁻¹) r) volume r₀ R :=
    fun i _ => (intervalIntegrable_indicator_inv hr₀ hR).const_mul _
  calc ∫ r in r₀..R, φ r / r ≤ ∫ r in r₀..R, ∑ i ∈ S, m i * (Ici (d i)).indicator
        (fun r : ℝ => r⁻¹) r := by
        refine intervalIntegral.integral_mono_on hR hφi (by simpa only [Finset.sum_fn] using IntervalIntegrable.sum S hI) ?_
        intro r hr
        have hr0 : 0 < r := hr₀.trans_le hr.1
        have hsum : ∑ i ∈ S, m i * (Ici (d i)).indicator (fun r : ℝ => r⁻¹) r =
            (∑ i ∈ S with d i ≤ r, m i) / r := by
          rw [Finset.sum_filter, Finset.sum_div]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases h : d i ≤ r
          · rw [indicator_of_mem (show r ∈ Ici (d i) from h), if_pos h, div_eq_mul_inv]
          · rw [indicator_of_notMem (show r ∉ Ici (d i) from h), if_neg h, mul_zero, zero_div]
        rw [hsum]
        exact div_le_div_of_nonneg_right (hφ r hr) hr0.le
    _ = ∑ i ∈ S, m i * ∫ r in r₀..R, (Ici (d i)).indicator (fun r : ℝ => r⁻¹) r := by
        rw [intervalIntegral.integral_finsetSum hI]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [intervalIntegral.integral_const_mul]
    _ ≤ ∑ i ∈ S, m i * Real.log (R / d i) :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
          (integral_indicator_inv_le (hd i hi) (hdR i hi) hR) (hm i hi)

/-- **Jensen's formula with an integrated lower count.** If `f` is entire, `f c ≠ 0`, and
`φ(r)` is at most the number of zeros of `f` (with multiplicity) in `closedBall c r` for
`r ∈ [r₀, R]`, then `log|f(c)| + ∫_{r₀}^R φ(r)/r dr ≤` the circle average of `log|f|`. -/
theorem log_norm_add_integral_le_circleAverage {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    {c : ℂ} (hc : f c ≠ 0) {r₀ R : ℝ} (hr₀ : 0 < r₀) (hR : r₀ ≤ R) {φ : ℝ → ℝ}
    (hφi : IntervalIntegrable (fun r => φ r / r) volume r₀ R)
    (hφ : ∀ r ∈ Icc r₀ R, φ r ≤ ∑ᶠ u, (MeromorphicOn.divisor f (closedBall c r) u : ℝ)) :
    Real.log ‖f c‖ + ∫ r in r₀..R, φ r / r ≤ Real.circleAverage (fun z => Real.log ‖f z‖) c R := by
  have hR0 : 0 < R := hr₀.trans_le hR
  have hRabs : |R| = R := abs_of_pos hR0
  have hfR : AnalyticOnNhd ℂ f (closedBall c |R|) := fun z _ => hf z (mem_univ z)
  rw [hfR.circleAverage_log_norm hR0.ne' hc, hRabs]
  set D := MeromorphicOn.divisor f (closedBall c R)
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall c R)
  set S := hfin.toFinset
  have hDnn : ∀ u, 0 ≤ D u := fun u =>
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun z _ => hf z (mem_univ z)) u
  have hsuppS : ∀ u ∈ S, u ∈ closedBall c R ∧ u ≠ c := by
    intro u hu
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hu
    refine ⟨by_contra fun h => hu (D.apply_eq_zero_of_notMem h), fun huc => hu ?_⟩
    rw [huc, MeromorphicOn.divisor_apply (fun z _ => (hf z (mem_univ z)).meromorphicAt)
      (mem_closedBall_self hR0.le), ((hf c (mem_univ c)).meromorphicOrderAt_eq),
      (hf c (mem_univ c)).analyticOrderAt_eq_zero.mpr hc]
    rfl
  have hsum : ∑ᶠ u, (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) =
      ∑ u ∈ S, (D u : ℝ) * Real.log (R / ‖c - u‖) := by
    rw [finsum_eq_sum_of_support_subset _ (s := S) ?_]
    · refine Finset.sum_congr rfl fun u _ => by rw [div_eq_mul_inv]
    · intro u hu
      rw [Function.mem_support] at hu
      rw [Set.Finite.coe_toFinset, Function.mem_support]
      intro h; apply hu; rw [h]; simp
  rw [hsum]
  have hmain := integral_div_le_sum_log S (fun u => (D u : ℝ)) (fun u => ‖c - u‖) hr₀ hR
    (fun u _ => by exact_mod_cast hDnn u)
    (fun u hu => norm_pos_iff.mpr (sub_ne_zero.mpr (hsuppS u hu).2.symm))
    (fun u hu => by have := (hsuppS u hu).1; rwa [mem_closedBall, dist_comm, dist_eq_norm] at this)
    hφi (fun r hr => by
      refine (hφ r hr).trans (le_of_eq ?_)
      have hsub : Function.support (fun u => (MeromorphicOn.divisor f (closedBall c r) u : ℝ)) ⊆
          (S.filter fun u => ‖c - u‖ ≤ r : Finset ℂ) := by
        intro u hu
        rw [Function.mem_support] at hu
        have hur : u ∈ closedBall c r := by
          by_contra h; exact hu (by rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ h]; simp)
        have huR : u ∈ closedBall c R := closedBall_subset_closedBall hr.2 hur
        rw [Finset.coe_filter, mem_setOf_eq]
        refine ⟨?_, by rwa [mem_closedBall, dist_comm, dist_eq_norm] at hur⟩
        rw [Set.Finite.mem_toFinset, Function.mem_support]
        intro h0
        apply hu
        rw [MeromorphicOn.divisor_apply (fun z _ => (hf z (mem_univ z)).meromorphicAt) hur]
        rw [MeromorphicOn.divisor_apply (fun z _ => (hf z (mem_univ z)).meromorphicAt) huR] at h0
        exact_mod_cast h0
      rw [finsum_eq_sum_of_support_subset _ hsub, Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases h : ‖c - u‖ ≤ r
      · have hur : u ∈ closedBall c r := by rwa [mem_closedBall, dist_comm, dist_eq_norm]
        have huR : u ∈ closedBall c R := closedBall_subset_closedBall hr.2 hur
        rw [if_pos h, if_pos h,
          MeromorphicOn.divisor_apply (fun z _ => (hf z (mem_univ z)).meromorphicAt) hur,
          MeromorphicOn.divisor_apply (fun z _ => (hf z (mem_univ z)).meromorphicAt) huR]
      · rw [if_neg h, if_neg h])
  linarith

/-- `∫₀^{2π} |sin θ| dθ = 4`. -/
theorem integral_abs_sin_zero_two_pi : ∫ θ in (0 : ℝ)..2 * Real.pi, |Real.sin θ| = 4 := by
  have hπ := Real.pi_pos
  have h1 : ∫ θ in (0 : ℝ)..Real.pi, |Real.sin θ| = 2 := by
    rw [intervalIntegral.integral_congr (g := Real.sin) fun θ hθ => by
      rw [uIcc_of_le hπ.le] at hθ
      exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)]
    rw [integral_sin]; simp; norm_num
  have h2 : ∫ θ in Real.pi..2 * Real.pi, |Real.sin θ| = 2 := by
    rw [intervalIntegral.integral_congr (g := fun θ => -Real.sin θ) fun θ hθ => by
      rw [uIcc_of_le (by linarith)] at hθ
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi (x := θ - Real.pi) (by linarith [hθ.1])
        (by linarith [hθ.2])
      rw [Real.sin_sub_pi] at hs
      exact abs_of_nonpos (by linarith)]
    rw [intervalIntegral.integral_neg, integral_sin]; simp; norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := Real.pi), h1, h2]
  · norm_num
  · exact (continuous_abs.comp Real.continuous_sin).intervalIntegrable _ _
  · exact (continuous_abs.comp Real.continuous_sin).intervalIntegrable _ _

/-- **Angular average of the height.** On the circle `|z - c| = R`, the average of `|Im z|` is at
most `|Im c| + (2/π) R`. -/
theorem circleAverage_abs_im_le (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    Real.circleAverage (fun z => |z.im|) c R ≤ |c.im| + 2 / Real.pi * R := by
  have hπ := Real.pi_pos
  rw [Real.circleAverage_def, smul_eq_mul]
  have hpt : ∀ θ : ℝ, |(circleMap c R θ).im| ≤ |c.im| + R * |Real.sin θ| := by
    intro θ
    have : (circleMap c R θ).im = c.im + R * Real.sin θ := by
      simp [circleMap, Complex.exp_ofReal_mul_I_im]
    rw [this]
    calc |c.im + R * Real.sin θ| ≤ |c.im| + |R * Real.sin θ| := abs_add_le _ _
      _ = |c.im| + R * |Real.sin θ| := by rw [abs_mul, abs_of_nonneg hR]
  have hint1 : IntervalIntegrable (fun θ => |(circleMap c R θ).im|) volume 0 (2 * Real.pi) :=
    (continuous_abs.comp (Complex.continuous_im.comp (continuous_circleMap c R))).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun θ : ℝ => |c.im| + R * |Real.sin θ|) volume 0 (2 * Real.pi) :=
    (continuous_const.add (continuous_const.mul (continuous_abs.comp Real.continuous_sin))).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on (by positivity) hint1 hint2 fun θ _ => hpt θ
  have hval : ∫ θ in (0 : ℝ)..2 * Real.pi, (|c.im| + R * |Real.sin θ|) =
      (2 * Real.pi - 0) * |c.im| + R * 4 := by
    rw [intervalIntegral.integral_add (f := fun _ => |c.im|) (g := fun θ => R * |Real.sin θ|)
      intervalIntegrable_const
      ((continuous_const.mul (continuous_abs.comp Real.continuous_sin)).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_abs_sin_zero_two_pi, smul_eq_mul]
  rw [hval] at hmono
  calc (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, |(circleMap c R θ).im| ≤
        (2 * Real.pi)⁻¹ * ((2 * Real.pi - 0) * |c.im| + R * 4) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = |c.im| + 2 / Real.pi * R := by field_simp; ring

end

end HTGeometry
