import Mathlib

/-!
# The logarithmic kernel of a compact bounded profile is square integrable off the support

For a bounded profile supported in `[-a, a]`, the kernel image `x ↦ ∫_{-a}^a u(t)/(x-t) dt` obeys
the exact off-support bound `M · log((x+a)/(x-a))` on the right exterior ray.  The bound splits
into a boundary collar, where `log((r+2a)/r)² ≲ (log(1+2a) - log r)²` is integrable because
`log(1/r) ≤ 4 r^{-1/4}`, and a long-range tail, where `log(1+2a/(x-a)) ≤ 2a/(x-a)` is square
integrable.  Hence the exterior residual of the logarithmic block is `L²` — with no endpoint
trace, `H¹` premise, or asymptotic expansion anywhere.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set intervalIntegral

/-- The exact off-support integral of the shifted inverse kernel:
`∫_{-a}^a dt/(x-t) = log((x+a)/(x-a))` for `x > a`. -/
theorem integral_inv_sub_kernel {a x : ℝ} (ha : 0 ≤ a) (hx : a < x) :
    (∫ t in (-a)..a, (x - t)⁻¹) = Real.log ((x + a) / (x - a)) := by
  have hderiv : ∀ t ∈ uIcc (-a) a, HasDerivAt (fun t => -Real.log (x - t)) ((x - t)⁻¹) t := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    have hxt : 0 < x - t := by
      rcases ht with ⟨_, h2⟩
      linarith
    have h1 : HasDerivAt (fun t : ℝ => x - t) (-1) t := (hasDerivAt_id t).const_sub x
    have h2 := (h1.log hxt.ne').neg
    have h3 : -(-1 / (x - t)) = (x - t)⁻¹ := by
      field_simp
    rw [← h3]
    exact h2
  have hint : IntervalIntegrable (fun t => (x - t)⁻¹) volume (-a) a := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    have : 0 < x - t := by
      rcases ht with ⟨_, h2⟩
      linarith
    exact this.ne'
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  have hxa : 0 < x - a := by linarith
  have hxa' : 0 < x + a := by linarith
  rw [Real.log_div hxa'.ne' hxa.ne']
  ring_nf

/-- The pointwise off-support kernel bound: `|∫ u(t)/(x-t) dt| ≤ M log((x+a)/(x-a))`. -/
theorem abs_integral_kernel_le {u : ℝ → ℝ} {a M x : ℝ} (ha : 0 ≤ a) (hx : a < x)
    (hM : ∀ t, |u t| ≤ M) (hmeas : Measurable u) :
    |∫ t in Icc (-a) a, u t / (x - t)|
      ≤ M * Real.log ((x + a) / (x - a)) := by
  have hb : ∀ t ∈ Icc (-a) a, |u t / (x - t)| ≤ M * (x - t)⁻¹ := by
    intro t ht
    have hxt : 0 < x - t := by
      rcases ht with ⟨_, h2⟩
      linarith
    rw [abs_div, abs_of_pos hxt, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hM t) (by positivity)
  have hint : IntegrableOn (fun t => M * (x - t)⁻¹) (Icc (-a) a) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro t ht
    have : 0 < x - t := by
      rcases ht with ⟨_, h2⟩
      linarith
    exact this.ne'
  have hint2 : IntegrableOn (fun t => u t / (x - t)) (Icc (-a) a) := by
    refine Integrable.mono' hint ?_ ?_
    · exact ((hmeas.div ((measurable_const.sub measurable_id))).aestronglyMeasurable).restrict
    · exact (ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun t ht => by
          rw [Real.norm_eq_abs]
          exact hb t ht)
  calc |∫ t in Icc (-a) a, u t / (x - t)|
      ≤ ∫ t in Icc (-a) a, |u t / (x - t)| := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ t in Icc (-a) a, M * (x - t)⁻¹ := by
        refine setIntegral_mono_on hint2.abs hint measurableSet_Icc hb
    _ = M * ∫ t in Icc (-a) a, (x - t)⁻¹ := by
        rw [MeasureTheory.integral_const_mul]
    _ = M * Real.log ((x + a) / (x - a)) := by
        congr 1
        rw [← setIntegral_congr_set Ioc_ae_eq_Icc,
          ← intervalIntegral.integral_of_le (by linarith : -a ≤ a)]
        exact integral_inv_sub_kernel ha hx

/-- `log(1/r) ≤ 4 r^{-1/4}` on `(0, 1]` — the collar comparison. -/
theorem log_inv_le_rpow {r : ℝ} (hr : 0 < r) :
    Real.log (1 / r) ≤ 4 * r ^ (-(1 : ℝ) / 4) := by
  have h1 := Real.log_le_rpow_div (le_of_lt (by positivity : (0 : ℝ) < 1 / r))
    (by norm_num : (0 : ℝ) < 1 / 4)
  calc Real.log (1 / r) ≤ (1 / r) ^ ((1 : ℝ) / 4) / (1 / 4) := h1
    _ = 4 * r ^ (-(1 : ℝ) / 4) := by
        have h2 : ((1 : ℝ) / r) ^ ((1 : ℝ) / 4) = r ^ (-((1 : ℝ) / 4)) := by
          rw [one_div, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]
        have h3 : -(1 : ℝ) / 4 = -((1 : ℝ) / 4) := by ring
        rw [h2, h3]
        field_simp

/-- **The collar is square integrable**: `∫_0^1 log((r+c)/r)² dr < ∞` for `c > 0`. -/
theorem integrableOn_log_collar_sq {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun r => Real.log ((r + c) / r) ^ 2) (Ioo (0 : ℝ) 1) := by
  have hbound : ∀ r ∈ Ioo (0 : ℝ) 1, Real.log ((r + c) / r) ^ 2
      ≤ (Real.log (1 + c) + 4 * r ^ (-(1 : ℝ) / 4)) ^ 2 := by
    intro r hr
    have hrpos := hr.1
    have hr1 := hr.2
    have hlog1 : Real.log ((r + c) / r) ≤ Real.log (1 + c) + Real.log (1 / r) := by
      have h2 : (r + c) / r ≤ (1 + c) * (1 / r) := by
        rw [div_le_iff₀ hrpos] at *
        have : (1 + c) * (1 / r) * r = 1 + c := by
          field_simp
        rw [this]
        linarith
      calc Real.log ((r + c) / r) ≤ Real.log ((1 + c) * (1 / r)) :=
          Real.log_le_log (by positivity) h2
        _ = Real.log (1 + c) + Real.log (1 / r) :=
          Real.log_mul (by positivity) (by positivity)
    have hnn : 0 ≤ Real.log ((r + c) / r) := by
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ hrpos]
      linarith
    have hrhs : Real.log ((r + c) / r) ≤ Real.log (1 + c) + 4 * r ^ (-(1 : ℝ) / 4) :=
      le_trans hlog1 (by
        have := log_inv_le_rpow hrpos
        linarith)
    exact pow_le_pow_left₀ hnn hrhs 2
  have hint : IntegrableOn
      (fun r => (Real.log (1 + c) + 4 * r ^ (-(1 : ℝ) / 4)) ^ 2) (Ioo (0 : ℝ) 1) := by
    have hexp : ∀ r : ℝ, 0 < r →
        (Real.log (1 + c) + 4 * r ^ (-(1 : ℝ) / 4)) ^ 2
          = Real.log (1 + c) ^ 2
            + 8 * Real.log (1 + c) * r ^ (-(1 : ℝ) / 4)
            + 16 * (r ^ (-(1 : ℝ) / 4)) ^ 2 := fun r hr => by ring
    have h1 : IntegrableOn (fun r : ℝ => r ^ (-(1 : ℝ) / 4)) (Ioo (0 : ℝ) 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).mpr (by norm_num)
    have h2 : IntegrableOn (fun r : ℝ => r ^ (-(1 : ℝ) / 2)) (Ioo (0 : ℝ) 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).mpr (by norm_num)
    have h3 : IntegrableOn
        (fun r : ℝ => Real.log (1 + c) ^ 2
          + 8 * Real.log (1 + c) * r ^ (-(1 : ℝ) / 4)
          + 16 * (r ^ (-(1 : ℝ) / 2))) (Ioo (0 : ℝ) 1) := by
      refine Integrable.add (Integrable.add ?_ ?_) ?_
      · exact integrableOn_const (by simp [Real.volume_Ioo])
      · exact h1.const_mul _
      · exact h2.const_mul _
    refine h3.congr_fun ?_ measurableSet_Ioo
    intro r hr
    show Real.log (1 + c) ^ 2 + 8 * Real.log (1 + c) * r ^ (-(1 : ℝ) / 4)
        + 16 * (r ^ (-(1 : ℝ) / 2))
      = (Real.log (1 + c) + 4 * r ^ (-(1 : ℝ) / 4)) ^ 2
    rw [hexp r hr.1]
    congr 1
    rw [← Real.rpow_natCast (r ^ (-(1 : ℝ) / 4)) 2, ← Real.rpow_mul hr.1.le]
    norm_num
  refine Integrable.mono' hint ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_ |>.restrict
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall fun r hr => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound r hr

/-- **The long-range tail is square integrable**: `log(1 + c/(x-a)) ≤ c/(x-a)` gives an
`O(x⁻¹)` bound past the unit collar. -/
theorem integrableOn_log_tail_sq {a c : ℝ} (hc : 0 ≤ c) :
    IntegrableOn (fun x => Real.log ((x - a + c) / (x - a)) ^ 2) (Ioi (a + 1)) := by
  have hbound : ∀ x ∈ Ioi (a + 1), Real.log ((x - a + c) / (x - a)) ^ 2
      ≤ c ^ 2 * ((x - a) ^ (-1 : ℝ)) ^ 2 := by
    intro x hx
    rw [mem_Ioi] at hx
    have hxa : (0 : ℝ) < x - a := by linarith
    have hdiv : (x - a + c) / (x - a) = 1 + c / (x - a) := by
      field_simp
    have hlog : Real.log ((x - a + c) / (x - a)) ≤ c / (x - a) := by
      rw [hdiv]
      calc Real.log (1 + c / (x - a)) ≤ 1 + c / (x - a) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        _ = c / (x - a) := by ring
    have hnn : 0 ≤ Real.log ((x - a + c) / (x - a)) := by
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ hxa]
      linarith
    calc Real.log ((x - a + c) / (x - a)) ^ 2 ≤ (c / (x - a)) ^ 2 :=
        pow_le_pow_left₀ hnn hlog 2
      _ = c ^ 2 * ((x - a) ^ (-1 : ℝ)) ^ 2 := by
        rw [Real.rpow_neg_one, div_pow, div_eq_mul_inv, inv_pow]
  have hint : IntegrableOn (fun x : ℝ => c ^ 2 * ((x - a) ^ (-1 : ℝ)) ^ 2) (Ioi (a + 1)) := by
    have h1 : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
    have h2 : IntegrableOn (fun x : ℝ => ((x - a) ^ (-2 : ℝ))) (Ioi (a + 1)) := by
      have h3 := (integrable_indicator_iff measurableSet_Ioi).mpr h1
      have h4 := h3.comp_sub_right a
      rw [← integrable_indicator_iff measurableSet_Ioi]
      refine h4.congr ?_
      refine Filter.Eventually.of_forall fun x => ?_
      show (Ioi (1 : ℝ)).indicator (fun y => y ^ (-2 : ℝ)) (x - a)
          = (Ioi (a + 1)).indicator (fun x => (x - a) ^ (-2 : ℝ)) x
      by_cases hx : x - a ∈ Ioi (1 : ℝ)
      · rw [indicator_of_mem hx, indicator_of_mem (by
          rw [mem_Ioi] at hx ⊢
          linarith)]
      · rw [indicator_of_notMem hx, indicator_of_notMem (by
          rw [mem_Ioi] at hx ⊢
          intro h
          exact hx (by linarith))]
    have h5 : IntegrableOn (fun x : ℝ => c ^ 2 * ((x - a) ^ (-2 : ℝ))) (Ioi (a + 1)) :=
      h2.const_mul (c ^ 2)
    refine h5.congr_fun ?_ measurableSet_Ioi
    intro x hx
    rw [mem_Ioi] at hx
    have hxa : (0 : ℝ) < x - a := by linarith
    show c ^ 2 * ((x - a) ^ (-2 : ℝ)) = c ^ 2 * ((x - a) ^ (-1 : ℝ)) ^ 2
    rw [← Real.rpow_natCast ((x - a) ^ (-1 : ℝ)) 2, ← Real.rpow_mul hxa.le]
    norm_num
  refine Integrable.mono' hint ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_ |>.restrict
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound x hx

end GaloisForLFunctions.HTGeometry
