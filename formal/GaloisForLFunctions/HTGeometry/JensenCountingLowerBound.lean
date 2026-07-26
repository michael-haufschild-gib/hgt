import Mathlib.Analysis.Complex.JensenFormula

/-!
# A Jensen lower bound for the number of zeros

Mathlib's `AnalyticOnNhd.sum_divisor_le` bounds the number of zeros of an analytic function in a
ball *from above* by the growth of the function.  The opposite direction is what converts a growth
*lower* bound into a zero count, and it is what a counting law such as Riemann--von Mangoldt rests
on.

Comparing Jensen's formula at two radii `0 < r < R` and using that every zero contributes
`log (R/‖c-u‖) ≤ log (R/r)` once it lies outside the small ball, while a zero inside the small ball
contributes exactly `log (r/‖c-u‖) + log (R/r)`, gives the termwise estimate

```
d(u) log (R/‖c-u‖) ≤ d_r(u) log (r/‖c-u‖) + d(u) log (R/r)
```

and hence

```
circleAverage (log ‖f‖) c R - circleAverage (log ‖f‖) c r ≤ (number of zeros in B(c,R)) log (R/r).
```

Zeros are counted with multiplicity, as the total mass of the divisor.
-/

open Filter Metric Real Set MeromorphicOn Topology

namespace GaloisForLFunctions.HTGeometry

/-- The number of zeros of `f` in the closed ball of radius `R`, counted with multiplicity. -/
noncomputable def zeroCount (f : ℂ → ℂ) (c : ℂ) (R : ℝ) : ℝ :=
  ∑ᶠ u, (divisor f (closedBall c R) u : ℝ)

/-- Termwise comparison of the two Jensen weights. -/
theorem divisor_mul_log_le {c : ℂ} {r R : ℝ} {f : ℂ → ℂ} (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0) (u : ℂ) :
    (divisor f (closedBall c R) u : ℝ) * Real.log (R * ‖c - u‖⁻¹)
      ≤ (divisor f (closedBall c r) u : ℝ) * Real.log (r * ‖c - u‖⁻¹)
        + (divisor f (closedBall c R) u : ℝ) * Real.log (R / r) := by
  have hR : 0 < R := lt_trans hr hrR
  have hsub : closedBall c r ⊆ closedBall c R := closedBall_subset_closedBall hrR.le
  by_cases hzero : divisor f (closedBall c R) u = 0
  · have hzr : divisor f (closedBall c r) u = 0 := by
      by_cases hu : u ∈ closedBall c r
      · rw [hf.divisor_apply (hsub hu)] at hzero
        rw [(hf.mono hsub).divisor_apply hu, hzero]
      · rw [divisor_def]
        exact if_neg fun h => hu h.2
    rw [hzero, hzr]
    simp
  · -- `u` is an actual zero of `f`, hence distinct from `c` and inside the big ball
    have humem : u ∈ closedBall c R := by
      by_contra hu
      exact hzero (by rw [divisor_def]; exact if_neg fun h => hu h.2)
    have hdpos : 0 < (divisor f (closedBall c R) u : ℝ) := by
      have hnn : (0 : ℤ) ≤ divisor f (closedBall c R) u := hf.divisor_nonneg u
      exact_mod_cast lt_of_le_of_ne hnn (Ne.symm hzero)
    have hne : u ≠ c := by
      intro huc
      apply hzero
      have hcmem : c ∈ closedBall c R := mem_closedBall_self hR.le
      rw [huc, hf.divisor_apply hcmem,
        (hf c hcmem).analyticOrderAt_eq_zero.mpr hfc]
      simp
    have hd : 0 < ‖c - u‖ := by
      simpa [sub_eq_zero] using (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne)))
    by_cases hu : u ∈ closedBall c r
    · -- inside the small ball: the two weights differ by exactly `log (R/r)`
      have hdr : divisor f (closedBall c r) u = divisor f (closedBall c R) u := by
        rw [(hf.mono hsub).divisor_apply hu, hf.divisor_apply (hsub hu)]
      have hsplit : Real.log (R * ‖c - u‖⁻¹) = Real.log (r * ‖c - u‖⁻¹) + Real.log (R / r) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
      rw [hdr, hsplit]
      ring_nf
      rfl
    · -- outside the small ball: the weight is at most `log (R/r)`
      have hzr : divisor f (closedBall c r) u = 0 := by
        rw [divisor_def]
        exact if_neg fun h => hu h.2
      have hdist : r < ‖c - u‖ := by
        simp only [mem_closedBall, not_le, dist_eq_norm] at hu
        simpa [norm_sub_rev] using hu
      have hweight : Real.log (R * ‖c - u‖⁻¹) ≤ Real.log (R / r) := by
        apply Real.log_le_log (by positivity)
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by
          rw [inv_le_inv₀ hd hr]; exact hdist.le) hR.le
      rw [hzr]
      simp only [Int.cast_zero, zero_mul, zero_add]
      exact mul_le_mul_of_nonneg_left hweight hdpos.le

/-- **Jensen counting lower bound.**  The growth of the circle average of `log ‖f‖` between two
radii is at most the number of zeros in the larger ball times `log (R/r)`. -/
theorem circleAverage_sub_le_zeroCount_mul_log {c : ℂ} {r R : ℝ} {f : ℂ → ℂ}
    (hr : 0 < r) (hrR : r < R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0) :
    circleAverage (Real.log ‖f ·‖) c R - circleAverage (Real.log ‖f ·‖) c r
      ≤ zeroCount f c R * Real.log (R / r) := by
  have hR : 0 < R := lt_trans hr hrR
  have hsub : closedBall c r ⊆ closedBall c R := closedBall_subset_closedBall hrR.le
  have hfr : AnalyticOnNhd ℂ f (closedBall c r) := hf.mono hsub
  have hRabs : |R| = R := abs_of_pos hR
  have hrabs : |r| = r := abs_of_pos hr
  have hfabsR : AnalyticOnNhd ℂ f (closedBall c |R|) := by rwa [hRabs]
  have hfabsr : AnalyticOnNhd ℂ f (closedBall c |r|) := by rwa [hrabs]
  have hjR := hfabsR.circleAverage_log_norm hR.ne' hfc
  have hjr := hfabsr.circleAverage_log_norm hr.ne' hfc
  rw [hRabs] at hjR
  rw [hrabs] at hjr
  -- finite supports
  have hfinR : (Function.support fun u =>
      (divisor f (closedBall c R) u : ℝ) * Real.log (R * ‖c - u‖⁻¹)).Finite := by
    refine ((divisor f (closedBall c R)).finiteSupport (isCompact_closedBall ..)).subset ?_
    intro u hu
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hu
    exact_mod_cast fun h => hu.1 (by rw [h]; simp)
  have hfinr : (Function.support fun u =>
      (divisor f (closedBall c r) u : ℝ) * Real.log (r * ‖c - u‖⁻¹)).Finite := by
    refine ((divisor f (closedBall c r)).finiteSupport (isCompact_closedBall ..)).subset ?_
    intro u hu
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hu
    exact_mod_cast fun h => hu.1 (by rw [h]; simp)
  have hfinc : (Function.support fun u =>
      (divisor f (closedBall c R) u : ℝ) * Real.log (R / r)).Finite := by
    refine ((divisor f (closedBall c R)).finiteSupport (isCompact_closedBall ..)).subset ?_
    intro u hu
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hu
    exact_mod_cast fun h => hu.1 (by rw [h]; simp)
  have hle : (∑ᶠ u, (divisor f (closedBall c R) u : ℝ) * Real.log (R * ‖c - u‖⁻¹))
      ≤ (∑ᶠ u, (divisor f (closedBall c r) u : ℝ) * Real.log (r * ‖c - u‖⁻¹))
        + ∑ᶠ u, (divisor f (closedBall c R) u : ℝ) * Real.log (R / r) := by
    rw [← finsum_add_distrib hfinr hfinc]
    exact finsum_le_finsum' hfinR (hfinr.union hfinc |>.subset (by
      intro u hu
      simp only [Function.mem_support, ne_eq] at hu
      by_contra hcon
      simp only [Set.mem_union, Function.mem_support, ne_eq, not_or, not_not] at hcon
      exact hu (by rw [hcon.1, hcon.2, add_zero]))) fun u =>
      divisor_mul_log_le hr hrR hf hfc u
  have hconst : (∑ᶠ u, (divisor f (closedBall c R) u : ℝ) * Real.log (R / r))
      = zeroCount f c R * Real.log (R / r) := by
    rw [zeroCount, finsum_mul]
  rw [hjR, hjr]
  rw [hconst] at hle
  linarith

/-- The number of zeros in the larger ball is at least the normalized circle-average increment. -/
theorem le_zeroCount {c : ℂ} {r R : ℝ} {f : ℂ → ℂ}
    (hr : 0 < r) (hrR : r < R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0) :
    (circleAverage (Real.log ‖f ·‖) c R - circleAverage (Real.log ‖f ·‖) c r)
        / Real.log (R / r)
      ≤ zeroCount f c R := by
  have hlogpos : 0 < Real.log (R / r) := Real.log_pos (by rw [lt_div_iff₀ hr]; linarith)
  rw [div_le_iff₀ hlogpos]
  exact circleAverage_sub_le_zeroCount_mul_log hr hrR hf hfc

end GaloisForLFunctions.HTGeometry
