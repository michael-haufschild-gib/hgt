import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The endpoint logarithm and its comparison with the square root

The antiderivative of `1 / sqrt(x² - 1)` on the ray `x > 1` is `log(x + sqrt(x² - 1))`, the inverse
hyperbolic cosine.  mathlib has `Real.arcosh` but no derivative for it, so this file builds the
antiderivative directly and proves the two-sided comparison with `sqrt(x² - 1)`:

```text
sqrt(x²-1) (1 - (x²-1)/6)  ≤  log(x + sqrt(x²-1))  ≤  sqrt(x²-1).
```

Both bounds are proved the same way: the difference vanishes at `x = 1` and its derivative has a fixed
sign on the ray, the sign coming from the elementary inequality `x(x+1) ≥ 2`.  The lower bound is what
makes the pair `(log(x + sqrt(x²-1)), sqrt(x²-1))` interchangeable to relative order `x² - 1` near the
endpoint — the input every endpoint-uniform Liouville estimate needs.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Set

/-- The endpoint logarithm `log(x + sqrt(x²-1))`, the antiderivative of `1/sqrt(x²-1)`. -/
def endpointLog (x : ℝ) : ℝ := Real.log (x + Real.sqrt (x ^ 2 - 1))

theorem endpointLog_one : endpointLog 1 = 0 := by
  rw [endpointLog]
  norm_num

theorem hasDerivAt_endpointLog {x : ℝ} (hx : 1 < x) :
    HasDerivAt endpointLog (1 / Real.sqrt (x ^ 2 - 1)) x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hs : (0 : ℝ) < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.mpr hd
  have hsum : (0 : ℝ) < x + Real.sqrt (x ^ 2 - 1) := by linarith
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2 - 1) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).sub_const 1
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 - 1))
      (2 * x / (2 * Real.sqrt (x ^ 2 - 1))) x := hsq.sqrt hd.ne'
  have hinner : HasDerivAt (fun t : ℝ => t + Real.sqrt (t ^ 2 - 1))
      (1 + 2 * x / (2 * Real.sqrt (x ^ 2 - 1))) x := by
    simpa using (hasDerivAt_id x).fun_add hsqrt
  have h := hinner.log hsum.ne'
  have hval : (1 + 2 * x / (2 * Real.sqrt (x ^ 2 - 1))) / (x + Real.sqrt (x ^ 2 - 1))
      = 1 / Real.sqrt (x ^ 2 - 1) := by
    rw [div_eq_div_iff hsum.ne' hs.ne']
    field_simp
    ring
  rw [hval] at h
  exact h

theorem continuousOn_endpointLog : ContinuousOn endpointLog (Ici 1) := by
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  have hx1 : (1 : ℝ) ≤ x := hx
  have hsum : (0 : ℝ) < x + Real.sqrt (x ^ 2 - 1) := by
    have : (0 : ℝ) ≤ Real.sqrt (x ^ 2 - 1) := Real.sqrt_nonneg _
    linarith
  refine ContinuousAt.log ?_ hsum.ne'
  exact continuousAt_id.add ((Real.continuous_sqrt.continuousAt).comp (by fun_prop))

/-- **The upper comparison.**  `log(x + sqrt(x²-1)) ≤ sqrt(x²-1)`: the difference vanishes at the
endpoint and its derivative is `(1 - x)/sqrt(x²-1) ≤ 0`. -/
theorem endpointLog_le_sqrt {x : ℝ} (hx : 1 ≤ x) :
    endpointLog x ≤ Real.sqrt (x ^ 2 - 1) := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, endpointLog_one]
    norm_num
  -- work on the compact interval [1, x]
  set F : ℝ → ℝ := fun t => Real.sqrt (t ^ 2 - 1) - endpointLog t with hFdef
  have hFcont : ContinuousOn F (Icc 1 x) := by
    refine ContinuousOn.sub ?_ (continuousOn_endpointLog.mono (fun t ht => ht.1))
    exact (Real.continuous_sqrt.comp_continuousOn (by fun_prop))
  have hFderiv : ∀ t ∈ Ioo (1 : ℝ) x, HasDerivAt F
      (2 * t / (2 * Real.sqrt (t ^ 2 - 1)) - 1 / Real.sqrt (t ^ 2 - 1)) t := by
    intro t ht
    have ht1 : (1 : ℝ) < t := ht.1
    have hd : (0 : ℝ) < t ^ 2 - 1 := by nlinarith
    have hsq : HasDerivAt (fun u : ℝ => u ^ 2 - 1) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).sub_const 1
    exact (hsq.sqrt hd.ne').fun_sub (hasDerivAt_endpointLog ht1)
  have hmono : MonotoneOn F (Icc 1 x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 1 x) hFcont ?_ ?_
    · intro t ht
      rw [interior_Icc] at ht
      exact ((hFderiv t ht).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hFderiv t ht).deriv]
      have ht1 : (1 : ℝ) < t := ht.1
      have hd : (0 : ℝ) < t ^ 2 - 1 := by nlinarith
      have hs : (0 : ℝ) < Real.sqrt (t ^ 2 - 1) := Real.sqrt_pos.mpr hd
      rw [div_sub_div _ _ (by positivity) hs.ne', le_div_iff₀ (by positivity)]
      nlinarith [hs.le, ht1.le]
  have hF1 : F 1 = 0 := by
    rw [hFdef]
    simp only
    rw [endpointLog_one]
    norm_num
  have hle := hmono (left_mem_Icc.mpr hx) (right_mem_Icc.mpr hx) hx
  rw [hF1] at hle
  rw [hFdef] at hle
  simp only at hle
  linarith

/-- **The lower comparison.**  `sqrt(x²-1)(1 - (x²-1)/6) ≤ log(x + sqrt(x²-1))`.  The derivative
comparison reduces to `x(x+1) ≥ 2`, which holds on the whole ray. -/
theorem sqrt_mul_one_sub_le_endpointLog {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt (x ^ 2 - 1) * (1 - (x ^ 2 - 1) / 6) ≤ endpointLog x := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, endpointLog_one]
    norm_num
  set G : ℝ → ℝ := fun t => endpointLog t - Real.sqrt (t ^ 2 - 1) * (1 - (t ^ 2 - 1) / 6)
    with hGdef
  have hGcont : ContinuousOn G (Icc 1 x) := by
    refine ContinuousOn.sub (continuousOn_endpointLog.mono (fun t ht => ht.1)) ?_
    exact (Real.continuous_sqrt.comp_continuousOn (by fun_prop)).mul (by fun_prop)
  have hGderiv : ∀ t ∈ Ioo (1 : ℝ) x, HasDerivAt G
      (1 / Real.sqrt (t ^ 2 - 1)
        - (2 * t / (2 * Real.sqrt (t ^ 2 - 1)) * (1 - (t ^ 2 - 1) / 6)
          + Real.sqrt (t ^ 2 - 1) * (-(2 * t / 6)))) t := by
    intro t ht
    have ht1 : (1 : ℝ) < t := ht.1
    have hd : (0 : ℝ) < t ^ 2 - 1 := by nlinarith
    have hsq : HasDerivAt (fun u : ℝ => u ^ 2 - 1) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).sub_const 1
    have hfac : HasDerivAt (fun u : ℝ => 1 - (u ^ 2 - 1) / 6) (-(2 * t / 6)) t := by
      have h := (hsq.div_const 6)
      have h2 := h.const_sub 1
      simpa using h2
    exact (hasDerivAt_endpointLog ht1).fun_sub ((hsq.sqrt hd.ne').fun_mul hfac)
  have hmono : MonotoneOn G (Icc 1 x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 1 x) hGcont ?_ ?_
    · intro t ht
      rw [interior_Icc] at ht
      exact ((hGderiv t ht).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hGderiv t ht).deriv]
      have ht1 : (1 : ℝ) < t := ht.1
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht1
      have hd : (0 : ℝ) < t ^ 2 - 1 := by nlinarith
      have hs : (0 : ℝ) < Real.sqrt (t ^ 2 - 1) := Real.sqrt_pos.mpr hd
      have hssq : Real.sqrt (t ^ 2 - 1) * Real.sqrt (t ^ 2 - 1) = t ^ 2 - 1 :=
        Real.mul_self_sqrt hd.le
      -- the derivative is (1 - t(1 - (t²-1)/2)) / sqrt(t²-1)
      have hval : 1 / Real.sqrt (t ^ 2 - 1)
            - (2 * t / (2 * Real.sqrt (t ^ 2 - 1)) * (1 - (t ^ 2 - 1) / 6)
              + Real.sqrt (t ^ 2 - 1) * (-(2 * t / 6)))
          = (1 - t * (1 - (t ^ 2 - 1) / 2)) / Real.sqrt (t ^ 2 - 1) := by
        obtain ⟨S, hS0, hSsq, hSeq⟩ : ∃ S : ℝ, 0 < S ∧ S * S = t ^ 2 - 1
            ∧ Real.sqrt (t ^ 2 - 1) = S := ⟨Real.sqrt (t ^ 2 - 1), hs, hssq, rfl⟩
        rw [hSeq, ← hSsq]
        field_simp
        ring
      rw [hval]
      refine div_nonneg ?_ hs.le
      nlinarith [ht1.le, ht0.le]
  have hG1 : G 1 = 0 := by
    rw [hGdef]
    simp only
    rw [endpointLog_one]
    norm_num
  have hle := hmono (left_mem_Icc.mpr hx) (right_mem_Icc.mpr hx) hx
  rw [hG1] at hle
  rw [hGdef] at hle
  simp only at hle
  linarith

/-! ## The companion antiderivative

The second-order expansion of an endpoint Liouville phase needs the primitive of `sqrt(t²-1)` as well as
that of `1/sqrt(t²-1)`.  Both are elementary and both are absent from mathlib. -/

/-- The primitive of `sqrt(t²-1)` from the endpoint: `(x sqrt(x²-1) - L(x))/2`. -/
def endpointSqrtPrimitive (x : ℝ) : ℝ := (x * Real.sqrt (x ^ 2 - 1) - endpointLog x) / 2

theorem endpointSqrtPrimitive_one : endpointSqrtPrimitive 1 = 0 := by
  rw [endpointSqrtPrimitive, endpointLog_one]
  norm_num

theorem hasDerivAt_endpointSqrtPrimitive {x : ℝ} (hx : 1 < x) :
    HasDerivAt endpointSqrtPrimitive (Real.sqrt (x ^ 2 - 1)) x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hs : (0 : ℝ) < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.mpr hd
  have hssq : Real.sqrt (x ^ 2 - 1) * Real.sqrt (x ^ 2 - 1) = x ^ 2 - 1 :=
    Real.mul_self_sqrt hd.le
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2 - 1) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).sub_const 1
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 - 1))
      (2 * x / (2 * Real.sqrt (x ^ 2 - 1))) x := hsq.sqrt hd.ne'
  have hprod : HasDerivAt (fun t : ℝ => t * Real.sqrt (t ^ 2 - 1))
      (1 * Real.sqrt (x ^ 2 - 1) + x * (2 * x / (2 * Real.sqrt (x ^ 2 - 1)))) x :=
    (hasDerivAt_id x).fun_mul hsqrt
  have h := (hprod.fun_sub (hasDerivAt_endpointLog hx)).div_const 2
  have hne : Real.sqrt (x ^ 2 - 1) ≠ 0 := ne_of_gt hs
  have hval : (1 * Real.sqrt (x ^ 2 - 1) + x * (2 * x / (2 * Real.sqrt (x ^ 2 - 1)))
        - 1 / Real.sqrt (x ^ 2 - 1)) / 2
      = Real.sqrt (x ^ 2 - 1) := by
    have e1 : x * (2 * x / (2 * Real.sqrt (x ^ 2 - 1)))
        = x ^ 2 / Real.sqrt (x ^ 2 - 1) := by
      field_simp
    have e2 : x ^ 2 / Real.sqrt (x ^ 2 - 1) - 1 / Real.sqrt (x ^ 2 - 1)
        = Real.sqrt (x ^ 2 - 1) := by
      rw [div_sub_div_same, div_eq_iff hne]
      exact hssq.symm
    rw [add_sub_assoc, e1, e2]
    ring
  rw [hval] at h
  exact h

theorem continuousOn_endpointSqrtPrimitive : ContinuousOn endpointSqrtPrimitive (Ici 1) := by
  refine ContinuousOn.div_const ?_ 2
  refine ContinuousOn.sub ?_ continuousOn_endpointLog
  exact continuousOn_id.mul (Real.continuous_sqrt.comp_continuousOn (by fun_prop))

/-- The Taylor bound behind the second-order expansion: `|sqrt(1+u) - 1 - u/2| ≤ u²/8` for `u ≥ 0`.
The upper half is `(1 + u/2)² ≥ 1 + u`; the lower half squares to `u⁴/64 ≤ u³/8`, i.e. `u ≤ 8`, and past
`u = 8` the quadratic is already negative. -/
theorem abs_sqrt_one_add_sub_le {u : ℝ} (hu : 0 ≤ u) :
    |Real.sqrt (1 + u) - (1 + u / 2)| ≤ u ^ 2 / 8 := by
  have h1 : (0 : ℝ) ≤ 1 + u := by linarith
  have hs : Real.sqrt (1 + u) ≤ 1 + u / 2 := by
    have hsq : (1 : ℝ) + u ≤ (1 + u / 2) ^ 2 := by nlinarith
    calc Real.sqrt (1 + u) ≤ Real.sqrt ((1 + u / 2) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 1 + u / 2 := Real.sqrt_sq (by linarith)
  rw [abs_of_nonpos (by linarith : Real.sqrt (1 + u) - (1 + u / 2) ≤ 0)]
  rcases le_or_gt u 8 with hle | hgt
  · have hlow : 1 + u / 2 - u ^ 2 / 8 ≤ Real.sqrt (1 + u) := by
      rcases le_or_gt (1 + u / 2 - u ^ 2 / 8) 0 with h | h
      · exact le_trans h (Real.sqrt_nonneg _)
      · have hsq2 : (1 + u / 2 - u ^ 2 / 8) ^ 2 ≤ 1 + u := by
          nlinarith [mul_nonneg (pow_nonneg hu 3) (by linarith : (0 : ℝ) ≤ 8 - u)]
        calc 1 + u / 2 - u ^ 2 / 8 = Real.sqrt ((1 + u / 2 - u ^ 2 / 8) ^ 2) :=
              (Real.sqrt_sq h.le).symm
          _ ≤ Real.sqrt (1 + u) := Real.sqrt_le_sqrt hsq2
    linarith
  · have h2 : (1 : ℝ) ≤ Real.sqrt (1 + u) := by
      nlinarith [Real.sq_sqrt h1, Real.sqrt_nonneg (1 + u)]
    nlinarith [h2, mul_nonneg hu (by linarith : (0 : ℝ) ≤ u - 8)]

end GaloisForLFunctions.HTGeometry

end
