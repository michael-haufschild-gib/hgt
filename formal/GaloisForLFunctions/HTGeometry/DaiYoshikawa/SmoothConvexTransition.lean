import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Convex.Deriv

/-!
# The convex cut profile of Lemma 3.1

Lemma 3.1 of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the
Laplacian* (arXiv:2509.06151v2), produces a Hermitian metric on `L` with semi-negative curvature
which is *flat* near the nodes.  The whole construction rests on one real function: for `c > 0` a
smooth convex increasing `F_c` on `[0,∞)` with

```text
F_c(t) = 0        (t ≤ c),
F_c(t) = t + A_c  (t ≥ 2c),
```

whose existence the paper asserts by integrating a smooth step.  Convexity and monotonicity of `F_c`
are exactly what make `i∂∂̄ F_c(φ) = F_c'(φ) i∂∂̄φ + F_c''(φ) i∂φ∧∂̄φ` semi-positive, and the
vanishing near `0` is what makes the metric flat near the node.

This file constructs `F_c` from mathlib's smooth transition and proves all four properties.
-/

open Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- The smooth step: `0` below `c`, `1` above `2c`. -/
noncomputable def cutProfile (c t : ℝ) : ℝ := Real.smoothTransition ((t - c) / c)

theorem cutProfile_nonneg (c t : ℝ) : 0 ≤ cutProfile c t := Real.smoothTransition.nonneg _

theorem cutProfile_le_one (c t : ℝ) : cutProfile c t ≤ 1 := Real.smoothTransition.le_one _

theorem cutProfile_eq_zero {c t : ℝ} (hc : 0 < c) (ht : t ≤ c) : cutProfile c t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hc.le)

theorem cutProfile_eq_one {c t : ℝ} (hc : 0 < c) (ht : 2 * c ≤ t) : cutProfile c t = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hc]; linarith)

theorem monotone_cutProfile {c : ℝ} (hc : 0 < c) : Monotone (cutProfile c) := by
  intro x y hxy
  refine Real.smoothTransition.monotone ?_
  gcongr

theorem contDiff_cutProfile (c : ℝ) (n : ℕ∞) : ContDiff ℝ n (cutProfile c) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const c)

theorem continuous_cutProfile (c : ℝ) : Continuous (cutProfile c) :=
  (contDiff_cutProfile c 1).continuous

/-- The convex increasing cut of Lemma 3.1: the primitive of the smooth step. -/
noncomputable def cutPrimitive (c t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, cutProfile c s

theorem hasDerivAt_cutPrimitive (c t : ℝ) : HasDerivAt (cutPrimitive c) (cutProfile c t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_cutProfile c).intervalIntegrable 0 t)
    ((continuous_cutProfile c).stronglyMeasurableAtFilter _ _)
    (continuous_cutProfile c).continuousAt

theorem deriv_cutPrimitive (c t : ℝ) : deriv (cutPrimitive c) t = cutProfile c t :=
  (hasDerivAt_cutPrimitive c t).deriv

theorem differentiable_cutPrimitive (c : ℝ) : Differentiable ℝ (cutPrimitive c) := fun t =>
  (hasDerivAt_cutPrimitive c t).differentiableAt

/-- `F_c` vanishes on `[0, c]`. -/
theorem cutPrimitive_eq_zero {c t : ℝ} (hc : 0 < c) (ht0 : 0 ≤ t) (ht : t ≤ c) :
    cutPrimitive c t = 0 := by
  rw [cutPrimitive]
  have hcongr : (∫ s in (0 : ℝ)..t, cutProfile c s) = ∫ _s in (0 : ℝ)..t, (0 : ℝ) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht0] at hs
    exact cutProfile_eq_zero hc (le_trans hs.2 ht)
  rw [hcongr, intervalIntegral.integral_zero]

/-- `F_c` is affine of slope one above `2c`. -/
theorem cutPrimitive_eq_add {c t : ℝ} (hc : 0 < c) (ht : 2 * c ≤ t) :
    cutPrimitive c t = t + (cutPrimitive c (2 * c) - 2 * c) := by
  have hsplit : cutPrimitive c t
      = cutPrimitive c (2 * c) + ∫ s in (2 * c)..t, cutProfile c s := by
    rw [cutPrimitive, cutPrimitive]
    exact (intervalIntegral.integral_add_adjacent_intervals
      ((continuous_cutProfile c).intervalIntegrable 0 (2 * c))
      ((continuous_cutProfile c).intervalIntegrable (2 * c) t)).symm
  have htail : (∫ s in (2 * c)..t, cutProfile c s) = t - 2 * c := by
    have hcongr : (∫ s in (2 * c)..t, cutProfile c s) = ∫ _s in (2 * c)..t, (1 : ℝ) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le ht] at hs
      exact cutProfile_eq_one hc hs.1
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  rw [hsplit, htail]
  ring

/-- `F_c` is increasing. -/
theorem monotone_cutPrimitive (c : ℝ) : Monotone (cutPrimitive c) := by
  refine monotone_of_deriv_nonneg (differentiable_cutPrimitive c) fun t => ?_
  rw [deriv_cutPrimitive]
  exact cutProfile_nonneg c t

/-- `F_c` is convex: its derivative is the monotone step. -/
theorem convexOn_cutPrimitive {c : ℝ} (hc : 0 < c) : ConvexOn ℝ univ (cutPrimitive c) := by
  have hmono : MonotoneOn (deriv (cutPrimitive c)) (interior (univ : Set ℝ)) := by
    intro x _ y _ hxy
    rw [deriv_cutPrimitive, deriv_cutPrimitive]
    exact monotone_cutProfile hc hxy
  exact hmono.convexOn_of_deriv convex_univ
    (differentiable_cutPrimitive c).continuous.continuousOn
    ((differentiable_cutPrimitive c).differentiableOn)

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
