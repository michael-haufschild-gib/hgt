import GaloisForLFunctions.HTGeometry.LogDerivProximityBound
import GaloisForLFunctions.HTGeometry.SecondMainTheoremOmitted

/-!
# The logarithmic-derivative estimate at an omitted value

When `f` omits `a`, the shift `f − a` is zero-free, its divisor vanishes, and the divisor term of
the logarithmic-derivative estimate disappears entirely.  What is left is

```text
m(r, f'/(f−a)) ≤ (1/α)·log(1 + (2R/(R−r)²·(2 T(R, f−a) + |log‖f(0)−a‖|))^α),
```

a bound in the characteristic alone.  The trailing coefficient of a zero-free analytic germ is its
value, so the two entries of the estimate's `max` coincide.
-/

namespace GaloisForLFunctions.HTGeometry

open ValueDistribution Metric Real

/-- The divisor of a zero-free entire function vanishes identically. -/
theorem divisor_eq_zero_of_forall_ne_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hne : ∀ z, g z ≠ 0) (U : Set ℂ) : MeromorphicOn.divisor g U = 0 := by
  ext z
  by_cases hz : z ∈ U
  · rw [MeromorphicOn.divisor_apply (fun w _ => (hg.analyticAt w).meromorphicAt) hz]
    have hA : AnalyticAt ℂ g z := hg.analyticAt z
    rw [hA.meromorphicOrderAt_eq, hA.analyticOrderAt_eq_zero.mpr (hne z)]
    simp
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

/-- **The logarithmic-derivative estimate at an omitted value.**  No divisor term survives. -/
theorem proximity_logDeriv_le_of_omits {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : 1 ≤ R) {f : ℂ → ℂ} {a : ℂ}
    (hf : Differentiable ℂ f) (hne : ∀ z, f z ≠ a) :
    proximity (fun z => deriv f z / (f z - a)) ⊤ r
      ≤ (1 / α) * Real.log (1 + (2 * R / (R - r) ^ 2
          * (2 * characteristic (fun w => f w - a) ⊤ R
            + |Real.log ‖f 0 - a‖|)) ^ α) := by
  have hg : Differentiable ℂ (fun w => f w - a) := hf.sub_const a
  have hgne : ∀ z, (fun w => f w - a) z ≠ 0 := fun z => sub_ne_zero.mpr (hne z)
  have hdiv : MeromorphicOn.divisor (fun w => f w - a) (closedBall (0 : ℂ) |R|) = 0 :=
    divisor_eq_zero_of_forall_ne_zero hg hgne _
  have hf0 : ∀ z, meromorphicOrderAt (fun w => f w - a) z ≠ ⊤ := by
    intro z
    have hA : AnalyticAt ℂ (fun w => f w - a) z := hg.analyticAt z
    rw [hA.meromorphicOrderAt_eq, hA.analyticOrderAt_eq_zero.mpr (hgne z)]
    simp
  have hbd : ∀ u ∈ sphere (0 : ℂ) |R|,
      MeromorphicOn.divisor (fun w => f w - a) (closedBall (0 : ℂ) |R|) u = 0 := by
    intro u _
    rw [hdiv]
    rfl
  have hmain := proximity_logDeriv_sub_const_le hα0 hα1 hr hrR hR a hf hf0 hbd
  refine le_trans hmain (le_of_eq ?_)
  congr 2
  have hfinsum : (∑ᶠ u : ℂ,
      (|(MeromorphicOn.divisor (fun w => f w - a) (closedBall (0 : ℂ) |R|) u : ℤ)| : ℝ) ^ α) = 0 := by
    have hzero : ∀ u : ℂ,
        (|(MeromorphicOn.divisor (fun w => f w - a) (closedBall (0 : ℂ) |R|) u : ℤ)| : ℝ) ^ α = 0 := by
      intro u
      rw [hdiv]
      show (|((0 : Function.locallyFinsuppWithin (closedBall (0 : ℂ) |R|) ℤ) u : ℤ)| : ℝ) ^ α = 0
      simp [Real.zero_rpow (ne_of_gt hα0)]
    rw [finsum_congr hzero, finsum_zero]
  rw [hfinsum, zero_mul, mul_zero, zero_add]
  have htrail : meromorphicTrailingCoeffAt (fun w => f w - a) 0 = f 0 - a :=
    (hg.analyticAt 0).meromorphicTrailingCoeffAt_of_ne_zero (hgne 0)
  rw [htrail]
  beta_reduce
  rw [max_self]

end GaloisForLFunctions.HTGeometry
