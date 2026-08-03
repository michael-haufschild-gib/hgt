import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# The antiderivative behind the Hilbert constant

The weighted row sums of the Hilbert–Hankel kernel are compared against the integral

```text
∫ dt / ((a + t) √t),
```

whose antiderivative is elementary:

```text
d/dt [ (2/√a) · arctan(√t/√a) ] = 1 / ((a + t) √t)      (a > 0, t > 0).
```

Since `arctan(√t/√a)` tends to `0` at `0` and to `π/2` at infinity, the improper integral over
`(0,∞)` is `π/√a` — the source of the constant `π` in the Hilbert inequality.
-/

open Real MeasureTheory

namespace GaloisForLFunctions

/-- **The elementary antiderivative.**  `(2/√a)·arctan(√t/√a)` differentiates to `1/((a+t)√t)`. -/
theorem hasDerivAt_arctan_sqrt_div {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => 2 / Real.sqrt a * Real.arctan (Real.sqrt x / Real.sqrt a))
      (1 / ((a + t) * Real.sqrt t)) t := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt t)) t :=
    Real.hasDerivAt_sqrt (ne_of_gt ht)
  have hdiv : HasDerivAt (fun x : ℝ => Real.sqrt x / Real.sqrt a)
      (1 / (2 * Real.sqrt t) / Real.sqrt a) t := hsqrt.div_const _
  have harctan := hdiv.arctan
  have hscale := harctan.const_mul (2 / Real.sqrt a)
  have hval : 2 / Real.sqrt a *
        (1 / (1 + (Real.sqrt t / Real.sqrt a) ^ 2) * (1 / (2 * Real.sqrt t) / Real.sqrt a))
      = 1 / ((a + t) * Real.sqrt t) := by
    have hsa2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
    have hst2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
    have hpos : 0 < 1 + (Real.sqrt t / Real.sqrt a) ^ 2 := by positivity
    field_simp
    nlinarith [hsa2, hst2, hsa, hst, mul_pos hsa hst]
  rw [hval] at hscale
  exact hscale

/-! ## The endpoint values -/

/-- At the origin the antiderivative vanishes. -/
theorem arctan_sqrt_div_zero {a : ℝ} :
    2 / Real.sqrt a * Real.arctan (Real.sqrt 0 / Real.sqrt a) = 0 := by
  rw [Real.sqrt_zero, zero_div, Real.arctan_zero, mul_zero]

/-- At infinity the antiderivative tends to `π/√a`, which is the value of the improper integral. -/
theorem tendsto_arctan_sqrt_div_atTop {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (fun t : ℝ => 2 / Real.sqrt a * Real.arctan (Real.sqrt t / Real.sqrt a))
      Filter.atTop (nhds (Real.pi / Real.sqrt a)) := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsqrt : Filter.Tendsto (fun t : ℝ => Real.sqrt t) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop
  have hdiv : Filter.Tendsto (fun t : ℝ => Real.sqrt t / Real.sqrt a) Filter.atTop
      Filter.atTop := hsqrt.atTop_div_const hsa
  have harctan := Real.tendsto_arctan_atTop.comp hdiv
  have hnhds : Filter.Tendsto (fun t : ℝ => Real.arctan (Real.sqrt t / Real.sqrt a))
      Filter.atTop (nhds (Real.pi / 2)) := harctan.mono_right nhdsWithin_le_nhds
  have hmul := hnhds.const_mul (2 / Real.sqrt a)
  have hval : 2 / Real.sqrt a * (Real.pi / 2) = Real.pi / Real.sqrt a := by
    field_simp
  rwa [hval] at hmul

/-! ## The improper integral -/

/-- **The integral behind the Hilbert constant.**  `∫₀^∞ dt / ((a + t) √t) = π / √a`. -/
theorem integral_Ioi_one_div_add_mul_sqrt {a : ℝ} (ha : 0 < a) :
    (∫ t in Set.Ioi (0:ℝ), 1 / ((a + t) * Real.sqrt t)) = Real.pi / Real.sqrt a := by
  have hcont : ContinuousWithinAt
      (fun t : ℝ => 2 / Real.sqrt a * Real.arctan (Real.sqrt t / Real.sqrt a))
      (Set.Ici (0:ℝ)) 0 := by
    have : Continuous fun t : ℝ =>
        2 / Real.sqrt a * Real.arctan (Real.sqrt t / Real.sqrt a) := by fun_prop
    exact this.continuousWithinAt
  have hderiv : ∀ t ∈ Set.Ioi (0:ℝ),
      HasDerivAt (fun x : ℝ => 2 / Real.sqrt a * Real.arctan (Real.sqrt x / Real.sqrt a))
        (1 / ((a + t) * Real.sqrt t)) t := fun t ht => hasDerivAt_arctan_sqrt_div ha ht
  have hnonneg : ∀ t ∈ Set.Ioi (0:ℝ), 0 ≤ 1 / ((a + t) * Real.sqrt t) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    positivity
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnonneg
    (tendsto_arctan_sqrt_div_atTop ha)
  rw [h, arctan_sqrt_div_zero, sub_zero]

end GaloisForLFunctions
