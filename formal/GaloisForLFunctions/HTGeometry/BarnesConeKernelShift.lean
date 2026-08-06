import GaloisForLFunctions.HTGeometry.BarnesSingleZetaContinuation

/-!
# The shift identity of the Barnes cone kernel

Shifting the argument of the cone kernel by one period multiplies it by `e^(-omega t)`, and the
complementary factor `1 - e^(-omega t)` cancels one of the two geometric denominators:

```text
F_2(x,t) = F_2(x + omega_1, t) + F_1(omega_2; x, t).
```

This is the kernel-level form of the double zeta's shift equation, and it is an exact algebraic
identity rather than a statement about series, so it transports directly to every object built from
the kernel.
-/

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem cone_shift_algebra (E a b : ℂ) (ha : (1 : ℂ) - a ≠ 0) (hb : (1 : ℂ) - b ≠ 0) :
    E / ((1 - a) * (1 - b)) = E * a / ((1 - a) * (1 - b)) + E / (1 - b) := by
  field_simp
  ring

/-- **The cone kernel's shift identity.**  Shifting the argument by a period peels off one ray:
`F₂(x,t) = F₂(x+ω₁,t) + F₁(ω₂;x,t)`. -/
theorem barnesConeKernel_shift {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) (x : ℝ) {t : ℝ}
    (ht : 0 < t) :
    barnesConeKernel o1 o2 x t
      = barnesConeKernel o1 o2 (x + o1) t + barnesRayKernel o2 x t := by
  have hd1 : (1 : ℂ) - ((Real.exp (-o1 * t) : ℝ) : ℂ) ≠ 0 := by
    intro hcon
    have hz : ‖(1 : ℂ) - ((Real.exp (-o1 * t) : ℝ) : ℂ)‖ = 0 := by rw [hcon, norm_zero]
    rw [norm_one_sub_exp_neg_mul_ofReal h1 ht] at hz
    linarith [one_sub_exp_neg_mul_ofReal_pos h1 ht]
  have hd2 : (1 : ℂ) - ((Real.exp (-o2 * t) : ℝ) : ℂ) ≠ 0 := by
    intro hcon
    have hz : ‖(1 : ℂ) - ((Real.exp (-o2 * t) : ℝ) : ℂ)‖ = 0 := by rw [hcon, norm_zero]
    rw [norm_one_sub_exp_neg_mul_ofReal h2 ht] at hz
    linarith [one_sub_exp_neg_mul_ofReal_pos h2 ht]
  have hexp : ((Real.exp (-(x + o1) * t) : ℝ) : ℂ)
      = ((Real.exp (-x * t) : ℝ) : ℂ) * ((Real.exp (-o1 * t) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  rw [barnesConeKernel, barnesConeKernel, barnesRayKernel, hexp]
  exact cone_shift_algebra _ _ _ hd1 hd2

end

end GaloisForLFunctions.HTGeometry
