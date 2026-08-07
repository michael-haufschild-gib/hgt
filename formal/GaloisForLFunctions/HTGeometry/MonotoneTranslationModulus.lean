import Mathlib

/-!
# The `L¹` modulus of continuity of a monotone function

For a monotone function the translation difference telescopes exactly:

`∫_a^b (g(x+h) − g(x)) dx = ∫_b^{b+h} g − ∫_a^{a+h} g`,

because translating the variable moves the window rather than the function.  Monotonicity bounds
the two short windows by their endpoint values, giving

`∫_a^b |g(x+h) − g(x)| dx ≤ h · (g(b+h) − g(a))`.

The right-hand side is the variation of `g` across the enlarged window, so this is the `L¹`
modulus of continuity of a bounded-variation function in the monotone case.  No differentiability
is used anywhere — which is the point, since a monotone profile may have infinite one-sided
derivative.
-/

open MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

/-- A translate of a monotone function is monotone. -/
theorem monotone_comp_add_right {g : ℝ → ℝ} (hg : Monotone g) (h : ℝ) :
    Monotone fun x => g (x + h) := fun _ _ hpq => hg (by linarith)

/-- **The translation difference telescopes.**  Shifting the variable of a monotone function moves
the integration window, so the difference of the two integrals is the difference of the two short
end windows. -/
theorem integral_translate_sub_eq_end_windows {g : ℝ → ℝ} (hg : Monotone g) (a b h : ℝ) :
    (∫ x in a..b, (g (x + h) - g x)) = (∫ x in b..(b + h), g x) - ∫ x in a..(a + h), g x := by
  have hgi : ∀ p q : ℝ, IntervalIntegrable g volume p q := fun _ _ => hg.intervalIntegrable
  have hti : ∀ p q : ℝ, IntervalIntegrable (fun x => g (x + h)) volume p q := fun _ _ =>
    (monotone_comp_add_right hg h).intervalIntegrable
  rw [intervalIntegral.integral_sub (hti a b) (hgi a b),
    intervalIntegral.integral_comp_add_right g h]
  have h1 : (∫ x in a..(a + h), g x) + ∫ x in (a + h)..(b + h), g x = ∫ x in a..(b + h), g x :=
    intervalIntegral.integral_add_adjacent_intervals (hgi _ _) (hgi _ _)
  have h2 : (∫ x in a..b, g x) + ∫ x in b..(b + h), g x = ∫ x in a..(b + h), g x :=
    intervalIntegral.integral_add_adjacent_intervals (hgi _ _) (hgi _ _)
  linarith

/-- A short window of a monotone function is bounded above by its length times the right endpoint
value. -/
theorem integral_le_length_mul_right {g : ℝ → ℝ} (hg : Monotone g) {c h : ℝ} (hh : 0 ≤ h) :
    (∫ x in c..(c + h), g x) ≤ h * g (c + h) := by
  have hle : c ≤ c + h := by linarith
  have hmono : (∫ x in c..(c + h), g x) ≤ ∫ _x in c..(c + h), g (c + h) :=
    intervalIntegral.integral_mono_on hle hg.intervalIntegrable
      intervalIntegrable_const fun x hx => hg hx.2
  rwa [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at hmono

/-- A short window of a monotone function is bounded below by its length times the left endpoint
value. -/
theorem length_mul_left_le_integral {g : ℝ → ℝ} (hg : Monotone g) {c h : ℝ} (hh : 0 ≤ h) :
    h * g c ≤ ∫ x in c..(c + h), g x := by
  have hle : c ≤ c + h := by linarith
  have hmono : (∫ _x in c..(c + h), g c) ≤ ∫ x in c..(c + h), g x :=
    intervalIntegral.integral_mono_on hle intervalIntegrable_const
      hg.intervalIntegrable fun x hx => hg hx.1
  rwa [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at hmono

/-- **The `L¹` modulus of continuity of a monotone function.**  The translation difference over a
window is bounded by the shift times the variation of `g` across the enlarged window. -/
theorem integral_translate_sub_le {g : ℝ → ℝ} (hg : Monotone g) {a b h : ℝ} (hh : 0 ≤ h) :
    (∫ x in a..b, (g (x + h) - g x)) ≤ h * (g (b + h) - g a) := by
  rw [integral_translate_sub_eq_end_windows hg a b h]
  have hup := integral_le_length_mul_right hg (c := b) hh
  have hlow := length_mul_left_le_integral hg (c := a) hh
  nlinarith [hup, hlow]

/-- **The `L¹` modulus of continuity in absolute value.**  For a monotone function and a
nonnegative shift the integrand is already nonnegative, so the absolute value costs nothing. -/
theorem integral_abs_translate_sub_le {g : ℝ → ℝ} (hg : Monotone g) {a b h : ℝ} (hab : a ≤ b)
    (hh : 0 ≤ h) :
    (∫ x in a..b, |g (x + h) - g x|) ≤ h * (g (b + h) - g a) := by
  have hcongr : (∫ x in a..b, |g (x + h) - g x|) = ∫ x in a..b, (g (x + h) - g x) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    exact abs_of_nonneg (sub_nonneg.mpr (hg (by linarith)))
  rw [hcongr]
  exact integral_translate_sub_le hg hh

/-- **The bound in terms of the total rise.**  If a monotone function rises by at most `V` across
the whole enlarged window, its `L¹` translation modulus is at most `V · h`.  This is the estimate
that feeds the fractional Sobolev criterion. -/
theorem integral_abs_translate_sub_le_variation {g : ℝ → ℝ} (hg : Monotone g) {a b h V : ℝ}
    (hab : a ≤ b) (hh : 0 ≤ h) (hV : g (b + h) - g a ≤ V) :
    (∫ x in a..b, |g (x + h) - g x|) ≤ V * h := by
  have hmain := integral_abs_translate_sub_le hg hab hh
  nlinarith [hmain, hV, hh]

end GaloisForLFunctions.HTGeometry
