import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Hölder and Fubini for continuous interval integrals

* **Cauchy–Schwarz:** `(∫_a^b gh)² ≤ (∫_a^b g²)(∫_a^b h²)` for continuous `g, h`
  (`sq_intervalIntegral_mul_le`).  The quadratic `s ↦ ∫(sg − h)²` is nonnegative, so its
  discriminant is nonpositive.
* **Weighted fourth-power Hölder:** `(∫ f w)⁴ ≤ (∫ w)³ ∫ f⁴ w` for continuous `f, w ≥ 0`
  (`intervalIntegral_mul_pow_four_le`), by Cauchy–Schwarz twice with the factor `√w`.
* **Fubini:** iterated interval integrals of a jointly continuous function commute
  (`intervalIntegral_integral_swap_of_continuous`).
-/

open MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Cauchy–Schwarz for interval integrals of continuous functions.** -/
theorem sq_intervalIntegral_mul_le {g h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hg : Continuous g)
    (hh : Continuous h) :
    (∫ x in a..b, g x * h x) ^ 2 ≤ (∫ x in a..b, g x ^ 2) * ∫ x in a..b, h x ^ 2 := by
  have hq : ∀ s : ℝ, 0 ≤ (∫ x in a..b, g x ^ 2) * (s * s) +
      (-2 * ∫ x in a..b, g x * h x) * s + ∫ x in a..b, h x ^ 2 := by
    intro s
    have hpos : 0 ≤ ∫ x in a..b, (s * g x - h x) ^ 2 :=
      integral_nonneg hab fun x _ => sq_nonneg _
    have i1 : IntervalIntegrable (fun x => s * s * g x ^ 2) volume a b :=
      (continuous_const.mul (hg.pow 2)).intervalIntegrable a b
    have i2 : IntervalIntegrable (fun x => -2 * s * (g x * h x)) volume a b :=
      (continuous_const.mul (hg.mul hh)).intervalIntegrable a b
    have i3 : IntervalIntegrable (fun x => h x ^ 2) volume a b := (hh.pow 2).intervalIntegrable a b
    have hexp : ∫ x in a..b, (s * g x - h x) ^ 2 = (∫ x in a..b, g x ^ 2) * (s * s) +
        (-2 * ∫ x in a..b, g x * h x) * s + ∫ x in a..b, h x ^ 2 := by
      have e : ∀ x, (s * g x - h x) ^ 2 = s * s * g x ^ 2 + -2 * s * (g x * h x) +
          h x ^ 2 := fun x => by ring
      simp_rw [e]
      rw [integral_add (i1.add i2) i3, integral_add i1 i2, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      ring
    linarith
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith

/-- **Weighted fourth-power Hölder.**  For continuous `f, w ≥ 0` on `[a, b]`,
`(∫ f w)⁴ ≤ (∫ w)³ ∫ f⁴ w`. -/
theorem intervalIntegral_mul_pow_four_le {f w : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : Continuous f) (hw : Continuous w) (hf0 : ∀ x, 0 ≤ f x) (hw0 : ∀ x, 0 ≤ w x) :
    (∫ x in a..b, f x * w x) ^ 4 ≤ (∫ x in a..b, w x) ^ 3 * ∫ x in a..b, f x ^ 4 * w x := by
  have hs : Continuous fun x => Real.sqrt (w x) := Real.continuous_sqrt.comp hw
  have hss : ∀ x, Real.sqrt (w x) * Real.sqrt (w x) = w x := fun x => Real.mul_self_sqrt (hw0 x)
  -- `(∫ f w)² ≤ (∫ f² w)(∫ w)`
  have e3 : (∫ x in a..b, Real.sqrt (w x) ^ 2) = ∫ x in a..b, w x :=
    integral_congr fun x _ => Real.sq_sqrt (hw0 x)
  have c1 : (∫ x in a..b, f x * w x) ^ 2 ≤ (∫ x in a..b, f x ^ 2 * w x) * ∫ x in a..b, w x := by
    have h := sq_intervalIntegral_mul_le (g := fun x => f x * Real.sqrt (w x))
      (h := fun x => Real.sqrt (w x)) hab (hf.mul hs) hs
    beta_reduce at h
    have e1 : (∫ x in a..b, f x * Real.sqrt (w x) * Real.sqrt (w x)) = ∫ x in a..b, f x * w x :=
      integral_congr fun x _ => by rw [mul_assoc, hss]
    have e2 : (∫ x in a..b, (f x * Real.sqrt (w x)) ^ 2) = ∫ x in a..b, f x ^ 2 * w x :=
      integral_congr fun x _ => by rw [mul_pow, Real.sq_sqrt (hw0 x)]
    rwa [e1, e2, e3] at h
  -- `(∫ f² w)² ≤ (∫ f⁴ w)(∫ w)`
  have c2 : (∫ x in a..b, f x ^ 2 * w x) ^ 2 ≤
      (∫ x in a..b, f x ^ 4 * w x) * ∫ x in a..b, w x := by
    have h := sq_intervalIntegral_mul_le (g := fun x => f x ^ 2 * Real.sqrt (w x))
      (h := fun x => Real.sqrt (w x)) hab ((hf.pow 2).mul hs) hs
    beta_reduce at h
    have e1 : (∫ x in a..b, f x ^ 2 * Real.sqrt (w x) * Real.sqrt (w x)) =
        ∫ x in a..b, f x ^ 2 * w x :=
      integral_congr fun x _ => by rw [mul_assoc, hss]
    have e2 : (∫ x in a..b, (f x ^ 2 * Real.sqrt (w x)) ^ 2) = ∫ x in a..b, f x ^ 4 * w x :=
      integral_congr fun x _ => by rw [mul_pow, Real.sq_sqrt (hw0 x)]; ring
    rwa [e1, e2, e3] at h
  have hW : 0 ≤ ∫ x in a..b, w x := integral_nonneg hab fun x _ => hw0 x
  have hF2 : 0 ≤ ∫ x in a..b, f x ^ 2 * w x :=
    integral_nonneg hab fun x _ => mul_nonneg (sq_nonneg _) (hw0 x)
  have hF1 : 0 ≤ ∫ x in a..b, f x * w x := integral_nonneg hab fun x _ => mul_nonneg (hf0 x) (hw0 x)
  calc (∫ x in a..b, f x * w x) ^ 4 = ((∫ x in a..b, f x * w x) ^ 2) ^ 2 := by ring
    _ ≤ ((∫ x in a..b, f x ^ 2 * w x) * ∫ x in a..b, w x) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) c1 2
    _ = (∫ x in a..b, f x ^ 2 * w x) ^ 2 * (∫ x in a..b, w x) ^ 2 := by ring
    _ ≤ ((∫ x in a..b, f x ^ 4 * w x) * ∫ x in a..b, w x) * (∫ x in a..b, w x) ^ 2 :=
        mul_le_mul_of_nonneg_right c2 (sq_nonneg _)
    _ = (∫ x in a..b, w x) ^ 3 * ∫ x in a..b, f x ^ 4 * w x := by ring

/-- **Fubini for interval integrals of a jointly continuous function.** -/
theorem intervalIntegral_integral_swap_of_continuous {F : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ x in a..b, ∫ y in c..d, F x y = ∫ y in c..d, ∫ x in a..b, F x y := by
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  refine integral_integral_swap ?_
  rw [Measure.prod_restrict]
  exact (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

end

end GaloisForLFunctions.HTGeometry
