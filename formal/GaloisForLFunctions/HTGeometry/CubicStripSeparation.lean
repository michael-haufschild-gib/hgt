import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Odd cubic branches and small-value strip regions

For `(f-3)f²=4d`, an odd zero of d forces f=3. In a connected region where
the cubic product has norm below two, the presence of f=3 excludes f=0.
Both oriented closed critical-strip tails provide such connected regions.
-/

namespace GaloisForLFunctions.HTGeometry
open Complex Set

/-- The simple cubic branch prevents the double branch from appearing in one small-value region. -/
theorem cubic_no_zero_on_small_connected_region {S : Set ℂ} (hS : IsPreconnected S)
    {f : ℂ → ℂ} (hf : ContinuousOn f S)
    (hsmall : ∀ z ∈ S, ‖(f z - 3) * f z ^ 2‖ < 2)
    {p : ℂ} (hp : p ∈ S) (hfp : f p = 3) :
    ∀ z ∈ S, f z ≠ 0 := by
  intro z hz hzero
  have hbetween : (1 : ℝ) ∈ Icc ‖f z‖ ‖f p‖ := by
    simp [hzero, hfp]
  obtain ⟨w, hw, hnorm⟩ := hS.intermediate_value hz hp hf.norm hbetween
  change ‖f w‖ = 1 at hnorm
  have hbound := norm_sub_norm_le (3 : ℂ) (f w)
  rw [norm_sub_rev] at hbound
  norm_num [hnorm] at hbound
  have hbad := hsmall w hw
  rw [norm_mul, norm_pow, hnorm, one_pow, mul_one] at hbad
  linarith

/-- At an odd source zero, a cubic lift takes the simple branch value. -/
theorem cubic_simple_branch_of_odd_order {f d : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z)
    (hrel : ∀ w, (f w - 3) * f w ^ 2 = 4 * d w)
    (hz : d z = 0) (hodd : Odd (analyticOrderAt d z).toNat) : f z = 3 := by
  have heq : (f z - 3) * f z ^ 2 = 0 := by rw [hrel, hz, mul_zero]
  rcases mul_eq_zero.mp heq with hs | hs
  · exact sub_eq_zero.mp hs
  · have hfz : f z = 0 := (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hs
    have hu : AnalyticAt ℂ (fun w => (f w - 3) / 4) z :=
      (hf.sub analyticAt_const).div analyticAt_const (by norm_num)
    have hu0 : (f z - 3) / 4 ≠ 0 := by rw [hfz]; norm_num
    have hfun : d = fun w => f w ^ 2 * ((f w - 3) / 4) := by
      funext w
      have h := hrel w
      linear_combination -(1 / 4 : ℂ) * h
    have hord : analyticOrderAt d z = 2 • analyticOrderAt f z := by
      rw [hfun]
      have hmul := analyticOrderAt_mul (hf.pow 2) hu
      change analyticOrderAt (fun w => f w ^ 2 * ((f w - 3) / 4)) z = _ at hmul
      rw [hmul, analyticOrderAt_pow hf, hu.analyticOrderAt_eq_zero.mpr hu0, add_zero]
    have heven : Even (analyticOrderAt d z).toNat := by
      rw [hord, nsmul_eq_mul, ENat.toNat_mul]
      exact even_two.mul_right _
    exact False.elim ((Nat.not_even_iff_odd.mpr hodd) heven)

/-- Both orientations of a closed vertical strip tail are connected. -/
theorem isPreconnected_vertical_strip_tail (T side : ℝ) :
    IsPreconnected {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ T ≤ side * z.im} := by
  have hc : Convex ℝ {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ T ≤ side * z.im} := by
    intro x hx y hy a b ha hb hab
    change 0 ≤ (a • x + b • y).re ∧ (a • x + b • y).re ≤ 1 ∧
      T ≤ side * (a • x + b • y).im
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
      smul_eq_mul]
    refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1), ?_, ?_⟩
    · nlinarith [mul_nonneg ha (sub_nonneg.mpr hx.2.1),
        mul_nonneg hb (sub_nonneg.mpr hy.2.1)]
    · have hT : (a + b) * T = T := by rw [hab, one_mul]
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hx.2.2),
        mul_nonneg hb (sub_nonneg.mpr hy.2.2)]
  exact hc.isPreconnected

end GaloisForLFunctions.HTGeometry
