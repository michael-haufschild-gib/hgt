import Mathlib

/-!
# Single-cell Riemann-sum error bound

The per-cell error between an integral and its left-endpoint rectangle, for a function with a linear
modulus of continuity (in particular any Lipschitz function), absent from mathlib:

`‖∫_c^{c+h} f − h·f(c)‖ ≤ K·h²/2`   whenever  `‖f(x) − f(c)‖ ≤ K·(x − c)` on `[c, c+h]`.

Summed over a uniform partition this gives the `O(h)` convergence of Riemann sums of a Lipschitz
integrand — the uniform cellwise estimate underlying the moving-window Riemann-sum tomography lemmas.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace HTGeometry

/-- **Single-cell Riemann error.**  If `‖f(x) − f(c)‖ ≤ K·(x − c)` on the cell `[c, c+h]` (`h ≥ 0`),
the integral differs from the left-endpoint rectangle `h·f(c)` by at most `K·h²/2`. -/
theorem norm_integral_sub_smul_le {f : ℝ → ℂ} {K c h : ℝ} (hh : 0 ≤ h)
    (hint : IntervalIntegrable f volume c (c + h))
    (hbound : ∀ x ∈ Set.Icc c (c + h), ‖f x - f c‖ ≤ K * (x - c)) :
    ‖(∫ x in c..(c + h), f x) - h • f c‖ ≤ K * h ^ 2 / 2 := by
  have hcle : c ≤ c + h := by linarith
  have hconst : (∫ _x in c..(c + h), f c) = h • f c := by
    rw [intervalIntegral.integral_const]; congr 1; ring
  have hnorm_int : IntervalIntegrable (fun x => ‖f x - f c‖) volume c (c + h) :=
    (hint.sub (continuous_const.intervalIntegrable _ _)).norm
  have hlin_int : IntervalIntegrable (fun x => K * (x - c)) volume c (c + h) :=
    (by fun_prop : Continuous (fun x : ℝ => K * (x - c))).intervalIntegrable _ _
  have hxc : (∫ x in c..(c + h), (x - c)) = h ^ 2 / 2 := by
    have hd : ∀ x : ℝ, HasDerivAt (fun t : ℝ => (t - c) ^ 2 / 2) (x - c) x := by
      intro x
      have h2 := (((hasDerivAt_id x).sub_const c).pow 2).div_const 2
      convert h2 using 1
      simp only [id_eq]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      ((by fun_prop : Continuous (fun x : ℝ => x - c)).intervalIntegrable _ _)]
    ring
  rw [← hconst, ← intervalIntegral.integral_sub hint (continuous_const.intervalIntegrable _ _)]
  calc ‖∫ x in c..(c + h), (f x - f c)‖
      ≤ ∫ x in c..(c + h), ‖f x - f c‖ := intervalIntegral.norm_integral_le_integral_norm hcle
    _ ≤ ∫ x in c..(c + h), K * (x - c) :=
        intervalIntegral.integral_mono_on hcle hnorm_int hlin_int hbound
    _ = K * h ^ 2 / 2 := by rw [intervalIntegral.integral_const_mul, hxc]; ring

end HTGeometry
