import GaloisForLFunctions.RHTower.CompletedZetaGrowth
import GaloisForLFunctions.RHTower.XiGlobalKummerSquareClasses
import GaloisForLFunctions.RHTower.EvenHadamardRayRigidity

/-!
# Global nonsquareness of exponential translates of Xi

The functional equation, order-one envelope, and real-axis growth of Xi exclude
a global meromorphic square root of every nonconstant real exponential translate.
The same obstruction applies to the positive-on-real-axis companion of a deletion factor.
-/

open Complex Filter Topology

namespace RHTower.XiGlobalKummer
open GaloisForLFunctions.HTGeometry

/-- No nonconstant real exponential translate of Xi has a global entire square root. -/
theorem not_exists_entire_sqrt_xi_add_exp {h : ℝ} (hh : h ≠ 0)
    {c : ℂ} (hc : c ≠ 0) :
    ¬ ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ s, g s ^ 2 = xi s + c * Complex.exp ((h : ℂ) * s) := by
  rintro ⟨g, hgd, hsq⟩
  have hxiO : OrderOneEnvelope xi := xi_growth_order_le_one
  have hgO := (hxiO.add ((orderOneEnvelope_exp_mul (h : ℂ)).const_mul c)).of_sq hsq
  let G : ℂ → ℂ := fun z => g (1 / 2 + z)
  have hGd : Differentiable ℂ G := by dsimp [G]; fun_prop
  have hGO : OrderOneEnvelope G :=
    (hgO.comp_affine 1 (1 / 2)).congr (fun z => by dsimp [G]; congr 1; ring)
  let C : ℂ := c * Complex.exp ((h : ℂ) / 2)
  have hC : C ≠ 0 := mul_ne_zero hc (Complex.exp_ne_zero _)
  have hrel (z : ℂ) : G z ^ 2 - G (-z) ^ 2 =
      C * (Complex.exp ((h : ℂ) * z) - Complex.exp ((h : ℂ) * (-z))) := by
    have hsym : xi (1 / 2 + -z) = xi (1 / 2 + z) := by
      convert xi_one_sub (1 / 2 + z) using 1; congr 1; ring
    have hexp (w : ℂ) : Complex.exp ((h : ℂ) * (1 / 2 + w)) =
        Complex.exp ((h : ℂ) / 2) * Complex.exp ((h : ℂ) * w) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    dsimp [G, C]
    rw [hsq, hsq, hsym, hexp, hexp]
    ring
  obtain ⟨A, hA, hAb⟩ :=
    OrderOneHadamard.exists_real_exp_bound_of_reflected_square_difference hGd hGO hC hh hrel
  let M : ℝ := A ^ 2 + ‖c‖
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨m, hm⟩ := (eventually_lt_log_norm_xi (2 * |h| + M)).exists
  let t : ℝ := 2 * ((m : ℝ) + 1)
  have ht : 2 ≤ t := by dsimp [t]; have := Nat.cast_nonneg (α := ℝ) m; linarith
  have htcast : (t : ℂ) = 2 * ((m : ℂ) + 1) := by dsimp [t]; push_cast; rfl
  have hlarge : Real.exp ((2 * |h| + M) * t) < ‖xi (t : ℂ)‖ := by
    rw [← htcast] at hm
    exact (Real.lt_log_iff_exp_lt (norm_pos_iff.mpr (xi_ne_zero_of_real t))).mp hm
  have hgb : ‖g (t : ℂ)‖ ≤ A * Real.exp (|h| * t) := by
    have hb := hAb (t - 1 / 2) (by linarith)
    have harg : G ((t - 1 / 2 : ℝ) : ℂ) = g (t : ℂ) := by
      dsimp [G]
      congr 1
      push_cast
      ring
    rw [harg] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [abs_nonneg h])) hA.le)
  have hpow : ‖g (t : ℂ)‖ ^ 2 ≤ A ^ 2 * Real.exp (2 * |h| * t) := by
    have hp := pow_le_pow_left₀ (norm_nonneg (g (t : ℂ))) hgb 2
    rw [mul_pow, ← Real.exp_nat_mul] at hp
    convert hp using 1; congr 1; ring
  have hexp : ‖Complex.exp ((h : ℂ) * (t : ℂ))‖ ≤ Real.exp (2 * |h| * t) := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    apply Real.exp_le_exp.mpr
    have hle : h ≤ 2 * |h| := by linarith [le_abs_self h, abs_nonneg h]
    nlinarith [mul_le_mul_of_nonneg_right hle (by linarith : 0 ≤ t)]
  have hxiB : ‖xi (t : ℂ)‖ ≤ M * Real.exp (2 * |h| * t) := by
    have hxiEq : xi (t : ℂ) = g (t : ℂ) ^ 2 - c * Complex.exp ((h : ℂ) * (t : ℂ)) := by
      linear_combination -(hsq (t : ℂ))
    have hn := norm_sub_le (g (t : ℂ) ^ 2) (c * Complex.exp ((h : ℂ) * (t : ℂ)))
    rw [← hxiEq, norm_pow, norm_mul] at hn
    dsimp [M]
    nlinarith [mul_le_mul_of_nonneg_left hexp (norm_nonneg c)]
  have hMexp : M ≤ Real.exp (M * t) := by
    have := Real.add_one_le_exp (M * t)
    nlinarith
  have hupper : ‖xi (t : ℂ)‖ ≤ Real.exp ((2 * |h| + M) * t) := by
    calc ‖xi (t : ℂ)‖ ≤ M * Real.exp (2 * |h| * t) := hxiB
      _ ≤ Real.exp (M * t) * Real.exp (2 * |h| * t) :=
        mul_le_mul_of_nonneg_right hMexp (Real.exp_pos _).le
      _ = Real.exp ((2 * |h| + M) * t) := by rw [← Real.exp_add]; congr 1; ring
  exact (not_lt_of_ge hupper) hlarge

/-- The same obstruction holds in the field of global meromorphic functions. -/
theorem xi_add_exp_not_isSquare_plane {h : ℝ} (hh : h ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    ¬ IsSquare (ofMeromorphic (fun s : ℂ => xi s + c * Complex.exp ((h : ℂ) * s))
      (fun z => ((xi_differentiable.add
        (show Differentiable ℂ (fun s : ℂ => c * Complex.exp ((h : ℂ) * s)) by fun_prop)).analyticAt z).meromorphicAt)) := by
  intro hs
  exact not_exists_entire_sqrt_xi_add_exp hh hc
    (entire_sqrt_of_isSquare_plane (xi_differentiable.add (by fun_prop)) hs)

end RHTower.XiGlobalKummer

namespace RHTower.XiGlobalKummer
open GaloisForLFunctions.HTGeometry

/-- The positive-on-real-axis companion of each deletion factor is globally nonsquare. -/
theorem not_exists_entire_sqrt_one_add_exp_mul_xi {h : ℝ} (hh : h ≠ 0) :
    ¬ ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ s, g s ^ 2 = 1 + Complex.exp ((h : ℂ) * s) * xi s := by
  rintro ⟨g, hgd, hsq⟩
  apply not_exists_entire_sqrt_xi_add_exp (neg_ne_zero.mpr hh) (c := 1) one_ne_zero
  refine ⟨fun s => Complex.exp (-(h : ℂ) * s / 2) * g s, by fun_prop, fun s => ?_⟩
  have hp : Complex.exp (-(h : ℂ) * s / 2) ^ 2 = Complex.exp (-(h : ℂ) * s) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have hi : Complex.exp (-(h : ℂ) * s) * Complex.exp ((h : ℂ) * s) = 1 := by
    rw [← Complex.exp_add, show -(h : ℂ) * s + (h : ℂ) * s = 0 by ring, Complex.exp_zero]
  rw [mul_pow, hp, hsq]
  push_cast
  linear_combination xi s * hi

theorem one_add_exp_mul_xi_not_isSquare_plane {h : ℝ} (hh : h ≠ 0) :
    ¬ IsSquare (ofMeromorphic (fun s : ℂ => 1 + Complex.exp ((h : ℂ) * s) * xi s)
      (fun z => ((show Differentiable ℂ (fun s : ℂ => 1 + Complex.exp ((h : ℂ) * s) * xi s)
        by have := xi_differentiable; fun_prop).analyticAt z).meromorphicAt)) := by
  intro hs
  apply not_exists_entire_sqrt_one_add_exp_mul_xi hh
  exact entire_sqrt_of_isSquare_plane (by have := xi_differentiable; fun_prop) hs

end RHTower.XiGlobalKummer
