/-
# Complex-polynomial asymptotics at the real ray (missing from Mathlib)

Mathlib's polynomial growth asymptotics (`Analysis/Polynomial/Basic.lean`) are stated only for
*ordered* fields (`ℝ[X]` at real `±∞`). For the n=2 Böttcher degree-forcing we need the analogue for
`ℂ[X]` evaluated along the real ray. The clean route is the reverse polynomial:
`p.eval(t)/t^{deg p} = (reverse p).eval(1/t)` (`Polynomial.eval₂_reverse_mul_pow`), which tends to
`(reverse p).eval(0) = leadingCoeff p` (`coeff_zero_reverse`) by continuity as `1/t → 0`.

* `tendsto_eval_div_pow_natDegree` — `p.eval(t)/t^{deg p} → leadingCoeff p`.
-/
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Topology.Algebra.Polynomial

open Polynomial Filter Topology

namespace PolyAsymptotics

/-- `(t : ℂ)⁻¹ → 0` as the real `t → +∞`. -/
@[aesop safe]
theorem tendsto_inv_ofReal_atTop : Tendsto (fun t : ℝ => ((t : ℂ))⁻¹) atTop (𝓝 0) := by
  have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
  simp only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_zero] at h
  exact h

/-- **`p.eval(t)/t^{deg p} → leadingCoeff p` (PROVED).** Via the reverse polynomial identity
`p.eval(t)/t^d = (reverse p).eval(1/t)` and continuity of `eval` at `1/t → 0`, where
`(reverse p).eval 0 = (reverse p).coeff 0 = leadingCoeff p`. -/
@[aesop safe]
theorem tendsto_eval_div_pow_natDegree (p : ℂ[X]) :
    Tendsto (fun t : ℝ => p.eval (t : ℂ) / (t : ℂ) ^ p.natDegree) atTop
      (𝓝 p.leadingCoeff) := by
  have heval0 : (p.reverse).eval (0 : ℂ) = p.leadingCoeff := by
    rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse]
  have hrev : Tendsto (fun t : ℝ => (p.reverse).eval ((t : ℂ)⁻¹)) atTop (𝓝 p.leadingCoeff) := by
    have hcont := (p.reverse).continuous.tendsto (0 : ℂ)
    rw [heval0] at hcont
    exact hcont.comp tendsto_inv_ofReal_atTop
  refine hrev.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  rw [eq_div_iff (pow_ne_zero _ ht0)]
  letI : Invertible (t : ℂ) := invertibleOfNonzero ht0
  have key := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) (t : ℂ) p
  rw [show (⅟(t : ℂ)) = (t : ℂ)⁻¹ from rfl] at key
  exact key

/-- **Degree-forcing (PROVED).** If `p.eval(t)/t → L` (a finite limit) along the real ray, then
`deg p ≤ 1`. If instead `deg p ≥ 2`, then `‖p.eval(t)/t‖ = ‖p.eval(t)/t^{deg p}‖ · t^{deg p − 1}` tends to
`‖leadingCoeff‖ · ∞ = ∞`, contradicting the finite limit. This is the missing-from-Mathlib input that
forces `deg b₁ = 1` in the n=2 Böttcher case. -/
@[aesop safe]
theorem natDegree_le_one_of_div_id_tendsto {p : ℂ[X]} {L : ℂ}
    (h : Tendsto (fun t : ℝ => p.eval (t : ℂ) / (t : ℂ)) atTop (𝓝 L)) : p.natDegree ≤ 1 := by
  by_contra hd
  rw [not_le] at hd
  have hp0 : p ≠ 0 := fun h0 => by simp [h0] at hd
  have hbdd : Tendsto (fun t : ℝ => ‖p.eval (t : ℂ) / (t : ℂ)‖) atTop (𝓝 ‖L‖) :=
    (continuous_norm.tendsto L).comp h
  have h1 : Tendsto (fun t : ℝ => ‖p.eval (t : ℂ) / (t : ℂ) ^ p.natDegree‖) atTop
      (𝓝 ‖p.leadingCoeff‖) := (continuous_norm.tendsto _).comp (tendsto_eval_div_pow_natDegree p)
  have h2 : Tendsto (fun t : ℝ => t ^ (p.natDegree - 1)) atTop atTop :=
    tendsto_pow_atTop (by omega)
  have h3 : Tendsto (fun t : ℝ => ‖p.eval (t : ℂ) / (t : ℂ) ^ p.natDegree‖ * t ^ (p.natDegree - 1))
      atTop atTop :=
    Filter.Tendsto.pos_mul_atTop (norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hp0)) h1 h2
  have hinf : Tendsto (fun t : ℝ => ‖p.eval (t : ℂ) / (t : ℂ)‖) atTop atTop := by
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [norm_div, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
        div_mul_eq_mul_div, mul_div_assoc]
    congr 1
    rw [show t ^ p.natDegree = t ^ (p.natDegree - 1) * t from by rw [← pow_succ]; congr 1; omega,
        div_mul_eq_div_div, div_self (pow_ne_zero _ (ne_of_gt ht)), one_div]
  exact not_tendsto_nhds_of_tendsto_atTop hinf _ hbdd

end PolyAsymptotics
