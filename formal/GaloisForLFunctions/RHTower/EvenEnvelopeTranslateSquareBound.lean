import GaloisForLFunctions.RHTower.EvenHadamardRayRigidity

/-!
# Real-ray rigidity of even exponential translates that are squares

Let `f` be even and entire with an order-one envelope.  If `f(z) + c·exp(hz) = g(z)²` for an
entire `g`, with `c ≠ 0` and real `h ≠ 0`, then `f` is bounded by a fixed exponential on the
positive real ray.  The reflected square difference of `g` is the exponential pair
`c(exp(hz) - exp(-hz))`, so the even-Hadamard ray bound applies to `g`.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower.OrderOneHadamard

theorem exists_real_exp_bound_of_even_add_exp_eq_sq {f g : ℂ → ℂ} (hfo : OrderOneEnvelope f)
    (heven : ∀ z, f (-z) = f z) (hg : Differentiable ℂ g) {c : ℂ} (hc : c ≠ 0) {h : ℝ}
    (hh : h ≠ 0) (hsq : ∀ z, g z ^ 2 = f z + c * Complex.exp ((h : ℂ) * z)) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, 1 ≤ x → ‖f x‖ ≤ B * Real.exp (2 * |h| * x) := by
  have hgo : OrderOneEnvelope g :=
    (hfo.add ((orderOneEnvelope_exp_mul (h : ℂ)).const_mul c)).of_sq hsq
  have hrel : ∀ z : ℂ, g z ^ 2 - g (-z) ^ 2 =
      c * (Complex.exp ((h : ℂ) * z) - Complex.exp ((h : ℂ) * (-z))) := by
    intro z
    rw [hsq, hsq, heven]
    ring
  obtain ⟨A, hA, hAb⟩ := exists_real_exp_bound_of_reflected_square_difference hg hgo hc hh hrel
  refine ⟨A ^ 2 + ‖c‖, by positivity, fun x hx => ?_⟩
  have hgx := hAb x hx
  have hpow : ‖g x‖ ^ 2 ≤ A ^ 2 * Real.exp (2 * |h| * x) := by
    have hp := pow_le_pow_left₀ (norm_nonneg (g x)) hgx 2
    rw [mul_pow, ← Real.exp_nat_mul] at hp
    have he : ((2 : ℕ) : ℝ) * (|h| * x) = 2 * |h| * x := by push_cast; ring
    rwa [he] at hp
  have hexp : ‖Complex.exp ((h : ℂ) * (x : ℂ))‖ ≤ Real.exp (2 * |h| * x) := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    apply Real.exp_le_exp.mpr
    have hle : h ≤ 2 * |h| := by linarith [le_abs_self h, abs_nonneg h]
    nlinarith [mul_le_mul_of_nonneg_right hle (by linarith : (0 : ℝ) ≤ x)]
  have hfx : f x = g x ^ 2 - c * Complex.exp ((h : ℂ) * (x : ℂ)) := by
    linear_combination -(hsq (x : ℂ))
  have hn := norm_sub_le (g x ^ 2) (c * Complex.exp ((h : ℂ) * (x : ℂ)))
  rw [← hfx, norm_pow, norm_mul] at hn
  nlinarith [mul_le_mul_of_nonneg_left hexp (norm_nonneg c)]

end RHTower.OrderOneHadamard
