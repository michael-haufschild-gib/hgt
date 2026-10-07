import GaloisForLFunctions.HTGeometry.SchottkyRationalGrowth
import GaloisForLFunctions.RHTower.XiPolynomialLeftFactors

/-!
# Entire rational lifts of tilted Xi

Coprimality makes the denominator nowhere zero along the lift. Any finite
outer pole, together with an actual Xi zero, forces an exponential ray bound
and contradicts Xi growth. Thus the denominator is constant and the numerator
is linear, for every real exponential tilt.
-/

open Complex Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- An entire rational lift of tilted Xi has constant denominator and linear numerator. -/
theorem xi_entire_rational_left_factor_degrees (a : ℝ) (p q : Polynomial ℂ)
    (hpq : IsCoprime p q) {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (hrel : ∀ z : ℂ, p.eval (h z) =
      (xi z * Complex.exp (-(a : ℂ) * z)) * q.eval (h z)) :
    q.natDegree = 0 ∧ p.natDegree = 1 := by
  have hqne (z : ℂ) : q.eval (h z) ≠ 0 := by
    intro he
    have hpe : p.eval (h z) = 0 := by rw [hrel, he, mul_zero]
    have hn := Polynomial.aeval_ne_zero_of_isCoprime hpq (h z)
    simp [hpe, he] at hn
  have hqdeg : q.natDegree = 0 := by
    by_contra hn
    have hqpos := Nat.pos_of_ne_zero hn
    obtain ⟨t, _, _, hzero, _⟩ := DeletionMixedRefinement.exists_high_simple_critical_xi 0
    let ρ := DeletionMixedRefinement.criticalResponsePoint t
    have hpzero : p.eval (h ρ) = 0 := by rw [hrel, show xi ρ = 0 from hzero, zero_mul, zero_mul]
    have homit : ∀ z : ℂ, 1 < z.re → q.eval (h z) ≠ 0 ∧ h z ≠ h ρ := by
      intro z hz
      refine ⟨hqne z, fun he => ?_⟩
      have hpz : p.eval (h z) = 0 := by rw [he, hpzero]
      have := hrel z
      rw [hpz] at this
      exact (mul_ne_zero (mul_ne_zero (xi_ne_zero_of_one_lt_re hz)
        (Complex.exp_ne_zero _)) (hqne z)) this.symm
    obtain ⟨C, hC, hbound⟩ := exists_exp_ray_bound_rational 1 p q hqpos
      hh.differentiableOn (hqne ρ) homit
    apply xi_tilt_not_exp_ray_bound a 1
    refine ⟨C, hC, fun t ht => ?_⟩
    simpa only [hrel, mul_div_cancel_right₀ _ (hqne _)] using hbound t ht
  refine ⟨hqdeg, ?_⟩
  have hqc := Polynomial.eq_C_of_natDegree_eq_zero hqdeg
  have hq0 : q.coeff 0 ≠ 0 := by
    have he := hqne 0
    rwa [hqc, Polynomial.eval_C] at he
  have hpoly : ∀ z : ℂ, (Polynomial.C (q.coeff 0)⁻¹ * p).eval (h z) =
      xi z * Complex.exp (-(a : ℂ) * z) := by
    intro z
    rw [Polynomial.eval_mul, Polynomial.eval_C, hrel]
    conv_lhs => arg 2; arg 2; rw [hqc, Polynomial.eval_C]
    field_simp
  have hd := xi_polynomial_left_factor_natDegree_eq_one a hh hpoly
  rwa [Polynomial.natDegree_C_mul (inv_ne_zero hq0)] at hd

end RHTower
