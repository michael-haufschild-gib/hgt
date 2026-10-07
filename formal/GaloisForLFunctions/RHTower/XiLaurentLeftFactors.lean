import GaloisForLFunctions.HTGeometry.SchottkyLaurentGrowth
import GaloisForLFunctions.RHTower.XiPolynomialLeftFactors

/-!
# Exclusion of Laurent outer factors on entire units

Every Laurent polynomial is a sum of a polynomial in a coordinate and one in
its reciprocal. No such expression in an entire nowhere-zero function can
equal an exponentially tilted Xi function.
-/

open Complex Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Tilted Xi is never a Laurent expression in an entire nowhere-zero function. -/
theorem xi_not_laurent_of_entire_unit (a : ℝ) (p q : Polynomial ℂ) {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) (hunit : ∀ z : ℂ, h z ≠ 0) :
    ¬ ∀ z : ℂ, p.eval (h z) + q.eval ((h z)⁻¹) =
      xi z * Complex.exp (-(a : ℂ) * z) := by
  intro hrel
  obtain ⟨t, _, _, hzero, _⟩ := DeletionMixedRefinement.exists_high_simple_critical_xi 0
  let ρ := DeletionMixedRefinement.criticalResponsePoint t
  have hb : p.eval (h ρ) + q.eval ((h ρ)⁻¹) = 0 := by
    rw [hrel, show xi ρ = 0 from hzero, zero_mul]
  have homit : ∀ z : ℂ, 1 < z.re → h z ≠ 0 ∧ h z ≠ h ρ := by
    intro z hz
    refine ⟨hunit z, fun he => ?_⟩
    apply mul_ne_zero (xi_ne_zero_of_one_lt_re hz) (Complex.exp_ne_zero (-(a : ℂ) * z))
    rw [← hrel z, he, hb]
  obtain ⟨C, hC, hbound⟩ := exists_exp_ray_bound_laurent 1 p q hh.differentiableOn
    (hunit ρ) homit
  apply xi_tilt_not_exp_ray_bound a 1
  exact ⟨C, hC, fun t ht => by simpa only [hrel] using hbound t ht⟩

end RHTower
