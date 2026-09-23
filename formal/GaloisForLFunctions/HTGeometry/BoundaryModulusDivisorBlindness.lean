import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Boundary modulus does not determine a holomorphic divisor

The monomials `z ↦ z^m` all have boundary modulus one on the unit circle, while their orders at
the origin are the arbitrary natural numbers `m`.  Thus any outer-factor or boundary-modulus
argument is blind to the inner zero divisor unless it supplies an additional phase, winding, or
inner-factor constraint.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- All monomials have the same norm on the unit circle. -/
theorem circleBoundaryNorm_monomials_eq (m n : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖z ^ m‖ = ‖z ^ n‖ := by
  simp [norm_pow, hz]

/-- The order at the origin of the `m`th monomial is exactly `m`. -/
theorem analyticOrderAt_monomial_zero (m : ℕ) :
    analyticOrderAt (fun z : ℂ => z ^ m) 0 = m := by
  have hfun : ((fun z : ℂ => z - 0) ^ m) = (fun z : ℂ => z ^ m) := by
    funext z
    simp
  rw [← hfun]
  exact analyticOrderAt_centeredMonomial

/-- Exact family witnessing that unit-circle modulus leaves zero order arbitrary. -/
theorem circleBoundaryModulus_blind_to_monomial_zero_order (m n : ℕ) :
    (∀ z : ℂ, ‖z‖ = 1 → ‖z ^ m‖ = ‖z ^ n‖) ∧
      analyticOrderAt (fun z : ℂ => z ^ m) 0 = m ∧
      analyticOrderAt (fun z : ℂ => z ^ n) 0 = n := by
  exact ⟨fun _ hz => circleBoundaryNorm_monomials_eq m n hz,
    analyticOrderAt_monomial_zero m, analyticOrderAt_monomial_zero n⟩

/-- Two entire functions can have identical boundary modulus and different zero orders. -/
theorem exists_entire_same_circleBoundaryNorm_distinct_zeroOrder :
    ∃ f g : ℂ → ℂ,
      AnalyticOnNhd ℂ f Set.univ ∧
      AnalyticOnNhd ℂ g Set.univ ∧
      (∀ z : ℂ, ‖z‖ = 1 → ‖f z‖ = ‖g z‖) ∧
      analyticOrderAt f 0 ≠ analyticOrderAt g 0 := by
  refine ⟨fun z : ℂ => z ^ (1 : ℕ), fun z : ℂ => z ^ (2 : ℕ), ?_, ?_, ?_, ?_⟩
  · rw [Complex.analyticOnNhd_univ_iff_differentiable]
    fun_prop
  · rw [Complex.analyticOnNhd_univ_iff_differentiable]
    fun_prop
  · intro z hz
    exact circleBoundaryNorm_monomials_eq 1 2 hz
  · rw [analyticOrderAt_monomial_zero, analyticOrderAt_monomial_zero]
    norm_num

end GaloisForLFunctions.HTGeometry
