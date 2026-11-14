import GaloisForLFunctions.HTGeometry.BorelResurgence.ContinuationRigidity
import GaloisForLFunctions.U0.U0NaturalBoundary

/-!
# Exceptional affine cancellations of the dyadic Mahler boundary

At any chosen unit-circle point, an arbitrary offset admits at most one coefficient of `u₀`
that allows analytic continuation. Across the whole circle the set of such coefficients is
countable. Neither statement assumes that the offset itself continues.
-/

open Complex Set
open GaloisForLFunctions.HTGeometry U0NaturalBoundary

namespace U0

/-- Local cancellation of the Mahler natural boundary has at most one scalar coefficient. -/
theorem affine_continuation_coefficients_subsingleton (f : ℂ → ℂ) (θ : ℝ) :
    {c : ℂ | U0NaturalBoundary.ContinuesAcross (fun z => f z + c * u0 z)
      Ext (Complex.exp ((θ : ℂ) * I))}.Subsingleton := by
  apply (not_continuesAcross_iff_affine_coefficients_subsingleton u0 Ext
    (Complex.exp ((θ : ℂ) * I))).mp
  exact u0_natural_boundary _ (by simp [Complex.norm_exp])

/-- Only countably many coefficients can remove even one point of the Mahler natural boundary. -/
theorem countable_affine_boundary_exceptions (f : ℂ → ℂ) :
    {c : ℂ | ∃ z : ℂ, ‖z‖ = 1 ∧
      U0NaturalBoundary.ContinuesAcross (fun w => f w + c * u0 w) Ext z}.Countable := by
  apply (countable_coefficients_continuing_at_singular_points f u0 Ext).mono
  rintro c ⟨z, hz, hcont⟩
  exact ⟨z, u0_natural_boundary z hz, hcont⟩

/-- Every prescribed exceptional coefficient is attained by its exact opposite offset. -/
theorem affine_exact_cancellation (c : ℂ) (θ : ℝ) :
    {d : ℂ | U0NaturalBoundary.ContinuesAcross (fun z => -c * u0 z + d * u0 z)
      Ext (Complex.exp ((θ : ℂ) * I))} = {c} := by
  apply (affine_continuation_coefficients_subsingleton (fun z => -c * u0 z) θ)
    .eq_singleton_of_mem
  refine ⟨fun _ => 0, analyticAt_const, Filter.Eventually.of_forall fun z => ?_⟩
  ring

end U0
