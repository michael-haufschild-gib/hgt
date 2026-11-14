import GaloisForLFunctions.HTGeometry.BorelResurgence.ContinuationRigidity
import GaloisForLFunctions.HTGeometry.FiniteHardyJetNaturalBoundary

/-!
# Affine cancellation of modular natural boundaries

The disk Eisenstein series and every finite Hardy primitive have genuine unit-circle natural
boundaries. An arbitrary offset can cancel each boundary point for at most one coefficient;
only countably many coefficients cancel any boundary point at all.
-/

open Complex Set

namespace GaloisForLFunctions.HTGeometry

/-- The Eisenstein boundary permits at most one local affine cancellation. -/
theorem e2_affine_continuation_coefficients_subsingleton (f : ℂ → ℂ) (θ : ℝ) :
    {c : ℂ | Bottcher.ContinuesAcross (fun z => f z + c * e2Disk z)
      (Complex.exp ((θ : ℂ) * I))}.Subsingleton := by
  simp_rw [← continuesAcross_disk_iff]
  apply (not_continuesAcross_iff_affine_coefficients_subsingleton e2Disk
    (Metric.ball 0 1) _).mp
  rw [continuesAcross_disk_iff]
  exact e2Disk_naturalBoundary (by simp [Complex.norm_exp])

/-- Every Hardy primitive has the same local rigidity, independently of primitive order. -/
theorem hardyPrimitive_affine_continuation_coefficients_subsingleton
    (m : ℕ) (f : ℂ → ℂ) (θ : ℝ) :
    {c : ℂ | Bottcher.ContinuesAcross (fun z => f z + c * hardyPrimitiveJet m z)
      (Complex.exp ((θ : ℂ) * I))}.Subsingleton := by
  simp_rw [← continuesAcross_disk_iff]
  apply (not_continuesAcross_iff_affine_coefficients_subsingleton (hardyPrimitiveJet m)
    (Metric.ball 0 1) _).mp
  rw [continuesAcross_disk_iff]
  exact hardyPrimitiveJet_naturalBoundary m (by simp [Complex.norm_exp])

/-- Across the whole Eisenstein boundary the exceptional coefficients form a countable set. -/
theorem countable_e2_affine_boundary_exceptions (f : ℂ → ℂ) :
    {c : ℂ | ∃ z : ℂ, ‖z‖ = 1 ∧
      Bottcher.ContinuesAcross (fun w => f w + c * e2Disk w) z}.Countable := by
  apply (countable_coefficients_continuing_at_singular_points f e2Disk
    (Metric.ball 0 1)).mono
  rintro c ⟨z, hz, hcont⟩
  refine ⟨z, ?_, (continuesAcross_disk_iff _ _).mpr hcont⟩
  rw [continuesAcross_disk_iff]
  exact e2Disk_naturalBoundary hz

/-- Countability persists through every finite primitive of the modular source. -/
theorem countable_hardyPrimitive_affine_boundary_exceptions (m : ℕ) (f : ℂ → ℂ) :
    {c : ℂ | ∃ z : ℂ, ‖z‖ = 1 ∧
      Bottcher.ContinuesAcross (fun w => f w + c * hardyPrimitiveJet m w) z}.Countable := by
  apply (countable_coefficients_continuing_at_singular_points f (hardyPrimitiveJet m)
    (Metric.ball 0 1)).mono
  rintro c ⟨z, hz, hcont⟩
  refine ⟨z, ?_, (continuesAcross_disk_iff _ _).mpr hcont⟩
  rw [continuesAcross_disk_iff]
  exact hardyPrimitiveJet_naturalBoundary m hz

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.e2_affine_continuation_coefficients_subsingleton
#print axioms GaloisForLFunctions.HTGeometry.hardyPrimitive_affine_continuation_coefficients_subsingleton
#print axioms GaloisForLFunctions.HTGeometry.countable_e2_affine_boundary_exceptions
#print axioms GaloisForLFunctions.HTGeometry.countable_hardyPrimitive_affine_boundary_exceptions
