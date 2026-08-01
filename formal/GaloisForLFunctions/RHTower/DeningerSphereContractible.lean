import GaloisForLFunctions.RHTower.DeningerSphereLineHomotopy
import Mathlib.Topology.Homotopy.Contractible

/-!
# Contractibility of the unit sphere

Concatenating the normalized straight-line deformation with the quarter-circle deformation
contracts the unit sphere of a real inner product space carrying an eigenvector-free isometry whose
range misses a unit vector.  Such an isometry exists exactly in infinite dimensions, and this is
the angular contraction the Kummer polar splitting needs.

* `deningerSphere_nullhomotopic` : the identity of the sphere is nullhomotopic.
* `deningerSphere_contractible` : the sphere is contractible.
-/

namespace RHTower

open scoped InnerProductSpace unitInterval

section Contractible

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **The identity of the unit sphere is nullhomotopic.** -/
theorem deningerSphere_nullhomotopic (S : H →ₗᵢ[ℝ] H)
    (hS : ∀ (y : H) (c : ℝ), y ≠ 0 → S y ≠ c • y) {e : H} (he : ‖e‖ = 1)
    (hperp : ∀ y : H, ⟪S y, e⟫_ℝ = 0) :
    (ContinuousMap.id (Metric.sphere (0 : H) 1)).Nullhomotopic :=
  ⟨⟨e, mem_sphere_zero_iff_norm.mpr he⟩,
    ⟨(deningerSphereLineHomotopy S hS).trans (deningerSlideHomotopy S he hperp)⟩⟩

/-- **The unit sphere is contractible.**  This is the angular factor of the Kummer polar
splitting: it carries no ordinary cohomology in positive degree. -/
theorem deningerSphere_contractible (S : H →ₗᵢ[ℝ] H)
    (hS : ∀ (y : H) (c : ℝ), y ≠ 0 → S y ≠ c • y) {e : H} (he : ‖e‖ = 1)
    (hperp : ∀ y : H, ⟪S y, e⟫_ℝ = 0) :
    ContractibleSpace (Metric.sphere (0 : H) 1) :=
  (contractible_iff_id_nullhomotopic _).mpr (deningerSphere_nullhomotopic S hS he hperp)

end Contractible

end RHTower
