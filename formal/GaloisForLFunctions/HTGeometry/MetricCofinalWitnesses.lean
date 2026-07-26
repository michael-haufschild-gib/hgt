import GaloisForLFunctions.HTGeometry.HypertranscendentalClockBoundary

/-!
# Realizations of the metric-cofinality interface

A sampling is metric-bornologically cofinal whenever it is surjective — in particular for the
identity sampling — and, at the opposite extreme, whenever the transport itself is uniformly bounded,
in which case any nonempty sampling is cofinal with constant twice the bounding radius.
-/

namespace GaloisForLFunctions.HTGeometry

variable {ι κ X : Type*} [PseudoMetricSpace X]

theorem isMetricBornologicallyCofinal_id (p : ι → X) :
    IsMetricBornologicallyCofinal p id :=
  ⟨0, fun i => ⟨i, by simp⟩⟩

theorem isMetricBornologicallyCofinal_of_surjective (p : ι → X) {φ : κ → ι}
    (hφ : Function.Surjective φ) : IsMetricBornologicallyCofinal p φ := by
  refine ⟨0, fun i => ?_⟩
  obtain ⟨j, hj⟩ := hφ i
  exact ⟨j, by simp [hj]⟩

/-- A uniformly bounded transport is cofinal along every nonempty sampling, with constant twice the
bounding radius. -/
theorem isMetricBornologicallyCofinal_of_uniformlyBoundedAround [Nonempty κ]
    {p : ι → X} (hp : IsUniformlyBoundedAround p) (φ : κ → ι) :
    IsMetricBornologicallyCofinal p φ := by
  obtain ⟨x₀, R, hR⟩ := hp
  refine ⟨2 * R, fun i => ⟨Classical.arbitrary κ, ?_⟩⟩
  calc dist (p i) (p (φ (Classical.arbitrary κ)))
      ≤ dist (p i) x₀ + dist x₀ (p (φ (Classical.arbitrary κ))) := dist_triangle _ _ _
    _ ≤ R + R := by
        refine add_le_add (hR i) ?_
        rw [dist_comm]
        exact hR _
    _ = 2 * R := by ring

end GaloisForLFunctions.HTGeometry
