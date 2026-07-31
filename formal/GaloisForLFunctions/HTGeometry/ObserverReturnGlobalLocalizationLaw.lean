import GaloisForLFunctions.HTGeometry.ObserverReturnLocalVolumeLaw

/-!
# Global localization of high-fidelity return targets

A continuous nonnegative return defect on a compact orbit carrier is bounded
strictly away from zero outside every open neighborhood of its exact-return
set. Therefore every sufficiently high-fidelity return belongs to the chosen
local charts. This is the compactness step that upgrades local recurrence
geometry to the complete return target.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Compact global return localization.** Let `K` be a compact orbit
carrier and `U` any open set containing every exact return in `K`. Then one
positive defect threshold forces the complete sublevel set in `K` into
`U`. -/
theorem exists_pos_returnThreshold_sublevel_subset
    {X : Type*} [TopologicalSpace X]
    (K U : Set X) (defect : X → ℝ)
    (hK : IsCompact K) (hU : IsOpen U)
    (hdefectContinuous : ContinuousOn defect K)
    (hdefectNonneg : ∀ x ∈ K, 0 ≤ defect x)
    (hzero : ∀ x ∈ K, defect x = 0 → x ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧
      {x | x ∈ K ∧ defect x < δ} ⊆ U := by
  by_cases houtside : (K \ U).Nonempty
  · obtain ⟨x₀, hx₀, hmin⟩ :=
      (hK.diff hU).exists_isMinOn houtside
        (hdefectContinuous.mono Set.sdiff_subset)
    have hδpos : 0 < defect x₀ := by
      have hnonneg := hdefectNonneg x₀ hx₀.1
      have hne : defect x₀ ≠ 0 := by
        intro hzeroValue
        exact hx₀.2 (hzero x₀ hx₀.1 hzeroValue)
      exact lt_of_le_of_ne hnonneg (Ne.symm hne)
    refine ⟨defect x₀, hδpos, ?_⟩
    intro x hx
    by_contra hxU
    have hxoutside : x ∈ K \ U := ⟨hx.1, hxU⟩
    have hminimum := (isMinOn_iff.mp hmin) x hxoutside
    exact (not_lt_of_ge hminimum) hx.2
  · refine ⟨1, one_pos, ?_⟩
    intro x hx
    by_contra hxU
    exact houtside ⟨x, hx.1, hxU⟩

end

end GaloisForLFunctions.HTGeometry
