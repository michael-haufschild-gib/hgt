import GaloisForLFunctions.HTGeometry.OrderedCriticalValueFiniteFibers
import GaloisForLFunctions.HTGeometry.ProperFiniteFiberEndpoint

/-!
# Unique endpoints of actual critical-value continuations

Properness and finite fibers are both discharged for the constructed polynomial family.
Every continuous parameter curve with convergent critical values therefore has a unique
parameter endpoint, including collisions of critical values and critical positions.
-/

open Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
noncomputable section

/-- Every continuous actual parameter curve whose critical values have a finite limit has one
and only one parameter endpoint, even when critical values and positions collide. -/
theorem existsUnique_right_limit_valuesWithConstant {n : ℕ} {v : ℝ → Parameter n}
    {a : ℝ} (ha : 0 < a) (hv : ContinuousOn v (Ioo 0 a)) {b : Fin (n + 1) → ℂ}
    (hb : Tendsto (valuesWithConstant ∘ v) (𝓝[>] 0) (𝓝 b)) :
    ∃! w : Parameter n, valuesWithConstant w = b ∧ Tendsto v (𝓝[>] 0) (𝓝 w) := by
  obtain ⟨w, hw, hlim⟩ := exists_right_limit_of_proper_finite_fiber
    (isProperMap_valuesWithConstant n) ha hv hb (finite_valuesWithConstant_fiber b)
  refine ⟨w, ⟨hw, hlim⟩, ?_⟩
  intro z hz
  exact tendsto_nhds_unique hz.2 hlim

end
end GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
