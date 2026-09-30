import GaloisForLFunctions.HTGeometry.WeightedDensityL2

/-!
# Canonical complex L² congruence under equality of measures

The isometry changes only the measure's presentation. Its literal
function representative and every admitted `toLp` class are preserved.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- The canonical identity isometry when the two measures are proved equal. -/
def l2MeasureCongruence (h : μ = ν) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν :=
  { toLinearEquiv :=
      { toEquiv := Equiv.cast (congrArg (fun m => (Lp ℂ 2 m : Type _)) h)
        map_add' := by subst ν; intro x y; rfl
        map_smul' := by subst ν; intro c f; rfl }
    norm_map' := by subst ν; intro f; rfl }

theorem l2MeasureCongruence_coe (h : μ = ν) (f : Lp ℂ 2 μ) :
    (l2MeasureCongruence h f : α → ℂ) = (f : α → ℂ) := by
  subst ν
  rfl

/-- A literal representative remains the same almost everywhere for the target measure. -/
theorem l2MeasureCongruence_coe_ae (h : μ = ν) (f : Lp ℂ 2 μ) (g : α → ℂ)
    (hf : (f : α → ℂ) =ᵐ[μ] g) :
    (l2MeasureCongruence h f : α → ℂ) =ᵐ[ν] g := by
  subst ν
  exact hf

theorem l2MeasureCongruence_toLp (h : μ = ν) (f : α → ℂ)
    (hf : MemLp f 2 μ) (hg : MemLp f 2 ν) :
    l2MeasureCongruence h (hf.toLp f) = hg.toLp f := by
  subst ν
  rfl

/-- Canonical measure congruence transports a literal closed span of `L²` vectors. -/
theorem l2MeasureCongruence_mem_closedSpan_image {I : Type*} (h : μ = ν)
    (v : I → Lp ℂ 2 μ) (f : Lp ℂ 2 μ)
    (hf : f ∈ (Submodule.span ℂ (Set.range v)).topologicalClosure) :
    l2MeasureCongruence h f ∈
      (Submodule.span ℂ (Set.range fun i => l2MeasureCongruence h (v i))).topologicalClosure := by
  subst ν
  exact hf

/-- The same closed-span transport with its target family already identified. -/
theorem l2MeasureCongruence_mem_closedSpan_of_familyEq {I : Type*} (h : μ = ν)
    (v : I → Lp ℂ 2 μ) (w : I → Lp ℂ 2 ν)
    (hw : (fun i => l2MeasureCongruence h (v i)) = w) (f : Lp ℂ 2 μ)
    (hf : f ∈ (Submodule.span ℂ (Set.range v)).topologicalClosure) :
    l2MeasureCongruence h f ∈ (Submodule.span ℂ (Set.range w)).topologicalClosure := by
  rw [← hw]
  exact l2MeasureCongruence_mem_closedSpan_image h v f hf

end

end GaloisForLFunctions.HTGeometry
