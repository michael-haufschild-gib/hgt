import GaloisForLFunctions.HTGeometry.ProperFiniteFiberEndpoint
import Mathlib.Topology.Order.ExtendFrom
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.UnitInterval

open Set Filter Topology
open scoped unitInterval
namespace GaloisForLFunctions.HTGeometry
noncomputable section

theorem exists_left_limit_of_proper_finite_fiber
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    {f : X → Y} (hf : IsProperMap f) {v : ℝ → X} {a b : ℝ} (hab : a < b)
    (hv : ContinuousOn v (Ioo a b)) {y : Y}
    (hlim : Tendsto (f ∘ v) (𝓝[<] b) (𝓝 y)) (hfin : (f ⁻¹' {y}).Finite) :
    ∃ x, f x = y ∧ Tendsto v (𝓝[<] b) (𝓝 x) := by
  have hb := ((nhdsLT_basis b).restrict_subset
    ((nhdsLT_basis b).mem_of_mem hab)).map v
  apply exists_limit_of_proper_finite_fiber_connected_basis hf hb ?_ ?_ hfin
  · intro c hc
    exact isPreconnected_Ioo.image v (hv.mono hc.2)
  · change Filter.map f (Filter.map v (𝓝[<] b)) ≤ 𝓝 y
    rw [Filter.map_map]
    exact hlim

/-- A lift on a half-open interval extends through its finite terminal fiber. -/
theorem exists_closed_interval_extension_of_proper_finite_fiber
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T3Space X]
    {f : X → Y} (hf : IsProperMap f) {v : ℝ → X}
    (hv : ContinuousOn v (Ico 0 1)) (b : C(ℝ, Y))
    (hvb : ∀ t ∈ Ico (0 : ℝ) 1, f (v t) = b t)
    (hfin : (f ⁻¹' {b 1}).Finite) :
    ∃ V : C(I, X), V 0 = v 0 ∧ (∀ t, f (V t) = b t) ∧
      ∀ t : I, (t : ℝ) < 1 → V t = v t := by
  have hvopen : ContinuousOn v (Ioo 0 1) := hv.mono Ioo_subset_Ico_self
  have hv0 : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 (v 0)) := by
    have h := (hv 0 ⟨le_rfl, zero_lt_one⟩).mono Ioo_subset_Ico_self
    simpa only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsGT zero_lt_one] using h
  have hvb1 : Tendsto (f ∘ v) (𝓝[<] (1 : ℝ)) (𝓝 (b 1)) := by
    apply b.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr'
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    exact (hvb t ⟨ht.1.le, ht.2⟩).symm
  obtain ⟨x₁, hx₁, hv1⟩ := exists_left_limit_of_proper_finite_fiber hf zero_lt_one
    hvopen hvb1 hfin
  let V : C(I, X) := ⟨fun t => extendFrom (Ioo 0 1) v t,
    (continuousOn_Icc_extendFrom_Ioo hvopen hv0 hv1).restrict⟩
  have hV0 : V 0 = v 0 := eq_lim_at_left_extendFrom_Ioo zero_lt_one hv0
  have hV1 : V 1 = x₁ := eq_lim_at_right_extendFrom_Ioo zero_lt_one hv1
  have hVinterior (t : I) (ht : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) : V t = v t :=
    extendFrom_extends hvopen t ⟨ht, ht1⟩
  have hVhalf (t : I) (ht : (t : ℝ) < 1) : V t = v t := by
    by_cases ht0 : (t : ℝ) = 0
    · have heq : t = 0 := Subtype.ext ht0
      subst t
      exact hV0
    · exact hVinterior t (lt_of_le_of_ne t.property.1 (Ne.symm ht0)) ht
  refine ⟨V, hV0, ?_, hVhalf⟩
  intro t
  by_cases ht : (t : ℝ) < 1
  · rw [hVhalf t ht]
    exact hvb t ⟨t.property.1, ht⟩
  · have heq : t = 1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt ht))
    subst t
    rw [hV1]
    exact hx₁

end
end GaloisForLFunctions.HTGeometry
