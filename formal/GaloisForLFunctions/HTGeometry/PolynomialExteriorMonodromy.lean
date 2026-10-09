import GaloisForLFunctions.HTGeometry.PolynomialExteriorCycle
import GaloisForLFunctions.HTGeometry.OrderedPolynomialCoveringMonodromy

open Polynomial Set Topology
open scoped unitInterval
namespace GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
noncomputable section

/-- For every actual polynomial parameter, a positive exterior circle acts as one degree-sized
cycle in native covering monodromy, including parameters with colliding critical values. -/
theorem exists_positiveCircle_monodromyPerm_isCycleOn {n : ℕ} (v : Parameter n) :
    ∃ R : ℝ, 0 < R ∧ ∃ b : PolynomialRegularValue v,
      (b : ℂ) = 0 + (R : ℂ) ∧ ∃ γ : Path b b,
        (∀ t, (γ t : ℂ) = positiveCirclePath 0 R t) ∧
        ((isCoveringMap_polynomialCoverMap v).monodromyPerm b (.mk γ)).IsCycleOn univ ∧
        Nat.card ((polynomialCoverMap v) ⁻¹' {b}) = n + 2 := by
  obtain ⟨D⟩ := exists_polynomialExteriorPowerChart v
  let R := (D.radius ^ (n + 2))⁻¹
  have hR : 0 < R := inv_pos.mpr (pow_pos D.radius_pos _)
  let base : ℂ := 0 + (R : ℂ)
  have hb : ∀ j, base ≠ valuesWithConstant v j := by
    intro j
    have h := D.circle_avoid 0 j
    rw [(positiveCirclePath 0 R).source] at h
    exact h
  let b : PolynomialRegularValue v := ⟨base, hb⟩
  let γ : Path b b :=
    { toFun := fun t => ⟨positiveCirclePath 0 R t, D.circle_avoid t⟩
      continuous_toFun := (positiveCirclePath 0 R).continuous.subtype_mk _
      source' := Subtype.ext (positiveCirclePath 0 R).source
      target' := Subtype.ext (positiveCirclePath 0 R).target }
  let E := rootFiberCoverEquiv v b
  let T := rootLoopTransport v (positiveCirclePath 0 R) D.circle_avoid
  let nativePerm := (isCoveringMap_polynomialCoverMap v).monodromyPerm b (.mk γ)
  have hcompat : ∀ z : RootFiber v base, E (T z) = nativePerm (E z) := by
    intro z
    exact rootLoopTransport_eq_covering_monodromy v γ z
  refine ⟨R, hR, b, rfl, γ, fun _ => rfl, ?_, ?_⟩
  · obtain ⟨u, hu, hzero, hpow, hstep⟩ := D.primitive_coordinate
    apply isCycleOn_of_primitive_coordinate nativePerm (u ∘ E.symm)
      (hu.comp E.symm.injective) (fun w => hzero (E.symm w))
      (by omega : 0 < n + 2)
      (Complex.isPrimitiveRoot_exp (n + 2) (by omega)).inv
      (fun a b => hpow (E.symm a) (E.symm b))
    intro w
    obtain ⟨z, rfl⟩ := E.surjective w
    change u (E.symm (nativePerm (E z))) = _
    rw [← hcompat z, E.symm_apply_apply]
    exact hstep z
  · exact (Nat.card_congr E.symm).trans D.natCard_rootFiber

end
end GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
