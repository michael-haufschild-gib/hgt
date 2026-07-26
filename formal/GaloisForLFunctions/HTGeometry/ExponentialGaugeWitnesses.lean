import GaloisForLFunctions.HTGeometry.ExponentialGaugeSelection

/-!
# Realizations and normalizations of the exponential-gauge interfaces

The unit gauge with vanishing direction realizes the static gauge interface in one and in several
parameters, and the full field realizes relative closure under logarithmic primitives.  The gauge
axioms also force the normalization `u 0 = 1` in both forms, which is the exact statement that the
parameter acts through a group homomorphism into the multiplicative group.
-/

namespace GaloisForLFunctions

variable {C F : Type*} [Field C] [Field F] [Algebra C F]

/-! ## Realizations -/

/-- The unit gauge with vanishing direction. -/
theorem isDifferentialExponentialGauge_one (D : Derivation C F F) :
    IsDifferentialExponentialGauge D 0 (fun _ : C => (1 : F)) := by
  refine ⟨fun _ => one_ne_zero, fun c d => by simp, fun c => ?_⟩
  rw [Derivation.map_one_eq_zero, zero_div, mul_zero]

/-- The full field is closed under logarithmic primitives. -/
theorem closedUnderLogarithmicPrimitives_top (D : Derivation C F F) :
    ClosedUnderLogarithmicPrimitives (⊤ : IntermediateField C F) D :=
  fun _ _ _ => trivial

/-! ## Normalization forced by the gauge axioms -/

/-- A static exponential gauge is normalized at the zero parameter. -/
theorem IsDifferentialExponentialGauge.apply_zero {D : Derivation C F F} {dh : F} {u : C → F}
    (hu : IsDifferentialExponentialGauge D dh u) : u 0 = 1 := by
  have h := hu.2.1 0 0
  rw [sub_zero, div_self (hu.1 0)] at h
  exact h.symm

section Multidimensional

variable {V : Type*} [AddCommGroup V] [Module C V]

/-- The unit family with vanishing direction. -/
theorem isDifferentialExponentialFamily_one (D : Derivation C F F) :
    IsDifferentialExponentialFamily D (0 : V →ₗ[C] F) (fun _ : V => (1 : F)) := by
  refine ⟨fun _ => one_ne_zero, fun v w => by simp, fun v => ?_⟩
  rw [Derivation.map_one_eq_zero, zero_div]
  simp

/-- A multi-parameter exponential family is normalized at the zero parameter. -/
theorem IsDifferentialExponentialFamily.apply_zero {D : Derivation C F F}
    {direction : V →ₗ[C] F} {u : V → F}
    (hu : IsDifferentialExponentialFamily D direction u) : u 0 = 1 := by
  have h := hu.2.1 0 0
  rw [add_zero] at h
  have hne : u 0 ≠ 0 := hu.1 0
  field_simp at h
  exact h.symm

end Multidimensional

end GaloisForLFunctions
