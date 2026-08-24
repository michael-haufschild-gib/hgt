import GaloisForLFunctions.HTGeometry.FreeCoordinateField

/-!
# Hasse classification by free-coordinate derivations

The complete family of coordinate derivations on a free rational function field has the scalar
coefficient field as its exact common kernel. Hence rational functions modulo scalars are exactly
the derivative profiles that occur globally. Equality is placewise derivative equality, and every
nonzero quotient class has a coordinate witness.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Simultaneous observation by every free-coordinate derivation. -/
noncomputable def freeCoordinateDerivativeHasseProfile
    (C σ : Type*) [Field C] [CharZero C] :
    FreeCoordinateRationalField C σ →ₗ[C]
      (σ → FreeCoordinateRationalField C σ) :=
  LinearMap.pi fun i => (freeCoordinateDerivation C σ i).toLinearMap

@[simp] theorem freeCoordinateDerivativeHasseProfile_apply
    (C σ : Type*) [Field C] [CharZero C]
    (f : FreeCoordinateRationalField C σ) (i : σ) :
    freeCoordinateDerivativeHasseProfile C σ f i =
      freeCoordinateDerivation C σ i f := by
  rfl

/-- Scalar rational functions are exactly the common invisible sector. -/
theorem freeCoordinateDerivativeHasseProfile_ker
    (C σ : Type*) [Field C] [CharZero C] :
    LinearMap.ker (freeCoordinateDerivativeHasseProfile C σ) =
      (⊥ : IntermediateField C
        (FreeCoordinateRationalField C σ)).toSubmodule := by
  ext f
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    change f ∈ (⊥ : IntermediateField C
      (FreeCoordinateRationalField C σ))
    rw [IntermediateField.mem_bot]
    obtain ⟨c, hc⟩ := (all_freeCoordinateDerivations_eq_zero_iff f).mp
      (fun i => congrFun h i)
    exact ⟨c, hc.symm⟩
  · intro h
    have h' : f ∈ (⊥ : IntermediateField C
        (FreeCoordinateRationalField C σ)) := h
    rw [IntermediateField.mem_bot] at h'
    obtain ⟨c, hc⟩ := h'
    have hd := (all_freeCoordinateDerivations_eq_zero_iff f).mpr ⟨c, hc.symm⟩
    funext i
    exact hd i

/-- Rational functions modulo scalars. -/
abbrev FreeCoordinateDerivativeHasseClass
    (C σ : Type*) [Field C] [CharZero C] :=
  FreeCoordinateRationalField C σ ⧸
    (⊥ : IntermediateField C
      (FreeCoordinateRationalField C σ)).toSubmodule

/-- Rational functions modulo scalars are exactly realized derivative profiles. -/
noncomputable def freeCoordinateDerivativeHasseEquivRealizedProfiles
    (C σ : Type*) [Field C] [CharZero C] :
    FreeCoordinateDerivativeHasseClass C σ ≃ₗ[C]
      LinearMap.range (freeCoordinateDerivativeHasseProfile C σ) :=
  (Submodule.quotEquivOfEq _ _
    (freeCoordinateDerivativeHasseProfile_ker C σ).symm).trans
      (LinearMap.quotKerEquivRange _)

@[simp] theorem freeCoordinateDerivativeHasseEquivRealizedProfiles_mk
    (C σ : Type*) [Field C] [CharZero C]
    (f : FreeCoordinateRationalField C σ) :
    freeCoordinateDerivativeHasseEquivRealizedProfiles C σ
        (Submodule.Quotient.mk f) =
      ⟨freeCoordinateDerivativeHasseProfile C σ f, ⟨f, rfl⟩⟩ := by
  rfl

/-- Two rational functions agree modulo scalars iff every coordinate derivative agrees. -/
theorem freeCoordinateDerivative_congr_hasse_iff
    (C σ : Type*) [Field C] [CharZero C]
    (f g : FreeCoordinateRationalField C σ) :
    Submodule.Quotient.mk f =
        (Submodule.Quotient.mk g : FreeCoordinateDerivativeHasseClass C σ) ↔
      ∀ i, freeCoordinateDerivation C σ i f =
        freeCoordinateDerivation C σ i g := by
  constructor
  · intro h i
    have he := congrArg
      (freeCoordinateDerivativeHasseEquivRealizedProfiles C σ) h
    exact congrFun (congrArg Subtype.val he) i
  · intro h
    apply (freeCoordinateDerivativeHasseEquivRealizedProfiles C σ).injective
    apply Subtype.ext
    funext i
    exact h i

/-- A nonzero scalar-quotient class is detected by one coordinate derivation. -/
theorem freeCoordinateDerivativeClass_ne_zero_iff_exists_coordinateWitness
    (C σ : Type*) [Field C] [CharZero C]
    (x : FreeCoordinateDerivativeHasseClass C σ) :
    x ≠ 0 ↔
      ∃ i, (freeCoordinateDerivativeHasseEquivRealizedProfiles C σ x).1 i ≠ 0 := by
  constructor
  · intro hx
    have hp :
        (freeCoordinateDerivativeHasseEquivRealizedProfiles C σ x).1 ≠ 0 := by
      intro hp
      apply hx
      apply (freeCoordinateDerivativeHasseEquivRealizedProfiles C σ).injective
      apply Subtype.ext
      simpa using hp
    simpa only [Pi.zero_apply] using Function.ne_iff.mp hp
  · rintro ⟨i, hi⟩ rfl
    exact hi (by simp)

/-- Every realized derivative profile has one unique global class modulo scalars. -/
theorem freeCoordinateDerivativeRealizedProfile_existsUnique_global
    (C σ : Type*) [Field C] [CharZero C]
    (p : LinearMap.range (freeCoordinateDerivativeHasseProfile C σ)) :
    ∃! x : FreeCoordinateDerivativeHasseClass C σ,
      freeCoordinateDerivativeHasseEquivRealizedProfiles C σ x = p := by
  refine ⟨(freeCoordinateDerivativeHasseEquivRealizedProfiles C σ).symm p,
    (freeCoordinateDerivativeHasseEquivRealizedProfiles C σ).apply_symm_apply p, ?_⟩
  intro y hy
  apply (freeCoordinateDerivativeHasseEquivRealizedProfiles C σ).injective
  rw [hy, (freeCoordinateDerivativeHasseEquivRealizedProfiles C σ).apply_symm_apply]

end

end GaloisForLFunctions.HTGeometry
