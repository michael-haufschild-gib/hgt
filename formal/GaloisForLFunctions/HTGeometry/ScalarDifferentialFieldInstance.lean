import GaloisForLFunctions.HTGeometry.JetScalingClockField

/-!
# The differential structure on `C⟨y⟩` and the clock as an abstract semilinear automorphism

Equipping the scalar free differential field `C⟨y⟩` with its jet-shift derivation as a `Differential`
instance turns the concrete clock `clockDilationFieldEquiv` into an instance of the abstract clock of
the clock-character law: its field-level semilinearity becomes the `hsemi` hypothesis of
`clock_family_scaling_character_from_semilinear`, written with the `′` notation.

The base field `C` carries the zero derivation, so the field derivation kills base constants — this is
the `DifferentialAlgebra C (C⟨y⟩)` compatibility.
-/

namespace GaloisForLFunctions

noncomputable section

open scoped Differential

variable {C : Type*} [Field C]

/-- The jet-shift differential structure on `C⟨y⟩`.  The integer scalars are forced to the canonical
`Ring.toIntAlgebra` to avoid the localization `Algebra ℤ` diamond. -/
noncomputable instance scalarDifferentialFieldDifferential :
    Differential (ScalarDifferentialField C) := by
  letI : Algebra ℤ (ScalarDifferentialField C) := Ring.toIntAlgebra _
  exact ⟨(scalarDifferentialFieldDerivation (C := C)).restrictScalars ℤ⟩

@[simp] theorem scalarDifferentialField_deriv (z : ScalarDifferentialField C) :
    z′ = scalarDifferentialFieldDerivation z := rfl

/-- The field derivation kills the base-field constants (`C` has the zero derivation). -/
theorem scalarDifferentialFieldDerivation_algebraMap (c : C) :
    scalarDifferentialFieldDerivation (algebraMap C (ScalarDifferentialField C) c) = 0 :=
  Derivation.map_algebraMap _ c

/-- **Semilinearity in `hsemi` shape.**  The clock on `C⟨y⟩` satisfies the abstract clock hypothesis
`ρ_λ(w′) = λ · (ρ_λ w)′`. -/
theorem clockDilationFieldEquiv_semilinear (lam : C) (hlam : lam ≠ 0)
    (w : ScalarDifferentialField C) :
    clockDilationFieldEquiv lam hlam w′
      = algebraMap C (ScalarDifferentialField C) lam * (clockDilationFieldEquiv lam hlam w)′ := by
  simp only [scalarDifferentialField_deriv]
  exact clockDilationField_semilinear lam hlam w

/-- **`DifferentialAlgebra` compatibility.**  When `C` carries the zero derivation, the field
derivation restricts to `0` on the base, so `C⟨y⟩` is a differential `C`-algebra. -/
theorem scalarDifferentialFieldDifferentialAlgebra [Differential C] (hCzero : ∀ c : C, (c′ : C) = 0) :
    DifferentialAlgebra C (ScalarDifferentialField C) := by
  refine ⟨fun c => ?_⟩
  simp only [scalarDifferentialField_deriv, scalarDifferentialFieldDerivation_algebraMap]
  rw [hCzero c, map_zero]

end

end GaloisForLFunctions
