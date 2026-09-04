import GaloisForLFunctions.RHTower.RestrictedProjectionCubicRelativeIndex
import GaloisForLFunctions.RHTower.RestrictedUnitaryCubicOperator

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem RestrictedUnitaryDatum.opTrace_cubicDefect_eq_relativeIndex
    (D : RestrictedUnitaryDatum H) :
    opTrace (restrictedProjectionCubicDefect
        D.conjugateProjection D.projection) =
      (restrictedProjectionRelativeIndex
        D.conjugateProjection D.projection : ℂ) :=
  opTrace_restrictedProjectionCubicDefect_eq_relativeIndex
    D.conjugateProjection D.projection
    D.conjugateProjection_idempotent D.projection_idempotent
    D.conjugateProjection_adjoint D.projection_adjoint
    D.displacement_isHilbertSchmidt

theorem RestrictedUnitaryDatum.relativeIndex_eq_intersection_finrank_sub
    (D : RestrictedUnitaryDatum H) :
    restrictedProjectionRelativeIndex D.conjugateProjection D.projection =
      (Module.finrank ℂ
          ↥(LinearMap.range (D.conjugateProjection : H →ₗ[ℂ] H) ⊓
            LinearMap.ker (D.projection : H →ₗ[ℂ] H)) : ℤ) -
      (Module.finrank ℂ
          ↥(LinearMap.range (D.projection : H →ₗ[ℂ] H) ⊓
            LinearMap.ker (D.conjugateProjection : H →ₗ[ℂ] H)) : ℤ) :=
  restrictedProjectionRelativeIndex_eq_intersection_finrank_sub
    D.conjugateProjection D.projection
    D.conjugateProjection_idempotent D.projection_idempotent
    D.conjugateProjection_adjoint D.projection_adjoint

theorem restrictedUnitaryCubicRelativeIndex_operator_closed :
    ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (D : RestrictedUnitaryDatum H),
      opTrace (restrictedProjectionCubicDefect
          D.conjugateProjection D.projection) =
        (restrictedProjectionRelativeIndex
          D.conjugateProjection D.projection : ℂ) ∧
      restrictedProjectionRelativeIndex D.conjugateProjection D.projection =
        (Module.finrank ℂ
            ↥(LinearMap.range (D.conjugateProjection : H →ₗ[ℂ] H) ⊓
              LinearMap.ker (D.projection : H →ₗ[ℂ] H)) : ℤ) -
        (Module.finrank ℂ
            ↥(LinearMap.range (D.projection : H →ₗ[ℂ] H) ⊓
              LinearMap.ker (D.conjugateProjection : H →ₗ[ℂ] H)) : ℤ) := by
  intro H _ _ _ D
  exact ⟨D.opTrace_cubicDefect_eq_relativeIndex,
    D.relativeIndex_eq_intersection_finrank_sub⟩

end RHTower
