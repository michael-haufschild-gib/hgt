import GaloisForLFunctions.RHTower.RestrictedProjectionCubicRelativeIndex
import GaloisForLFunctions.RHTower.RestrictedUnitaryCubicOperator

/-!
# Cubic trace formula for the relative index of a restricted unitary

A restricted unitary datum is an orthogonal projection `P` on a complex Hilbert space together with
a unitary `U` whose commutator `PU - UP` is Hilbert–Schmidt. With `R = U* P U` the conjugated
projection, the displacement `R - P` is Hilbert–Schmidt, its cube `(R - P)³` is trace class, and
the trace of the cube equals the relative index of the pair `(R, P)`, which in turn equals
`dim(ran R ∩ ker P) - dim(ran P ∩ ker R)`.

## Main results

- `RestrictedUnitaryDatum.opTrace_cubicDefect_eq_relativeIndex`: `tr((R - P)³) = ind(R, P)`.
- `RestrictedUnitaryDatum.relativeIndex_eq_intersection_finrank_sub`:
  `ind(R, P) = dim(ran R ∩ ker P) - dim(ran P ∩ ker R)`.
- `restrictedUnitaryCubicRelativeIndex_operator_closed`: both identities, for every complex Hilbert
  space and every restricted unitary datum.

## Hypotheses

The results are unconditional for every `RestrictedUnitaryDatum`: the structure itself supplies
that `P` is an orthogonal projection, `U` is unitary, and `PU - UP` is Hilbert–Schmidt. No other
premise is used.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For a restricted unitary datum with conjugated projection `R = U* P U`, the operator trace of
the cubic defect `(R - P)³` equals the relative index of `(R, P)`. -/
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

/-- For a restricted unitary datum, the relative index of `(R, P)` equals
`dim(ran R ∩ ker P) - dim(ran P ∩ ker R)`. -/
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

/-- For every complex Hilbert space and every restricted unitary datum,
`tr((R - P)³) = ind(R, P) = dim(ran R ∩ ker P) - dim(ran P ∩ ker R)`. -/
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
