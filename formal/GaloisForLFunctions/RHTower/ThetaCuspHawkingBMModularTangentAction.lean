import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularSpacetimeCoordinates

/-! The actual modular coordinate differentials act on spacetime tangent pairs. -/

open Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
noncomputable section

/-- The actual modular coordinate differential acts by the original complex angular derivative. -/
theorem modularSpacetimeDifferential_apply (A : SL(2,ℤ)) (z : UpperHalfPlane) (v : Fin 4 → ℝ) :
    modularSpacetimeDifferential A z v =
      ![v 0,v 1,((1/(denom A z)^2)*((v 2:ℂ)+(v 3:ℂ)*Complex.I)).re,
        ((1/(denom A z)^2)*((v 2:ℂ)+(v 3:ℂ)*Complex.I)).im] := by
  have hv : spacetimeAngular v = (v 2:ℂ)+(v 3:ℂ)*Complex.I := rfl
  funext i
  fin_cases i <;> simp [modularSpacetimeDifferential,modular_chart_jacobian,hv]

/-- The identity modular map has the actual identity differential. -/
theorem modularSpacetimeDifferential_one (z : UpperHalfPlane) :
    modularSpacetimeDifferential 1 z = ContinuousLinearMap.id ℝ (Fin 4 → ℝ) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [modularSpacetimeDifferential_apply]
  funext i
  fin_cases i <;> simp

private theorem spacetime_action_comp (A B : SL(2,ℤ)) :
    modularSpacetimePoint (A*B) = modularSpacetimePoint A ∘ modularSpacetimePoint B := by
  funext x
  change spacetimePoint (x 0) (x 1) ((A*B) • ofComplex (spacetimeAngular x)) =
    modularSpacetimePoint A (spacetimePoint (x 0) (x 1) (B • ofComplex (spacetimeAngular x)))
  rw [modularSpacetimePoint_coordinates,mul_smul]

/-- The actual modular differential satisfies the group chain rule, derived from the coordinate maps. -/
theorem modularSpacetimeDifferential_mul (A B : SL(2,ℤ)) (z : UpperHalfPlane) :
    modularSpacetimeDifferential (A*B) z =
      (modularSpacetimeDifferential A (B • z)).comp (modularSpacetimeDifferential B z) := by
  have hA : HasFDerivAt (modularSpacetimePoint A) (modularSpacetimeDifferential A (B • z))
      (modularSpacetimePoint B (spacetimePoint 0 2 z)) := by
    rw [modularSpacetimePoint_coordinates]
    exact modularSpacetimePoint_hasFDerivAt A 0 2 (B • z)
  have h := hA.comp (spacetimePoint 0 2 z) (modularSpacetimePoint_hasFDerivAt B 0 2 z)
  rw [← spacetime_action_comp] at h
  exact (modularSpacetimePoint_hasFDerivAt (A*B) 0 2 z).unique h

/-- An angular point and two actual spacetime tangent vectors. -/
@[ext] structure ModularTangentPair where
  point : UpperHalfPlane
  left : Fin 4 → ℝ
  right : Fin 4 → ℝ

/-- Transport of both tangent vectors by the actual modular coordinate differential. -/
def modularTangentPairAction (A : SL(2,ℤ)) (p : ModularTangentPair) : ModularTangentPair where
  point := A • p.point
  left := modularSpacetimeDifferential A p.point p.left
  right := modularSpacetimeDifferential A p.point p.right

private theorem tangent_one (p : ModularTangentPair) : modularTangentPairAction 1 p = p := by
  cases p
  simp [modularTangentPairAction,modularSpacetimeDifferential_one]

private theorem tangent_mul (A B : SL(2,ℤ)) (p : ModularTangentPair) :
    modularTangentPairAction (A*B) p = modularTangentPairAction A (modularTangentPairAction B p) := by
  cases p
  simp [modularTangentPairAction,modularSpacetimeDifferential_mul,mul_smul]

instance : MulAction (SL(2,ℤ)) ModularTangentPair where
  smul := modularTangentPairAction
  one_smul := tangent_one
  mul_smul := tangent_mul

/-- The quotient identifies points and tangent vectors by their original modular differential. -/
abbrev ModularTangentQuotient := Quotient (MulAction.orbitRel (SL(2,ℤ)) ModularTangentPair)

end
end RHTower.D4BMModularCore
