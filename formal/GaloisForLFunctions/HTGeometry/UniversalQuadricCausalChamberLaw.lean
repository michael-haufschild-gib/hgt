import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolCausalChamber
import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolUniversalMatrixField

/-!
# Curved universal quadric causal chamber

The universal quadric matrix field supplies a positive replacement for the pretemporal flat-linear
no-go.  Its exact dependence boundary is nonlinear and its coefficient curvature is nonzero, yet
the positive-definite chamber of the same matrix pencil is nonempty and every law in it is
differentially independent.  This conclusion uses the exact universal realization and therefore
does not impose coefficient flatness or commutator closure.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

/-- The rank-three quadric symbol as a real-linear matrix pencil. -/
def quadricConeSymbolLinear :
    (Fin 3 → ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun := quadricConeSymbol
  map_add' A B := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [quadricConeSymbol]
  map_smul' a A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [quadricConeSymbol]

/-- The identity-axis direction is a positive-definite point of the quadric causal chamber. -/
theorem quadricCone_identityAxis_mem_causalChamber :
    Pi.single 0 1 ∈ matrixPrincipalCausalChamber quadricConeSymbolLinear := by
  change (quadricConeSymbolLinear (Pi.single 0 1)).PosDef
  have hone : quadricConeSymbolLinear (Pi.single 0 1) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [quadricConeSymbolLinear, quadricConeSymbol]
  rw [hone]
  exact Matrix.PosDef.one

/-- Every positive-definite direction of the universal quadric pencil selects a derivation for
which the two ancestral observables are differentially independent. -/
theorem universalQuadric_causalChamber_derivationIndependent :
    matrixPrincipalCausalChamber quadricConeSymbolLinear ⊆
      {A | DerivationIndependentOver ℝ
        (universalMatrixShiftLaw
          (fun A (_ : ℕ) ↦ quadricConeSymbol A) A)
        (universalShiftAncestor (K := ℝ) 0)} := by
  intro A hA
  change DerivationIndependentOver ℝ
    (universalMatrixShiftDerivation
      (fun (_ : ℕ) ↦ quadricConeSymbol A))
    (universalShiftAncestor (K := ℝ) 0)
  rw [universalMatrixShift_derivationIndependentOver_iff]
  intro n
  exact matrixPrincipalCausalChamber_det_ne_zero
    quadricConeSymbolLinear hA

/-- **Curved causal-chamber universality law.**  One concrete selected-derivation family has a
nonempty causal chamber consisting entirely of differentially independent laws, while its exact
boundary is the nonlinear quadric cone and its coefficient symbol has nonzero curvature. -/
theorem universalQuadric_nonemptyCausalChamber_curvedBoundary :
    (matrixPrincipalCausalChamber quadricConeSymbolLinear).Nonempty ∧
      matrixPrincipalCausalChamber quadricConeSymbolLinear ⊆
        {A | DerivationIndependentOver ℝ
          (universalMatrixShiftLaw
            (fun A (_ : ℕ) ↦ quadricConeSymbol A) A)
          (universalShiftAncestor (K := ℝ) 0)} ∧
      derivationLawDependentSet (K := ℝ)
          (universalMatrixShiftLaw
            (fun A (_ : ℕ) ↦ quadricConeSymbol A))
          (universalShiftAncestor (K := ℝ) 0) =
        {A : Fin 3 → ℝ | A 0 * A 0 = A 1 * A 2} ∧
      matrixCoefficientPrincipalCurvature
          (fun (_ : ℕ) (A : Fin 3 → ℝ) ↦ quadricConeSymbol A) 0
          (Pi.single 1 1) (Pi.single 2 1) ≠ 0 := by
  exact ⟨⟨Pi.single 0 1, quadricCone_identityAxis_mem_causalChamber⟩,
    universalQuadric_causalChamber_derivationIndependent,
    universalQuadric_dependentSet,
    quadricConeSymbol_curvature_ne_zero⟩

end

end GaloisForLFunctions.HTGeometry
