import GaloisForLFunctions.HTGeometry.ColorGramMinkowskiCone

/-!
# Three source directions do not carry colour `SU(3)`

A projective binary source square has three nonidentity directions.  Their Pauli/quaternion
composition induces the complex-bilinear cross bracket on `ℂ³`.  It is tempting to identify this
three-dimensional space directly with the fundamental colour carrier and declare its unitary
frame ambiguity to be `SU(3)`.

That identification is false if source composition is fixed.  The explicit matrix

```
diag(i, -i, 1)
```

is unitary and has determinant one, but it does not preserve the source bracket.  Hence full colour
`SU(3)` cannot be the automorphism group of the fixed three-direction source-composition law.

The surviving alternatives are structural: colour must act on an independent consequence
multiplicity, or the source-composition tensor must itself transform covariantly.  The theorem
below supplies the exact finite no-go that any such repair must respect.
-/

open Matrix
open scoped ComplexOrder Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Complex-bilinear bracket carried by the three Pauli/quaternion source directions. -/
def sourceThreeBracket
    (x y : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![x 1 * y 2 - x 2 * y 1,
    x 2 * y 0 - x 0 * y 2,
    x 0 * y 1 - x 1 * y 0]

/-- First coordinate source direction. -/
def sourceThreeE0 : Fin 3 → ℂ := ![1, 0, 0]

/-- Second coordinate source direction. -/
def sourceThreeE1 : Fin 3 → ℂ := ![0, 1, 0]

/-- Third coordinate source direction. -/
def sourceThreeE2 : Fin 3 → ℂ := ![0, 0, 1]

/-- A determinant-one unitary phase that fails to preserve source composition. -/
def sourceThreeSpecialPhase : Matrix (Fin 3) (Fin 3) ℂ :=
  !![Complex.I, 0, 0;
     0, -Complex.I, 0;
     0, 0, 1]

/-- The explicit phase is unitary. -/
theorem sourceThreeSpecialPhase_conjTranspose_mul_self :
    sourceThreeSpecialPhaseᴴ * sourceThreeSpecialPhase = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceThreeSpecialPhase, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.conjTranspose_apply, Complex.I_mul_I]

/-- The explicit phase has determinant one. -/
theorem sourceThreeSpecialPhase_det :
    sourceThreeSpecialPhase.det = 1 := by
  simp [sourceThreeSpecialPhase, Matrix.det_fin_three, Complex.I_mul_I]

/--
The determinant-one unitary phase is not equivariant for the fixed source bracket.

On the pair `(e₁, e₂)`, the left side is `i e₀`, whereas the right side is `-i e₀`.
-/
theorem sourceThreeSpecialPhase_not_bracket_equivariant :
    sourceThreeSpecialPhase *ᵥ sourceThreeBracket sourceThreeE1 sourceThreeE2 ≠
      sourceThreeBracket
        (sourceThreeSpecialPhase *ᵥ sourceThreeE1)
        (sourceThreeSpecialPhase *ᵥ sourceThreeE2) := by
  intro h
  have h0 := congrFun h 0
  simp [sourceThreeSpecialPhase, sourceThreeBracket, sourceThreeE1,
    sourceThreeE2, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0
  have him := congrArg Complex.im h0
  norm_num at him

/--
Full determinant-one unitary symmetry does not preserve the fixed three-source composition law.

This existential witness is the exact no-go needed to reject the direct identification of the
three projective-source directions with a colour fundamental carrying its full `SU(3)` action.
-/
theorem exists_specialUnitary_not_sourceThreeBracket_equivariant :
    ∃ U : Matrix (Fin 3) (Fin 3) ℂ,
      Uᴴ * U = 1 ∧
      U.det = 1 ∧
      ∃ x y : Fin 3 → ℂ,
        U *ᵥ sourceThreeBracket x y ≠
          sourceThreeBracket (U *ᵥ x) (U *ᵥ y) := by
  exact ⟨sourceThreeSpecialPhase,
    sourceThreeSpecialPhase_conjTranspose_mul_self,
    sourceThreeSpecialPhase_det,
    sourceThreeE1, sourceThreeE2,
    sourceThreeSpecialPhase_not_bracket_equivariant⟩

/--
Transport the source-composition tensor together with a unitary frame.

This is the positive replacement for demanding that every frame preserve one fixed bracket.
-/
def transportedSourceThreeBracket
    (U : Matrix (Fin 3) (Fin 3) ℂ)
    (x y : Fin 3 → ℂ) : Fin 3 → ℂ :=
  U *ᵥ sourceThreeBracket (Uᴴ *ᵥ x) (Uᴴ *ᵥ y)

/--
When the composition tensor is transported with a unitary frame, that frame is exactly
composition-equivariant between the old and transported brackets.
-/
theorem transportedSourceThreeBracket_equivariant
    (U : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : Uᴴ * U = 1)
    (x y : Fin 3 → ℂ) :
    transportedSourceThreeBracket U (U *ᵥ x) (U *ᵥ y) =
      U *ᵥ sourceThreeBracket x y := by
  simp only [transportedSourceThreeBracket, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

/--
For the no-go witness, the transported bracket is genuinely different from the original bracket.

Thus covariant composition is not a verbal relabeling of fixed-composition invariance: the
composition tensor itself moves along a nontrivial frame orbit.
-/
theorem sourceThreeSpecialPhase_transported_ne_original :
    transportedSourceThreeBracket sourceThreeSpecialPhase
        (sourceThreeSpecialPhase *ᵥ sourceThreeE1)
        (sourceThreeSpecialPhase *ᵥ sourceThreeE2) ≠
      sourceThreeBracket
        (sourceThreeSpecialPhase *ᵥ sourceThreeE1)
        (sourceThreeSpecialPhase *ᵥ sourceThreeE2) := by
  rw [transportedSourceThreeBracket_equivariant sourceThreeSpecialPhase
    sourceThreeSpecialPhase_conjTranspose_mul_self sourceThreeE1 sourceThreeE2]
  exact sourceThreeSpecialPhase_not_bracket_equivariant

end GaloisForLFunctions.HTGeometry
