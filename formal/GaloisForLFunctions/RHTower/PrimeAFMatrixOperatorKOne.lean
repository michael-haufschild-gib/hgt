import GaloisForLFunctions.RHTower.PrimeAFComplexUnitsKOne
import GaloisForLFunctions.RHTower.PrimeQuasiLocalCharge
import GaloisForLFunctions.HTGeometry.KroneckerAmplification

/-!
# Finite matrix-stage operator K₁ and determinant

For a nonempty finite carrier `iota`, the operator-`K₁` group of the circle matrix stage is
modeled by the additive fundamental group of `U(iota)`.  This file constructs the literal
determinant map to `π₁(ℂˣ) ≅ ℤ`, plus tensor-identity amplification on the unitary group.
-/

open GaloisForLFunctions.HTGeometry
open scoped Kronecker

namespace PrimeQuasiLocalCharge

noncomputable section

variable {iota : Type*} [Fintype iota] [DecidableEq iota]

theorem unitaryMatrix_det_ne_zero (U : Matrix.unitaryGroup iota ℂ) :
    (U : Matrix iota iota ℂ).det ≠ 0 := by
  have hdet : star (U : Matrix iota iota ℂ).det *
      (U : Matrix iota iota ℂ).det = 1 :=
    (Unitary.mem_iff.mp (Matrix.det_of_mem_unitary U.2)).1
  intro hzero
  rw [hzero, mul_zero] at hdet
  exact zero_ne_one hdet

/-- Determinant of a unitary matrix, regarded as an element of `ℂˣ`. -/
def unitaryDeterminantUnits (U : Matrix.unitaryGroup iota ℂ) : Units ℂ :=
  (unitsHomeomorphNeZero (G₀ := ℂ)).symm
    ⟨(U : Matrix iota iota ℂ).det, unitaryMatrix_det_ne_zero U⟩

@[simp] theorem unitaryDeterminantUnits_coe (U : Matrix.unitaryGroup iota ℂ) :
    (unitaryDeterminantUnits U : ℂ) = (U : Matrix iota iota ℂ).det := by
  have h := (unitsHomeomorphNeZero (G₀ := ℂ)).apply_symm_apply
    ⟨(U : Matrix iota iota ℂ).det, unitaryMatrix_det_ne_zero U⟩
  exact congrArg Subtype.val h

theorem continuous_unitaryDeterminantUnits :
    Continuous (unitaryDeterminantUnits : Matrix.unitaryGroup iota ℂ → Units ℂ) := by
  apply (unitsHomeomorphNeZero (G₀ := ℂ)).symm.continuous.comp
  apply continuous_induced_rng.2
  change Continuous (fun U : Matrix.unitaryGroup iota ℂ ↦
    (U : Matrix iota iota ℂ).det)
  fun_prop

@[simp] theorem unitaryDeterminantUnits_one :
    unitaryDeterminantUnits (1 : Matrix.unitaryGroup iota ℂ) = 1 := by
  apply Units.ext
  rw [unitaryDeterminantUnits_coe]
  simp

/-- Literal finite matrix-stage operator `K₁`, additively presented. -/
abbrev FiniteMatrixCircleOperatorKOne (iota : Type*) [Fintype iota] [DecidableEq iota] :=
  Additive (FundamentalGroup (Matrix.unitaryGroup iota ℂ) 1)

noncomputable local instance : CommGroup
    (FundamentalGroup (Matrix.unitaryGroup iota ℂ) 1) :=
  fundamentalGroupCommGroup

noncomputable local instance : CommGroup (FundamentalGroup (Units ℂ) 1) :=
  fundamentalGroupCommGroup

/-- Determinant-induced map from a finite matrix-stage operator `K₁` group to the scalar stage. -/
def finiteMatrixDeterminantKOneHom :
    FiniteMatrixCircleOperatorKOne iota →+ ComplexUnitsOperatorKOne := by
  let f : C(Matrix.unitaryGroup iota ℂ, Units ℂ) :=
    ⟨unitaryDeterminantUnits, continuous_unitaryDeterminantUnits⟩
  have h := FundamentalGroup.map f (1 : Matrix.unitaryGroup iota ℂ)
  have hone : f (1 : Matrix.unitaryGroup iota ℂ) = 1 :=
    unitaryDeterminantUnits_one
  rw [hone] at h
  exact MonoidHom.toAdditive h

/-- Integer determinant charge on the literal matrix-stage operator `K₁` group. -/
def finiteMatrixOperatorKOneCharge :
    FiniteMatrixCircleOperatorKOne iota →+ ℤ :=
  complexUnitsOperatorKOneEquivInt.toAddMonoidHom.comp
    finiteMatrixDeterminantKOneHom

/-- Tensor-identity amplification of a unitary matrix. -/
def amplifyUnitary (d : ℕ) (U : Matrix.unitaryGroup iota ℂ) :
    Matrix.unitaryGroup (iota × Fin d) ℂ :=
  ⟨(U : Matrix iota iota ℂ) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ),
    kronecker_one_mem_unitary U.2⟩

theorem continuous_amplifyUnitary (d : ℕ) :
    Continuous (amplifyUnitary d : Matrix.unitaryGroup iota ℂ →
      Matrix.unitaryGroup (iota × Fin d) ℂ) := by
  apply continuous_induced_rng.2
  change Continuous (fun U : Matrix.unitaryGroup iota ℂ ↦
    fun (p q : iota × Fin d) ↦ (U : Matrix iota iota ℂ) p.1 q.1 *
      (1 : Matrix (Fin d) (Fin d) ℂ) p.2 q.2)
  apply continuous_pi
  intro p
  apply continuous_pi
  intro q
  have hp : Continuous (fun U : Matrix.unitaryGroup iota ℂ ↦
      (U : Matrix iota iota ℂ) p.1) :=
    (continuous_apply p.1).comp continuous_subtype_val
  have hpq : Continuous (fun U : Matrix.unitaryGroup iota ℂ ↦
      (U : Matrix iota iota ℂ) p.1 q.1) :=
    (continuous_apply q.1).comp hp
  exact hpq.mul continuous_const

@[simp] theorem amplifyUnitary_one (d : ℕ) :
    amplifyUnitary d (1 : Matrix.unitaryGroup iota ℂ) = 1 := by
  apply Subtype.ext
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [amplifyUnitary, Matrix.one_apply]

/-- Tensor amplification on the literal matrix-stage operator `K₁` group. -/
def amplifyUnitaryKOneHom (d : ℕ) :
    FiniteMatrixCircleOperatorKOne iota →+
      FiniteMatrixCircleOperatorKOne (iota × Fin d) := by
  let f : C(Matrix.unitaryGroup iota ℂ,
      Matrix.unitaryGroup (iota × Fin d) ℂ) :=
    ⟨amplifyUnitary d, continuous_amplifyUnitary d⟩
  have h := FundamentalGroup.map f (1 : Matrix.unitaryGroup iota ℂ)
  have hone : f (1 : Matrix.unitaryGroup iota ℂ) = 1 := amplifyUnitary_one d
  rw [hone] at h
  exact MonoidHom.toAdditive h

/-- Determinant of tensor-identity amplification is the `d`th power of determinant. -/
theorem unitaryDeterminantUnits_amplifyUnitary (d : ℕ)
    (U : Matrix.unitaryGroup iota ℂ) :
    unitaryDeterminantUnits (amplifyUnitary d U) = unitaryDeterminantUnits U ^ d := by
  apply Units.ext
  simp only [unitaryDeterminantUnits_coe, Units.val_pow_eq_pow_val]
  change Matrix.det ((U : Matrix iota iota ℂ) ⊗ₖ
      (1 : Matrix (Fin d) (Fin d) ℂ)) =
    Matrix.det (U : Matrix iota iota ℂ) ^ d
  simpa [amplifyMatrix] using det_amplifyMatrix d (U : Matrix iota iota ℂ)

end

end PrimeQuasiLocalCharge
