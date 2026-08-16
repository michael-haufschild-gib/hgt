import GaloisForLFunctions.HTGeometry.ReplicaConfigurationBridge

/-!
# Two-sided multiplication by a scalar-inverse pair

A pair of matrices whose two products are the same nonzero scalar multiple of the identity defines
an invertible two-sided multiplication on the operator space.  Conjugating the commutator action of
a matrix by that multiplication is again a commutator action, of the sandwiched matrix rescaled by
the scalar.  This is the exact form of covariance required by the greatest-obstruction symmetry
criterion.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Two-sided multiplication on the matrix algebra. -/
def sandwichMap (Gm Hm : Matrix C C ℂ) : Matrix C C ℂ →ₗ[ℂ] Matrix C C ℂ where
  toFun X := Gm * X * Hm
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' z X := by
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

omit [DecidableEq C] in
@[simp] theorem sandwichMap_apply (Gm Hm X : Matrix C C ℂ) :
    sandwichMap Gm Hm X = Gm * X * Hm := rfl

theorem sandwich_double (Gm Hm X : Matrix C C ℂ) (κ : ℂ) (h : Gm * Hm = κ • 1) :
    Gm * (Hm * X * Gm) * Hm = (κ * κ) • X := by
  have hassoc : Gm * (Hm * X * Gm) * Hm = (Gm * Hm) * X * (Gm * Hm) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc, h, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]

/-- The invertible two-sided multiplication attached to a scalar-inverse pair. -/
def matrixSandwichEquiv (Gm Hm : Matrix C C ℂ) (κ : ℂ) (hκ : κ ≠ 0)
    (h1 : Gm * Hm = κ • 1) (h2 : Hm * Gm = κ • 1) : Matrix C C ℂ ≃ₗ[ℂ] Matrix C C ℂ :=
  LinearEquiv.ofLinear (sandwichMap Gm Hm) ((κ * κ)⁻¹ • sandwichMap Hm Gm)
    (by
      refine LinearMap.ext fun X => ?_
      show Gm * ((κ * κ)⁻¹ • (Hm * X * Gm)) * Hm = X
      rw [Matrix.mul_smul, Matrix.smul_mul, sandwich_double Gm Hm X κ h1, smul_smul,
        inv_mul_cancel₀ (mul_ne_zero hκ hκ), one_smul])
    (by
      refine LinearMap.ext fun X => ?_
      show (κ * κ)⁻¹ • (Hm * (Gm * X * Hm) * Gm) = X
      rw [sandwich_double Hm Gm X κ h2, smul_smul, inv_mul_cancel₀ (mul_ne_zero hκ hκ), one_smul])

@[simp] theorem matrixSandwichEquiv_apply (Gm Hm : Matrix C C ℂ) (κ : ℂ) (hκ : κ ≠ 0)
    (h1 : Gm * Hm = κ • 1) (h2 : Hm * Gm = κ • 1) (X : Matrix C C ℂ) :
    matrixSandwichEquiv Gm Hm κ hκ h1 h2 X = Gm * X * Hm := rfl

@[simp] theorem matrixSandwichEquiv_symm_apply (Gm Hm : Matrix C C ℂ) (κ : ℂ) (hκ : κ ≠ 0)
    (h1 : Gm * Hm = κ • 1) (h2 : Hm * Gm = κ • 1) (X : Matrix C C ℂ) :
    (matrixSandwichEquiv Gm Hm κ hκ h1 h2).symm X = (κ * κ)⁻¹ • (Hm * X * Gm) := rfl

/-- The commutator action of a matrix, as a linear map on the vectorized operator space. -/
def collectiveCommutatorOperator (C : Type*) [Fintype C] [DecidableEq C] :
    Matrix C C ℂ →ₗ[ℂ] (EuclideanSpace ℂ (C × C) →ₗ[ℂ] EuclideanSpace ℂ (C × C)) :=
  (Matrix.toEuclideanLin (𝕜 := ℂ) (n := C × C) (m := C × C)).toLinearMap.comp
    matrixCommutatorRepresentation

theorem commutatorRep_toEuclideanLin_vec (M X : Matrix C C ℂ) :
    (matrixCommutatorRepresentation M).toEuclideanLin (vecLinearEquiv C X) =
      vecLinearEquiv C (ringCommutator M X) := by
  rw [Matrix.toLpLin_apply]
  exact congrArg (WithLp.toLp 2) (matrixCommutatorRepresentation_mulVec_vec M X)

@[simp] theorem collectiveCommutatorOperator_apply (M X : Matrix C C ℂ) :
    collectiveCommutatorOperator C M (vecLinearEquiv C X) =
      vecLinearEquiv C (ringCommutator M X) :=
  commutatorRep_toEuclideanLin_vec M X

/-- Sandwiching a commutator action produces the commutator action of the sandwiched matrix. -/
theorem sandwich_ringCommutator (Gm Hm M X : Matrix C C ℂ) (κ : ℂ) (h1 : Gm * Hm = κ • 1) :
    Gm * ringCommutator M (Hm * X * Gm) * Hm = κ • ringCommutator (Gm * M * Hm) X := by
  rw [ringCommutator, ringCommutator, Matrix.mul_sub, Matrix.sub_mul, smul_sub]
  congr 1
  · have e1 : Gm * (M * (Hm * X * Gm)) * Hm = (Gm * M * Hm) * X * (Gm * Hm) := by
      simp only [Matrix.mul_assoc]
    rw [e1, h1, Matrix.mul_smul, Matrix.mul_one]
  · have e2 : Gm * ((Hm * X * Gm) * M) * Hm = (Gm * Hm) * X * (Gm * M * Hm) := by
      simp only [Matrix.mul_assoc]
    rw [e2, h1]
    simp only [Matrix.smul_mul, Matrix.one_mul]

/-- The invertible two-sided multiplication on the vectorized operator space. -/
def euclideanSandwichEquiv (Gm Hm : Matrix C C ℂ) (κ : ℂ) (hκ : κ ≠ 0)
    (h1 : Gm * Hm = κ • 1) (h2 : Hm * Gm = κ • 1) :
    EuclideanSpace ℂ (C × C) ≃ₗ[ℂ] EuclideanSpace ℂ (C × C) :=
  ((vecLinearEquiv C).symm.trans (matrixSandwichEquiv Gm Hm κ hκ h1 h2)).trans (vecLinearEquiv C)

theorem euclideanSandwichEquiv_apply_vec (Gm Hm : Matrix C C ℂ) (κ : ℂ) (hκ : κ ≠ 0)
    (h1 : Gm * Hm = κ • 1) (h2 : Hm * Gm = κ • 1) (X : Matrix C C ℂ) :
    euclideanSandwichEquiv Gm Hm κ hκ h1 h2 (vecLinearEquiv C X) =
      vecLinearEquiv C (Gm * X * Hm) := rfl

theorem euclideanSandwichEquiv_symm_apply_vec (Gm Hm : Matrix C C ℂ) (κ : ℂ) (hκ : κ ≠ 0)
    (h1 : Gm * Hm = κ • 1) (h2 : Hm * Gm = κ • 1) (X : Matrix C C ℂ) :
    (euclideanSandwichEquiv Gm Hm κ hκ h1 h2).symm (vecLinearEquiv C X) =
      vecLinearEquiv C ((κ * κ)⁻¹ • (Hm * X * Gm)) := rfl

/-- **Exact covariance of the commutator action under two-sided multiplication.** -/
theorem euclideanSandwichEquiv_conj_commutatorOperator (Gm Hm : Matrix C C ℂ) (κ : ℂ) (hκ : κ ≠ 0)
    (h1 : Gm * Hm = κ • 1) (h2 : Hm * Gm = κ • 1) (M : Matrix C C ℂ) :
    (((euclideanSandwichEquiv Gm Hm κ hκ h1 h2 :
          EuclideanSpace ℂ (C × C) →ₗ[ℂ] EuclideanSpace ℂ (C × C)).comp
        (collectiveCommutatorOperator C M)).comp
      ((euclideanSandwichEquiv Gm Hm κ hκ h1 h2).symm :
        EuclideanSpace ℂ (C × C) →ₗ[ℂ] EuclideanSpace ℂ (C × C))) =
      collectiveCommutatorOperator C (κ⁻¹ • (Gm * M * Hm)) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨X, rfl⟩ := (vecLinearEquiv C).surjective x
  have hstep1 : (euclideanSandwichEquiv Gm Hm κ hκ h1 h2).symm (vecLinearEquiv C X) =
      vecLinearEquiv C ((κ * κ)⁻¹ • (Hm * X * Gm)) :=
    euclideanSandwichEquiv_symm_apply_vec Gm Hm κ hκ h1 h2 X
  have hstep2 : collectiveCommutatorOperator C M
      (vecLinearEquiv C ((κ * κ)⁻¹ • (Hm * X * Gm))) =
      vecLinearEquiv C (ringCommutator M ((κ * κ)⁻¹ • (Hm * X * Gm))) :=
    collectiveCommutatorOperator_apply M _
  have hstep3 : ringCommutator M ((κ * κ)⁻¹ • (Hm * X * Gm)) =
      (κ * κ)⁻¹ • ringCommutator M (Hm * X * Gm) := by
    rw [ringCommutator, ringCommutator, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
  have hstep4 : euclideanSandwichEquiv Gm Hm κ hκ h1 h2
      (vecLinearEquiv C ((κ * κ)⁻¹ • ringCommutator M (Hm * X * Gm))) =
      vecLinearEquiv C (Gm * ((κ * κ)⁻¹ • ringCommutator M (Hm * X * Gm)) * Hm) :=
    euclideanSandwichEquiv_apply_vec Gm Hm κ hκ h1 h2 _
  have hstep5 : Gm * ((κ * κ)⁻¹ • ringCommutator M (Hm * X * Gm)) * Hm =
      κ⁻¹ • ringCommutator (Gm * M * Hm) X := by
    rw [Matrix.mul_smul, Matrix.smul_mul, sandwich_ringCommutator Gm Hm M X κ h1, smul_smul]
    congr 1
    field_simp
  have hrhs : collectiveCommutatorOperator C (κ⁻¹ • (Gm * M * Hm)) (vecLinearEquiv C X) =
      vecLinearEquiv C (κ⁻¹ • ringCommutator (Gm * M * Hm) X) := by
    rw [collectiveCommutatorOperator_apply, ringCommutator, ringCommutator, Matrix.smul_mul,
      Matrix.mul_smul, smul_sub]
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  show euclideanSandwichEquiv Gm Hm κ hκ h1 h2
      (collectiveCommutatorOperator C M
        ((euclideanSandwichEquiv Gm Hm κ hκ h1 h2).symm (vecLinearEquiv C X))) = _
  rw [hstep1, hstep2, hstep3, hstep4, hstep5, hrhs]

/-- **Exact covariance under the inverse two-sided multiplication.** -/
theorem euclideanSandwichEquiv_symm_conj_commutatorOperator (Gm Hm : Matrix C C ℂ) (κ : ℂ)
    (hκ : κ ≠ 0) (h1 : Gm * Hm = κ • 1) (h2 : Hm * Gm = κ • 1) (M : Matrix C C ℂ) :
    ((((euclideanSandwichEquiv Gm Hm κ hκ h1 h2).symm :
          EuclideanSpace ℂ (C × C) →ₗ[ℂ] EuclideanSpace ℂ (C × C)).comp
        (collectiveCommutatorOperator C M)).comp
      ((euclideanSandwichEquiv Gm Hm κ hκ h1 h2) :
        EuclideanSpace ℂ (C × C) →ₗ[ℂ] EuclideanSpace ℂ (C × C))) =
      collectiveCommutatorOperator C (κ⁻¹ • (Hm * M * Gm)) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨X, rfl⟩ := (vecLinearEquiv C).surjective x
  have hstep1 : euclideanSandwichEquiv Gm Hm κ hκ h1 h2 (vecLinearEquiv C X) =
      vecLinearEquiv C (Gm * X * Hm) :=
    euclideanSandwichEquiv_apply_vec Gm Hm κ hκ h1 h2 X
  have hstep2 : collectiveCommutatorOperator C M (vecLinearEquiv C (Gm * X * Hm)) =
      vecLinearEquiv C (ringCommutator M (Gm * X * Hm)) :=
    collectiveCommutatorOperator_apply M _
  have hstep3 : (euclideanSandwichEquiv Gm Hm κ hκ h1 h2).symm
      (vecLinearEquiv C (ringCommutator M (Gm * X * Hm))) =
      vecLinearEquiv C ((κ * κ)⁻¹ • (Hm * ringCommutator M (Gm * X * Hm) * Gm)) :=
    euclideanSandwichEquiv_symm_apply_vec Gm Hm κ hκ h1 h2 _
  have hstep4 : ((κ * κ)⁻¹ • (Hm * ringCommutator M (Gm * X * Hm) * Gm)) =
      κ⁻¹ • ringCommutator (Hm * M * Gm) X := by
    rw [sandwich_ringCommutator Hm Gm M X κ h2, smul_smul]
    congr 1
    field_simp
  have hrhs : collectiveCommutatorOperator C (κ⁻¹ • (Hm * M * Gm)) (vecLinearEquiv C X) =
      vecLinearEquiv C (κ⁻¹ • ringCommutator (Hm * M * Gm) X) := by
    rw [collectiveCommutatorOperator_apply, ringCommutator, ringCommutator, Matrix.smul_mul,
      Matrix.mul_smul, smul_sub]
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  show (euclideanSandwichEquiv Gm Hm κ hκ h1 h2).symm
      (collectiveCommutatorOperator C M
        (euclideanSandwichEquiv Gm Hm κ hκ h1 h2 (vecLinearEquiv C X))) = _
  rw [hstep1, hstep2, hstep3, hstep4, hrhs]

end GaloisForLFunctions.HTGeometry
