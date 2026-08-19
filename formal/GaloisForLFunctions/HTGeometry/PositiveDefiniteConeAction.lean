import GaloisForLFunctions.HTGeometry.PositiveDefiniteCone
import GaloisForLFunctions.HTGeometry.MacbeathConvexDomain
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# The action of `SL(n, ℤ)` on the positive definite cone

An integral unimodular matrix acts on real symmetric matrices by congruence, `A ↦ g · A · gᵀ`.  The
action preserves symmetry and positive definiteness — the latter because `g` is invertible over `ℝ`
— and is continuous, being linear.

This supplies the group action that Macbeath's criterion on a convex domain consumes.

* `slReal` : an integral unimodular matrix, read over `ℝ`.
* `symmConj` : the congruence action on symmetric matrices.
* the `MulAction` and `ContinuousConstSMul` instances on `posDefCone`.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Pointwise

variable {n : ℕ}

/-- An integral unimodular matrix, read over `ℝ`. -/
noncomputable def slReal (g : Matrix.SpecialLinearGroup (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  (Int.castRingHom ℝ).mapMatrix (g : Matrix (Fin n) (Fin n) ℤ)

@[simp]
theorem slReal_one : slReal (1 : Matrix.SpecialLinearGroup (Fin n) ℤ) = 1 := by
  show (Int.castRingHom ℝ).mapMatrix (1 : Matrix (Fin n) (Fin n) ℤ) = 1
  exact map_one _

theorem slReal_mul (g h : Matrix.SpecialLinearGroup (Fin n) ℤ) :
    slReal (g * h) = slReal g * slReal h := by
  unfold slReal
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact map_mul _ _ _

theorem slReal_det (g : Matrix.SpecialLinearGroup (Fin n) ℤ) : (slReal g).det = 1 := by
  unfold slReal
  rw [← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe]
  simp

theorem slReal_isUnit (g : Matrix.SpecialLinearGroup (Fin n) ℤ) : IsUnit (slReal g) :=
  (Matrix.isUnit_iff_isUnit_det _).2 (by rw [slReal_det]; exact isUnit_one)

theorem slReal_vecMul_injective (g : Matrix.SpecialLinearGroup (Fin n) ℤ) :
    Function.Injective (slReal g).vecMul :=
  Matrix.vecMul_injective_of_isUnit (slReal_isUnit g)

/-- The congruence action on symmetric matrices. -/
noncomputable def symmConj (g : Matrix.SpecialLinearGroup (Fin n) ℤ) (A : symmMatrices n) :
    symmMatrices n :=
  ⟨slReal g * (A : Matrix (Fin n) (Fin n) ℝ) * (slReal g)ᵀ, by
    show (slReal g * (A : Matrix (Fin n) (Fin n) ℝ) * (slReal g)ᵀ)ᵀ
      = slReal g * (A : Matrix (Fin n) (Fin n) ℝ) * (slReal g)ᵀ
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      (mem_symmMatrices_iff.1 A.2), Matrix.mul_assoc]⟩

@[simp]
theorem symmConj_coe (g : Matrix.SpecialLinearGroup (Fin n) ℤ) (A : symmMatrices n) :
    ((symmConj g A : symmMatrices n) : Matrix (Fin n) (Fin n) ℝ)
      = slReal g * (A : Matrix (Fin n) (Fin n) ℝ) * (slReal g)ᵀ := rfl

theorem symmConj_one (A : symmMatrices n) : symmConj 1 A = A := by
  refine Subtype.ext ?_
  rw [symmConj_coe, slReal_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem symmConj_mul (g h : Matrix.SpecialLinearGroup (Fin n) ℤ) (A : symmMatrices n) :
    symmConj (g * h) A = symmConj g (symmConj h A) := by
  refine Subtype.ext ?_
  rw [symmConj_coe, symmConj_coe, symmConj_coe, slReal_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem symmConj_posDef {g : Matrix.SpecialLinearGroup (Fin n) ℤ} {A : symmMatrices n}
    (hA : (A : Matrix (Fin n) (Fin n) ℝ).PosDef) :
    ((symmConj g A : symmMatrices n) : Matrix (Fin n) (Fin n) ℝ).PosDef := by
  rw [symmConj_coe]
  have := hA.mul_mul_conjTranspose_same (B := slReal g) (slReal_vecMul_injective g)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- The congruence action on the positive definite cone. -/
noncomputable instance posDefConeMulAction :
    MulAction (Matrix.SpecialLinearGroup (Fin n) ℤ) (posDefCone n) where
  smul g A := ⟨symmConj g (A : symmMatrices n), symmConj_posDef A.2⟩
  one_smul A := Subtype.ext (symmConj_one (A : symmMatrices n))
  mul_smul g h A := Subtype.ext (symmConj_mul g h (A : symmMatrices n))

@[simp]
theorem posDefCone_smul_coe (g : Matrix.SpecialLinearGroup (Fin n) ℤ) (A : posDefCone n) :
    (((g • A : posDefCone n) : symmMatrices n) : Matrix (Fin n) (Fin n) ℝ)
      = slReal g * ((A : symmMatrices n) : Matrix (Fin n) (Fin n) ℝ) * (slReal g)ᵀ := rfl

theorem continuous_symmConj (g : Matrix.SpecialLinearGroup (Fin n) ℤ) :
    Continuous (symmConj (n := n) g) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const

noncomputable instance posDefConeContinuousConstSMul :
    ContinuousConstSMul (Matrix.SpecialLinearGroup (Fin n) ℤ) (posDefCone n) where
  continuous_const_smul g := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_symmConj g).comp continuous_subtype_val

/-- **`SL(n, ℤ)` is finitely presented as soon as reduction theory supplies a connected fundamental
open set with finitely many overlaps.**  All the topology is discharged by the positive definite
cone being open and convex; what is left is exactly Siegel's finiteness property. -/
theorem isFinitelyPresented_specialLinearGroup_of_siegel {n : ℕ}
    {V : Set (posDefCone n)} (hVopen : IsOpen V) (hVne : V.Nonempty) (hVconn : IsPreconnected V)
    (hcover : ⋃ g : Matrix.SpecialLinearGroup (Fin n) ℤ, g • V = (Set.univ : Set (posDefCone n)))
    (hfin : (meetSet (G := Matrix.SpecialLinearGroup (Fin n) ℤ) V).Finite) :
    IsFinitelyPresented (Matrix.SpecialLinearGroup (Fin n) ℤ) :=
  isFinitelyPresented_of_macbeath_convex isOpen_posDefCone convex_posDefCone posDefCone_nonempty
    hVopen hVne hVconn hcover hfin

end GaloisForLFunctions.HTGeometry
