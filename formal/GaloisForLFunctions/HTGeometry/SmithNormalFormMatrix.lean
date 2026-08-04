import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FreeModule.Int

/-!
# Smith normal form of a nonsingular integer matrix

A square integer matrix with nonzero determinant is a unimodular matrix times a diagonal matrix
times a unimodular matrix, with all diagonal entries nonzero.

The statement is the matrix form of the Smith normal form of the image lattice: the matrix acts
injectively on `ℤ ^ r`, so its image is a full-rank sublattice, and a Smith basis pair for that
inclusion turns into a pair of change-of-basis matrices, which are unimodular.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

open scoped Matrix

noncomputable section

variable {r : ℕ}

/-- A square integer matrix of nonzero determinant acts injectively. -/
theorem mulVecLin_injective_of_det_ne_zero {M : Matrix (Fin r) (Fin r) ℤ} (hM : M.det ≠ 0) :
    Function.Injective (Matrix.mulVecLin M) := by
  intro u v huv
  have h0 : M *ᵥ (u - v) = 0 := by
    have huv' : M *ᵥ u = M *ᵥ v := huv
    rw [Matrix.mulVec_sub, huv', sub_self]
  have h1 : M.adjugate *ᵥ (M *ᵥ (u - v)) = M.det • (u - v) := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
    simp
  rw [h0, Matrix.mulVec_zero] at h1
  rcases smul_eq_zero.mp h1.symm with h | h
  · exact absurd h hM
  · exact sub_eq_zero.mp h

/-- **Smith normal form of a nonsingular integer matrix.** -/
theorem exists_unimodular_diagonal (M : Matrix (Fin r) (Fin r) ℤ) (hM : M.det ≠ 0) :
    ∃ (U V : Matrix (Fin r) (Fin r) ℤ) (d : Fin r → ℤ),
      IsUnit U.det ∧ IsUnit V.det ∧ (∀ i, d i ≠ 0) ∧ M = U * Matrix.diagonal d * V := by
  classical
  set std : Basis (Fin r) ℤ (Fin r → ℤ) := Pi.basisFun ℤ (Fin r) with hstd
  set f : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ) := Matrix.mulVecLin M with hf
  have hinj : Function.Injective f := mulVecLin_injective_of_det_ne_zero hM
  set e : (Fin r → ℤ) ≃ₗ[ℤ] ↥(LinearMap.range f) :=
    LinearEquiv.ofInjective f hinj with he
  have hrank : Module.finrank ℤ ↥(LinearMap.range f) = Module.finrank ℤ (Fin r → ℤ) :=
    (LinearEquiv.finrank_eq e).symm
  obtain ⟨b', a, ab', hab'⟩ :=
    Submodule.exists_smith_normal_form_of_rank_eq (N := LinearMap.range f) std hrank
  set c : Basis (Fin r) ℤ (Fin r → ℤ) := ab'.map e.symm with hc
  have hfc : ∀ i, f (c i) = a i • b' i := by
    intro i
    have hce : e (c i) = ab' i := by
      rw [hc, Basis.map_apply, LinearEquiv.apply_symm_apply]
    have hval : (e (c i) : Fin r → ℤ) = f (c i) := rfl
    rw [← hval, hce, hab' i]
  have hdiag : LinearMap.toMatrix c b' f = Matrix.diagonal a := by
    ext i j
    rw [LinearMap.toMatrix_apply, hfc j, map_smul, Basis.repr_self, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  have hMstd : LinearMap.toMatrix std std f = M := by
    rw [hstd, LinearMap.toMatrix_eq_toMatrix', hf]
    exact (LinearEquiv.eq_symm_apply LinearMap.toMatrix').mp rfl
  have hchain : (b'.toMatrix std) * M * (std.toMatrix c) = Matrix.diagonal a := by
    rw [← hMstd, basis_toMatrix_mul_linearMap_toMatrix, linearMap_toMatrix_mul_basis_toMatrix,
      hdiag]
  refine ⟨std.toMatrix b', c.toMatrix std, a, ?_, ?_, ?_, ?_⟩
  · refine IsUnit.of_mul_eq_one ((b'.toMatrix std).det) ?_
    rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  · refine IsUnit.of_mul_eq_one ((std.toMatrix c).det) ?_
    rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  · intro i hai
    have hdet : (Matrix.diagonal a).det = 0 := by
      rw [Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hai
    rw [← hchain, Matrix.det_mul, Matrix.det_mul] at hdet
    rcases mul_eq_zero.mp hdet with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · have hunit : IsUnit ((b'.toMatrix std).det) := by
          refine IsUnit.of_mul_eq_one ((std.toMatrix b').det) ?_
          rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
        rw [h'] at hunit
        exact (not_isUnit_zero (M₀ := ℤ)) hunit
      · exact hM h'
    · have hunit : IsUnit ((std.toMatrix c).det) := by
        refine IsUnit.of_mul_eq_one ((c.toMatrix std).det) ?_
        rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
      rw [h] at hunit
      exact (not_isUnit_zero (M₀ := ℤ)) hunit
  · have hleft : (std.toMatrix b') * (b'.toMatrix std) = 1 :=
      Module.Basis.toMatrix_mul_toMatrix_flip _ _
    have hright : (std.toMatrix c) * (c.toMatrix std) = 1 :=
      Module.Basis.toMatrix_mul_toMatrix_flip _ _
    have step1 : M = (std.toMatrix b') * ((b'.toMatrix std) * M) := by
      rw [← Matrix.mul_assoc, hleft, Matrix.one_mul]
    have step2 : (b'.toMatrix std) * M
        = ((b'.toMatrix std) * M * (std.toMatrix c)) * (c.toMatrix std) := by
      rw [Matrix.mul_assoc, hright, Matrix.mul_one]
    rw [step1, step2, hchain, Matrix.mul_assoc]


end

end GaloisForLFunctions.HTGeometry
