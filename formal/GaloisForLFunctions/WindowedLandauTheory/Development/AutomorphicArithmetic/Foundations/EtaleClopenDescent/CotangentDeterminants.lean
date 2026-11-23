import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Basic

/-! The determinant and exterior-degree coefficients of a cotangent
endomorphism are independent of the parameter basis and row convention. -/

noncomputable section

open scoped Matrix

namespace GlobalTheory.SchemeCohomology

variable {k : Type} [Field k] {d : ℕ}

private theorem det_similarity (A B P Q : Matrix (Fin d) (Fin d) k)
    (hB : B = P * A * Q) (hP : P * Q = 1) :
    (1 - B).det = (1 - A).det ∧
      (1 + (Polynomial.X : Polynomial k) • B.map Polynomial.C).det =
        (1 + (Polynomial.X : Polynomial k) • A.map Polynomial.C).det := by
  have hdet : P.det * Q.det = 1 := by rw [← Matrix.det_mul, hP, Matrix.det_one]
  constructor
  · have h : 1 - B = P * (1 - A) * Q := by
      rw [hB, Matrix.mul_sub, Matrix.sub_mul, mul_one, hP]
    rw [h, Matrix.det_mul, Matrix.det_mul,
      mul_right_comm P.det (1 - A).det Q.det, hdet, one_mul]
  · let P' := P.map (Polynomial.C : k →+* Polynomial k)
    let Q' := Q.map (Polynomial.C : k →+* Polynomial k)
    have hP' : P' * Q' = 1 := by
      change P.map _ * Q.map _ = _
      rw [← Matrix.map_mul, hP, Matrix.map_one Polynomial.C (map_zero _) (map_one _)]
    have hd : P'.det * Q'.det = 1 := by rw [← Matrix.det_mul, hP', Matrix.det_one]
    have h : 1 + (Polynomial.X : Polynomial k) • B.map Polynomial.C =
        P' * (1 + (Polynomial.X : Polynomial k) • A.map Polynomial.C) * Q' := by
      rw [hB, Matrix.map_mul, Matrix.map_mul, Matrix.mul_add, Matrix.add_mul,
        mul_one, hP', Matrix.mul_smul, Matrix.smul_mul]
    rw [h, Matrix.det_mul, Matrix.det_mul, mul_right_comm P'.det _ Q'.det, hd, one_mul]

variable {V : Type} [AddCommGroup V] [Module k V]

/-- A matrix whose rows describe an endomorphism in one basis has the same
two determinant polynomials as its matrix in any chosen basis. -/
theorem det_eq_of_cotangentRows (b c : Module.Basis (Fin d) k V) (T : V →ₗ[k] V)
    (A : Matrix (Fin d) (Fin d) k) (hA : ∀ i, T (b i) = ∑ j, A i j • b j) :
    (1 - A).det = (1 - LinearMap.toMatrix c c T).det ∧
      (1 + (Polynomial.X : Polynomial k) • A.map Polynomial.C).det =
        (1 + (Polynomial.X : Polynomial k) • (LinearMap.toMatrix c c T).map Polynomial.C).det := by
  let B := LinearMap.toMatrix b b T
  let C := LinearMap.toMatrix c c T
  have he : A = Bᵀ := by
    ext i j
    change A i j = LinearMap.toMatrix b b T j i
    rw [LinearMap.toMatrix_apply, hA, map_sum]
    simp only [Finsupp.finsetSum_apply, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hl
      simp [Finsupp.single_eq_of_ne hl.symm]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  let P := LinearMap.toMatrix c b (LinearMap.id : V →ₗ[k] V)
  let Q := LinearMap.toMatrix b c (LinearMap.id : V →ₗ[k] V)
  have hp : P * Q = 1 := by
    change LinearMap.toMatrix c b _ * LinearMap.toMatrix b c _ = _
    rw [← LinearMap.toMatrix_comp b c b, LinearMap.id_comp, LinearMap.toMatrix_id]
  have hb : B = P * C * Q := by
    change LinearMap.toMatrix b b T = LinearMap.toMatrix c b _ *
      LinearMap.toMatrix c c T * LinearMap.toMatrix b c _
    rw [← LinearMap.toMatrix_comp c c b, ← LinearMap.toMatrix_comp b c b,
      LinearMap.id_comp, LinearMap.comp_id]
  obtain ⟨h₁, h₂⟩ := det_similarity C B P Q hb hp
  rw [he]
  constructor
  · rw [show 1 - Bᵀ = (1 - B)ᵀ by simp, Matrix.det_transpose]
    exact h₁
  · rw [show 1 + (Polynomial.X : Polynomial k) • Bᵀ.map Polynomial.C =
      (1 + (Polynomial.X : Polynomial k) • B.map Polynomial.C)ᵀ by
      ext i j
      simp [Matrix.transpose_apply, Matrix.one_apply, eq_comm]]
    exact (Matrix.det_transpose _).trans h₂

end GlobalTheory.SchemeCohomology
