import GaloisForLFunctions.HTGeometry.GomesSpecialOrthogonalCommutant

/-!
# Planar metric and area reconstruction

The planar rotation commutant is the real matrix algebra of complex scalars. Its invariant
bilinear forms retain both the Euclidean metric and the oriented area form. Reflection
conjugation is still outer. This closes the exceptional two-dimensional boundary in
Gomes, arXiv:2607.24901, Proposition 3.
https://arxiv.org/abs/2607.24901
-/

open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The real matrix of multiplication by the complex scalar a + bi. -/
def gomesPlanarComplexMatrix (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a,-b;b,a]

/-- Real planar complex matrices multiply according to complex multiplication. -/
theorem gomesPlanarComplexMatrix_mul (a b c d : ℝ) :
    gomesPlanarComplexMatrix a b * gomesPlanarComplexMatrix c d =
      gomesPlanarComplexMatrix (a*c-b*d) (a*d+b*c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gomesPlanarComplexMatrix,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

/-- Transposition becomes complex conjugation in the planar real model. -/
theorem gomesPlanarComplexMatrix_transpose (a b : ℝ) :
    (gomesPlanarComplexMatrix a b)ᵀ = gomesPlanarComplexMatrix a (-b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gomesPlanarComplexMatrix]

/-- Commuting with a single quarter-turn reconstructs exactly the complex scalar matrices. -/
theorem planar_quarterTurn_commutant (C : Matrix (Fin 2) (Fin 2) ℝ) :
    C * gomesPlanarComplexMatrix 0 1 = gomesPlanarComplexMatrix 0 1 * C ↔
      C = gomesPlanarComplexMatrix (C 0 0) (C 1 0) := by
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h10 := congrFun (congrFun h 1) 0
    simp [gomesPlanarComplexMatrix,Matrix.mul_apply,Fin.sum_univ_two] at h00 h10
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gomesPlanarComplexMatrix,h00,h10]
  · intro h
    rw [h,gomesPlanarComplexMatrix_mul,gomesPlanarComplexMatrix_mul]
    simp

/-- Every special orthogonal planar matrix is multiplication by a unit complex number. -/
theorem planar_specialOrthogonal_complex_form (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    R.val = gomesPlanarComplexMatrix (R.val 0 0) (R.val 1 0) := by
  have h := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp R.property
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gomesPlanarComplexMatrix,h.1,h.2.1]

/-- Unlike dimensions at least three, the planar rotation commutant retains the complex structure. -/
theorem planar_specialOrthogonal_commutant (C : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ R : Matrix.specialOrthogonalGroup (Fin 2) ℝ, C * R.val = R.val * C) ↔
      C = gomesPlanarComplexMatrix (C 0 0) (C 1 0) := by
  constructor
  · intro h
    apply (planar_quarterTurn_commutant C).mp
    have hJ : gomesPlanarComplexMatrix 0 1 ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
      rw [Matrix.mem_specialOrthogonalGroup_fin_two_iff]
      simp [gomesPlanarComplexMatrix]
    exact h ⟨gomesPlanarComplexMatrix 0 1,hJ⟩
  · intro h R
    conv_lhs => rw [h,planar_specialOrthogonal_complex_form R]
    conv_rhs => rw [h,planar_specialOrthogonal_complex_form R]
    rw [gomesPlanarComplexMatrix_mul,gomesPlanarComplexMatrix_mul]
    congr 1 <;> ring

/-- The two-dimensional invariant bilinear forms are the span of the metric and oriented area. -/
theorem planar_specialOrthogonal_invariant_bilinear (C : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ R : Matrix.specialOrthogonalGroup (Fin 2) ℝ, R.valᵀ * C * R.val = C) ↔
      C = gomesPlanarComplexMatrix (C 0 0) (C 1 0) := by
  rw [← planar_specialOrthogonal_commutant]
  constructor
  · intro h R
    have hRR := (Matrix.mem_orthogonalGroup_iff _ _).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp R.property).1
    calc
      C * R.val = (R.val * R.valᵀ) * C * R.val := by rw [hRR]; simp
      _ = R.val * (R.valᵀ * C * R.val) := by simp only [mul_assoc]
      _ = R.val * C := by rw [h R]
  · intro h R
    have hRR := (Matrix.mem_orthogonalGroup_iff' _ _).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp R.property).1
    rw [mul_assoc,h R,← mul_assoc,hRR,one_mul]

/-- Orientation reversal exchanges a planar rotation with its inverse matrix. -/
theorem planar_reflection_conjugation (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    gomesAxisReflection (0 : Fin 2) * R.val * gomesAxisReflection (0 : Fin 2) = R.valᵀ := by
  rw [planar_specialOrthogonal_complex_form R]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gomesAxisReflection,gomesPlanarComplexMatrix,Matrix.diagonal_mul,Matrix.mul_diagonal]

/-- Reflection conjugation remains outer in dimension two despite the larger commutant. -/
theorem planar_specialOrthogonal_reflection_not_inner :
    ¬ ∃ S : Matrix.specialOrthogonalGroup (Fin 2) ℝ,
      ∀ R : Matrix.specialOrthogonalGroup (Fin 2) ℝ,
        gomesAxisReflection (0 : Fin 2) * R.val * gomesAxisReflection (0 : Fin 2) =
          S.val * R.val * S.valᵀ := by
  rintro ⟨S,h⟩
  have hJ : gomesPlanarComplexMatrix 0 1 ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
    rw [Matrix.mem_specialOrthogonalGroup_fin_two_iff]
    simp [gomesPlanarComplexMatrix]
  let J : Matrix.specialOrthogonalGroup (Fin 2) ℝ := ⟨gomesPlanarComplexMatrix 0 1,hJ⟩
  have hc := (planar_specialOrthogonal_commutant S.val).mpr
    (planar_specialOrthogonal_complex_form S) J
  have hs := (Matrix.mem_orthogonalGroup_iff _ _).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp S.property).1
  have hh := h J
  rw [planar_reflection_conjugation,hc,mul_assoc,hs,mul_one] at hh
  have he := congrFun (congrFun hh 0) 1
  change (1 : ℝ) = -1 at he
  linarith

end GaloisForLFunctions.HTGeometry
