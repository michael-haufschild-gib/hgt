import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Real special-orthogonal commutants

Double coordinate reflections remove off-diagonal entries; quarter-turns identify the diagonal.
This classifies every invariant bilinear matrix, including nonsymmetric and degenerate inputs.

Mechanically extracted from the symmetry-first reconstruction problem in
Gomes, arXiv:2607.24901, Proposition 3 and its normalizer discussion.
https://arxiv.org/abs/2607.24901
-/

open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Reflection reversing one coordinate axis. -/
def gomesAxisReflection {ι : Type*} [DecidableEq ι] (i : ι) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun j => if j=i then -1 else 1)

/-- Each axis reflection is an involution. -/
theorem gomesAxisReflection_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    gomesAxisReflection i * gomesAxisReflection i = 1 := by
  rw [gomesAxisReflection,Matrix.diagonal_mul_diagonal]
  change Matrix.diagonal (fun j => (if j = i then (-1 : ℝ) else 1) *
    (if j = i then (-1 : ℝ) else 1)) = Matrix.diagonal (fun _ => 1)
  congr 1
  funext j
  by_cases hj : j = i <;> simp [hj]

/-- Axis reflection is orthogonal in every finite dimension. -/
theorem gomesAxisReflection_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    gomesAxisReflection i ∈ Matrix.orthogonalGroup ι ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  have ht : (gomesAxisReflection i)ᵀ = gomesAxisReflection i := by
    simp [gomesAxisReflection]
  rw [ht]
  exact gomesAxisReflection_sq i

/-- Axis reflection reverses orientation. -/
theorem gomesAxisReflection_det {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    (gomesAxisReflection i).det = -1 := by
  simp [gomesAxisReflection,Matrix.det_diagonal]

/-- Flipping two axes always lies in the special orthogonal group, including a repeated axis. -/
theorem gomes_double_reflection_specialOrthogonal {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    gomesAxisReflection i * gomesAxisReflection j ∈ Matrix.specialOrthogonalGroup ι ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · exact (Matrix.orthogonalGroup ι ℝ).mul_mem
      (gomesAxisReflection_orthogonal i) (gomesAxisReflection_orthogonal j)
  · rw [Matrix.det_mul,gomesAxisReflection_det,gomesAxisReflection_det]
    ring

/-- A quarter-turn on distinct coordinate axes; repeated axes give the identity. -/
def gomesPlaneRotation {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) : Matrix ι ι ℝ :=
  if i=j then 1 else gomesAxisReflection i * (Equiv.swap i j).permMatrix ℝ

/-- Every coordinate-plane quarter-turn is special orthogonal. -/
theorem gomesPlaneRotation_specialOrthogonal {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    gomesPlaneRotation i j ∈ Matrix.specialOrthogonalGroup ι ℝ := by
  by_cases hij : i=j
  · simp [gomesPlaneRotation,hij]
  · have hp : (Equiv.swap i j).permMatrix ℝ ∈ Matrix.orthogonalGroup ι ℝ := by
      rw [Matrix.mem_orthogonalGroup_iff',Matrix.transpose_permMatrix,← Matrix.permMatrix_mul]
      simp
    rw [gomesPlaneRotation,if_neg hij,Matrix.mem_specialOrthogonalGroup_iff]
    constructor
    · exact (Matrix.orthogonalGroup ι ℝ).mul_mem (gomesAxisReflection_orthogonal i) hp
    · rw [Matrix.det_mul,gomesAxisReflection_det,Matrix.det_permutation,Equiv.Perm.sign_swap hij]
      simp

/-- The selected off-diagonal quarter-turn entry is nonzero whenever the axes differ. -/
theorem gomesPlaneRotation_axis_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    gomesPlaneRotation i j i j = if i=j then 1 else -1 := by
  by_cases hij : i=j
  · subst j
    simp [gomesPlaneRotation]
  · simp [gomesPlaneRotation,hij,gomesAxisReflection,Matrix.diagonal_mul,
      Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply]

/-- The entire real matrix commutant of SO(n+3) consists of scalar matrices. -/
theorem specialOrthogonal_matrix_commutant (n : ℕ)
    (C : Matrix (Fin (n+3)) (Fin (n+3)) ℝ) :
    (∀ R : Matrix.specialOrthogonalGroup (Fin (n+3)) ℝ,
      C * (R : Matrix (Fin (n+3)) (Fin (n+3)) ℝ) =
        (R : Matrix (Fin (n+3)) (Fin (n+3)) ℝ) * C) ↔
      C = C 0 0 • (1 : Matrix (Fin (n+3)) (Fin (n+3)) ℝ) := by
  constructor
  · intro h
    have hoff (i j : Fin (n+3)) : i ≠ j → C i j = 0 := by
      intro hij
      obtain ⟨k,hki,hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
      have hh := h ⟨gomesAxisReflection i * gomesAxisReflection k,
        gomes_double_reflection_specialOrthogonal i k⟩
      have he := congrFun (congrFun hh i) j
      simp [gomesAxisReflection,Matrix.diagonal_mul_diagonal,Matrix.mul_diagonal,
        Matrix.diagonal_mul,hij.symm,hki.symm,hkj.symm] at he
      linarith
    have hd : C = Matrix.diagonal (fun i => C i i) := by
      ext i j
      by_cases hij : i=j
      · subst j
        simp
      · simp [Matrix.diagonal,hij,hoff i j hij]
    have heq (i j : Fin (n+3)) : C i i = C j j := by
      by_cases hij : i=j
      · simp [hij]
      · have hh := h ⟨gomesPlaneRotation i j,gomesPlaneRotation_specialOrthogonal i j⟩
        have he := congrFun (congrFun hh i) j
        conv_lhs at he => rw [hd,Matrix.diagonal_mul]
        conv_rhs at he => rw [hd,Matrix.mul_diagonal]
        change C i i * gomesPlaneRotation i j i j =
          gomesPlaneRotation i j i j * C j j at he
        rw [gomesPlaneRotation_axis_entry,if_neg hij] at he
        linarith
    ext i j
    by_cases hij : i=j
    · subst j
      simpa using heq i 0
    · simp [hij,hoff i j hij]
  · intro h R
    rw [h]
    simp

/-- Every bilinear form invariant under all special orthogonal matrices is scalar Euclidean,
without imposing symmetry or nondegeneracy on the form in advance. -/
theorem specialOrthogonal_invariant_bilinear_matrix (n : ℕ)
    (C : Matrix (Fin (n+3)) (Fin (n+3)) ℝ) :
    (∀ R : Matrix.specialOrthogonalGroup (Fin (n+3)) ℝ, R.valᵀ * C * R.val = C) ↔
      C = C 0 0 • (1 : Matrix (Fin (n+3)) (Fin (n+3)) ℝ) := by
  rw [← specialOrthogonal_matrix_commutant]
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
    calc
      R.valᵀ * C * R.val = R.valᵀ * (C * R.val) := by rw [mul_assoc]
      _ = R.valᵀ * (R.val * C) := by rw [h R]
      _ = C := by rw [← mul_assoc,hRR,one_mul]


end GaloisForLFunctions.HTGeometry
