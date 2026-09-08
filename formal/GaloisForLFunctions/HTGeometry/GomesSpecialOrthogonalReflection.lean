import GaloisForLFunctions.HTGeometry.GomesSpecialOrthogonalCommutant

/-!
# Reflection conjugation and its exact parity boundary

Orthogonal conjugations agree exactly up to sign. Reflection conjugation is outer in every
even dimension at least four and is implemented by a special orthogonal map in odd dimension.

Mechanically extracted from the symmetry-first reconstruction problem in
Gomes, arXiv:2607.24901, Proposition 3 and its normalizer discussion.
https://arxiv.org/abs/2607.24901
-/

open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Two orthogonal maps induce the same conjugation of SO(n+3) exactly when they differ by sign. -/
theorem orthogonal_conjugation_eq_iff_sign (n : ℕ)
    (Q S : Matrix.orthogonalGroup (Fin (n+3)) ℝ) :
    (∀ R : Matrix.specialOrthogonalGroup (Fin (n+3)) ℝ,
      Q.val * R.val * Q.valᵀ = S.val * R.val * S.valᵀ) ↔
      Q.val = S.val ∨ Q.val = -S.val := by
  have hQ := (Matrix.mem_orthogonalGroup_iff _ _).mp Q.property
  have hQt := (Matrix.mem_orthogonalGroup_iff' _ _).mp Q.property
  have hS := (Matrix.mem_orthogonalGroup_iff _ _).mp S.property
  have hSt := (Matrix.mem_orthogonalGroup_iff' _ _).mp S.property
  constructor
  · intro h
    let C := S.valᵀ * Q.val
    have hcomm : ∀ R : Matrix.specialOrthogonalGroup (Fin (n+3)) ℝ,
        C * R.val = R.val * C := by
      intro R
      calc
        C * R.val = S.valᵀ * (Q.val * R.val * Q.valᵀ) * Q.val := by
          simp only [C,mul_assoc,hQt,mul_one]
        _ = S.valᵀ * (S.val * R.val * S.valᵀ) * Q.val := by rw [h R]
        _ = R.val * C := by simp only [C,← mul_assoc,hSt,one_mul]
    have hc := (specialOrthogonal_matrix_commutant n C).mp hcomm
    have hCC : Cᵀ * C = 1 := by
      calc
        Cᵀ * C = Q.valᵀ * (S.val * S.valᵀ) * Q.val := by
          simp only [C,Matrix.transpose_mul,Matrix.transpose_transpose,mul_assoc]
        _ = 1 := by rw [hS]; simpa using hQt
    have hsq : C 0 0 * C 0 0 = 1 := by
      conv_lhs at hCC => rw [hc]
      simp only [Matrix.transpose_smul,Matrix.transpose_one,Matrix.smul_mul,
        Matrix.mul_smul,Matrix.one_mul,smul_smul] at hCC
      have he := congrArg (fun M : Matrix (Fin (n+3)) (Fin (n+3)) ℝ => M 0 0) hCC
      simpa using he
    have hsign : C 0 0 = 1 ∨ C 0 0 = -1 := by
      have hp : (C 0 0 - 1) * (C 0 0 + 1) = 0 := by nlinarith [hsq]
      rcases mul_eq_zero.mp hp with hp | hp
      · left; linarith
      · right; linarith
    have hQC : Q.val = C 0 0 • S.val := by
      calc
        Q.val = S.val * C := by simp only [C,← mul_assoc,hS,one_mul]
        _ = C 0 0 • S.val := by rw [hc]; simp
    rcases hsign with hp | hm
    · left; simpa only [hp,one_smul] using hQC
    · right; simpa only [hm,neg_one_smul] using hQC
  · rintro (h | h) R
    · rw [h]
    · rw [h]
      simp

/-- A coordinate reflection induces an automorphism not implemented by any special orthogonal
matrix in every even dimension at least four. -/
theorem even_specialOrthogonal_reflection_not_inner (m : ℕ) :
    ¬ ∃ S : Matrix.specialOrthogonalGroup (Fin (2*m+4)) ℝ,
      ∀ R : Matrix.specialOrthogonalGroup (Fin (2*m+4)) ℝ,
        gomesAxisReflection (0 : Fin (2*m+4)) * R.val *
          gomesAxisReflection (0 : Fin (2*m+4)) = S.val * R.val * S.valᵀ := by
  rintro ⟨S,h⟩
  let Q : Matrix.orthogonalGroup (Fin ((2*m+1)+3)) ℝ :=
    ⟨gomesAxisReflection 0,gomesAxisReflection_orthogonal 0⟩
  let T : Matrix.orthogonalGroup (Fin ((2*m+1)+3)) ℝ :=
    ⟨S.val,(Matrix.mem_specialOrthogonalGroup_iff.mp S.property).1⟩
  have he : Q.val = T.val ∨ Q.val = -T.val := by
    apply (orthogonal_conjugation_eq_iff_sign (2*m+1) Q T).mp
    simpa [Q,T,gomesAxisReflection] using h
  have hdet := (Matrix.mem_specialOrthogonalGroup_iff.mp S.property).2
  have hQdet : Q.val.det = -1 := gomesAxisReflection_det 0
  rcases he with he | he
  · have hd := congrArg Matrix.det he
    change Q.val.det = S.val.det at hd
    rw [hdet,hQdet] at hd
    linarith
  · have hd := congrArg Matrix.det he
    change Q.val.det = (-S.val).det at hd
    rw [Matrix.det_neg,hdet,hQdet,Fintype.card_fin] at hd
    have hev : Even ((2*m+1)+3) := ⟨m+2,by omega⟩
    rw [hev.neg_one_pow,one_mul] at hd
    linarith

/-- The parity boundary is exact: in every odd dimension at least three, the negative reflection
is special orthogonal and implements reflection conjugation. -/
theorem odd_specialOrthogonal_reflection_inner (m : ℕ) :
    ∃ S : Matrix.specialOrthogonalGroup (Fin (2*m+3)) ℝ,
      ∀ R : Matrix.specialOrthogonalGroup (Fin (2*m+3)) ℝ,
        gomesAxisReflection (0 : Fin (2*m+3)) * R.val *
          gomesAxisReflection (0 : Fin (2*m+3)) = S.val * R.val * S.valᵀ := by
  let D := gomesAxisReflection (0 : Fin (2*m+3))
  have ht : Dᵀ = D := by simp [D,gomesAxisReflection]
  have hneg : -D ∈ Matrix.specialOrthogonalGroup (Fin (2*m+3)) ℝ := by
    rw [Matrix.mem_specialOrthogonalGroup_iff]
    constructor
    · rw [Matrix.mem_orthogonalGroup_iff']
      simp only [Matrix.transpose_neg,neg_mul_neg,ht]
      exact gomesAxisReflection_sq 0
    · rw [Matrix.det_neg,gomesAxisReflection_det,Fintype.card_fin]
      have hod : Odd (2*m+3) := ⟨m+1,by omega⟩
      rw [hod.neg_one_pow]
      ring
  refine ⟨⟨-D,hneg⟩,?_⟩
  intro R
  change D * R.val * D = (-D) * R.val * (-D)ᵀ
  simp [ht]

end GaloisForLFunctions.HTGeometry
