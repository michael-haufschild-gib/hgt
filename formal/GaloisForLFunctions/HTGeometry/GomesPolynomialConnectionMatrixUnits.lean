import GaloisForLFunctions.HTGeometry.GomesPolynomialConnectionCenter

/-!
# Elementary chain transfers and the commutativity boundary

Matrix units give actual connection symmetries transferring one orbit chain to another.
Their multiplication laws expose projections, nilpotent transfers, and noncommuting
symmetries as soon as coefficient degree exceeds one.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The elementary symmetry transferring the j-th connection chain to the i-th chain. -/
def gomesPolynomialConnectionMatrixUnit (A : GomesNonconstantPolynomialCoefficient)
    (i j : Fin A.val.natDegree) : GomesPolynomialConnectionCommutant A.val :=
  (gomesPolynomialConnectionCommutantMatrixEquiv A).symm (Matrix.single i j 1)

/-- The elementary chain transfer has exactly its prescribed elementary matrix. -/
theorem gomesPolynomialConnectionMatrixUnit_matrix (A : GomesNonconstantPolynomialCoefficient)
    (i j : Fin A.val.natDegree) :
    gomesPolynomialConnectionCommutantMatrixEquiv A (gomesPolynomialConnectionMatrixUnit A i j) =
      Matrix.single i j 1 :=
  (gomesPolynomialConnectionCommutantMatrixEquiv A).apply_symm_apply _

/-- Matching chain transfers compose to the direct transfer. -/
theorem gomesPolynomialConnectionMatrixUnit_mul_same (A : GomesNonconstantPolynomialCoefficient)
    (i j k : Fin A.val.natDegree) :
    gomesPolynomialConnectionMatrixUnit A i j * gomesPolynomialConnectionMatrixUnit A j k =
      gomesPolynomialConnectionMatrixUnit A i k := by
  apply (gomesPolynomialConnectionCommutantMatrixEquiv A).injective
  simp only [map_mul, gomesPolynomialConnectionMatrixUnit_matrix,
    Matrix.single_mul_single_same, one_mul]

/-- All elementary chain transfers satisfy the full matrix-unit multiplication law. -/
theorem gomesPolynomialConnectionMatrixUnit_mul (A : GomesNonconstantPolynomialCoefficient)
    (i j k l : Fin A.val.natDegree) :
    gomesPolynomialConnectionMatrixUnit A i j * gomesPolynomialConnectionMatrixUnit A k l =
      if j = k then gomesPolynomialConnectionMatrixUnit A i l else 0 := by
  by_cases h : j = k
  · subst k
    simp only [ite_true, gomesPolynomialConnectionMatrixUnit_mul_same]
  · rw [if_neg h]
    apply (gomesPolynomialConnectionCommutantMatrixEquiv A).injective
    simp only [map_mul, map_zero, gomesPolynomialConnectionMatrixUnit_matrix,
      Matrix.single_mul_single_of_ne _ _ _ _ h]

/-- Each elementary chain transfer is nonzero. -/
theorem gomesPolynomialConnectionMatrixUnit_ne_zero (A : GomesNonconstantPolynomialCoefficient)
    (i j : Fin A.val.natDegree) : gomesPolynomialConnectionMatrixUnit A i j ≠ 0 := by
  intro h
  have hm := congrArg (gomesPolynomialConnectionCommutantMatrixEquiv A) h
  rw [gomesPolynomialConnectionMatrixUnit_matrix, map_zero] at hm
  have hc := congrArg (fun M : Matrix (Fin A.val.natDegree) (Fin A.val.natDegree) ℝ[X] =>
    M i j) hm
  exact one_ne_zero (by simpa only [Matrix.single_apply_same, Matrix.zero_apply] using hc)

/-- Projecting onto one connection chain is idempotent. -/
theorem gomesPolynomialConnectionMatrixUnit_idempotent
    (A : GomesNonconstantPolynomialCoefficient) (i : Fin A.val.natDegree) :
    gomesPolynomialConnectionMatrixUnit A i i * gomesPolynomialConnectionMatrixUnit A i i =
      gomesPolynomialConnectionMatrixUnit A i i :=
  gomesPolynomialConnectionMatrixUnit_mul_same A i i i

/-- Precisely the transfers between different chains square to zero. -/
theorem gomesPolynomialConnectionMatrixUnit_square_zero_iff
    (A : GomesNonconstantPolynomialCoefficient) (i j : Fin A.val.natDegree) :
    gomesPolynomialConnectionMatrixUnit A i j * gomesPolynomialConnectionMatrixUnit A i j = 0 ↔
      i ≠ j := by
  constructor
  · intro h hij
    subst j
    rw [gomesPolynomialConnectionMatrixUnit_idempotent] at h
    exact gomesPolynomialConnectionMatrixUnit_ne_zero A i i h
  · intro h
    rw [gomesPolynomialConnectionMatrixUnit_mul, if_neg (Ne.symm h)]

/-- Opposite elementary chain transfers commute exactly when they are the same projection. -/
theorem gomesPolynomialConnectionMatrixUnit_opposite_commute_iff
    (A : GomesNonconstantPolynomialCoefficient) (i j : Fin A.val.natDegree) :
    gomesPolynomialConnectionMatrixUnit A i j * gomesPolynomialConnectionMatrixUnit A j i =
      gomesPolynomialConnectionMatrixUnit A j i * gomesPolynomialConnectionMatrixUnit A i j ↔
        i = j := by
  constructor
  · intro h
    by_contra hij
    rw [gomesPolynomialConnectionMatrixUnit_mul_same,
      gomesPolynomialConnectionMatrixUnit_mul_same] at h
    have hm := congrArg (gomesPolynomialConnectionCommutantMatrixEquiv A) h
    rw [gomesPolynomialConnectionMatrixUnit_matrix,
      gomesPolynomialConnectionMatrixUnit_matrix] at hm
    have hc := congrArg (fun M : Matrix (Fin A.val.natDegree) (Fin A.val.natDegree) ℝ[X] =>
      M i i) hm
    exact one_ne_zero (by simpa only [Matrix.single_apply_same,
      Matrix.single_apply_of_row_ne (Ne.symm hij)] using hc)
  · rintro rfl
    rfl

/-- In degree one every symmetry is a unique polynomial in the connection. -/
theorem gomesPolynomialConnection_degree_one_symmetries
    (A : {A : GomesNonconstantPolynomialCoefficient // A.val.natDegree = 1})
    (E : GomesPolynomialConnectionCommutant A.val.val) :
    ∃! P : ℝ[X], E = gomesPolynomialConnectionPolynomialSymmetry A.val.val P := by
  let z : Fin A.val.val.natDegree := ⟨0, gomesNonconstantPolynomialCoefficient_degree_pos A.val⟩
  have hi (i : Fin A.val.val.natDegree) : i = z := by
    apply Fin.ext
    exact Nat.lt_one_iff.mp (by simpa only [A.property] using i.2)
  let P := gomesPolynomialConnectionCommutantMatrixEquiv A.val E z z
  have hP : E = gomesPolynomialConnectionPolynomialSymmetry A.val.val P := by
    apply (gomesPolynomialConnectionCommutantMatrixEquiv A.val).injective
    rw [gomesPolynomialConnectionPolynomialSymmetry_matrix]
    apply Matrix.ext
    intro i j
    rw [hi i, hi j, Matrix.diagonal_apply_eq]
  refine ⟨P, hP, ?_⟩
  intro Q hQ
  exact gomesPolynomialConnectionPolynomialSymmetry_injective A.val (hQ.symm.trans hP)

/-- The full connection symmetry algebra is commutative exactly in coefficient degree one. -/
theorem gomesPolynomialConnectionCommutant_commutative_iff
    (A : GomesNonconstantPolynomialCoefficient) :
    (∀ E F : GomesPolynomialConnectionCommutant A.val, E * F = F * E) ↔
      A.val.natDegree = 1 := by
  constructor
  · intro h
    by_contra hm
    have hgreater : 1 < A.val.natDegree :=
      lt_of_le_of_ne (gomesNonconstantPolynomialCoefficient_degree_pos A) (Ne.symm hm)
    let i : Fin A.val.natDegree := ⟨0, gomesNonconstantPolynomialCoefficient_degree_pos A⟩
    let j : Fin A.val.natDegree := ⟨1, hgreater⟩
    have hij := (gomesPolynomialConnectionMatrixUnit_opposite_commute_iff A i j).mp
      (h (gomesPolynomialConnectionMatrixUnit A i j) (gomesPolynomialConnectionMatrixUnit A j i))
    exact Nat.zero_ne_one (congrArg Fin.val hij)
  · intro hm E F
    obtain ⟨P, hP, _⟩ := gomesPolynomialConnection_degree_one_symmetries ⟨A, hm⟩ E
    rw [hP]
    exact gomesPolynomialConnectionPolynomialSymmetry_central A P F

/-- Polynomial evolution exhausts all symmetries exactly in degree one. -/
theorem gomesPolynomialConnectionPolynomialSymmetry_surjective_iff
    (A : GomesNonconstantPolynomialCoefficient) :
    Function.Surjective (gomesPolynomialConnectionPolynomialSymmetry A.val) ↔
      A.val.natDegree = 1 := by
  constructor
  · intro h
    apply (gomesPolynomialConnectionCommutant_commutative_iff A).mp
    intro E F
    obtain ⟨P, rfl⟩ := h E
    exact gomesPolynomialConnectionPolynomialSymmetry_central A P F
  · intro h E
    obtain ⟨P, hP, _⟩ := gomesPolynomialConnection_degree_one_symmetries ⟨A, h⟩ E
    exact ⟨P, hP.symm⟩

end GaloisForLFunctions.HTGeometry
