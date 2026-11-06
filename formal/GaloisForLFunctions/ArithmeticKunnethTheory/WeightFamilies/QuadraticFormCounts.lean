import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.DiagonalQuadricCounts
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Quadratic fibre counts and discriminants

Diagonalization transports the exact affine counts to every nonsingular
quadratic form. The determinant changes by a nonzero square, so its quadratic
character is preserved. Symmetric matrices give the corresponding concrete
coordinate formulas.
-/

open Finset Matrix QuadraticMap
open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The cardinality of an actual fibre of a quadratic form, viewed as an integer. -/
def quadraticFormCount {n : ℕ} (Q : QuadraticForm F (Fin n → F)) (t : F) : ℤ :=
  ((univ.filter (fun x => Q x = t)).card : ℤ)

/-- Linear isometries preserve every affine fibre count. -/
theorem quadraticFormCount_isometry {m n : ℕ}
    {Q : QuadraticForm F (Fin m → F)} {P : QuadraticForm F (Fin n → F)}
    (e : Q.IsometryEquiv P) (t : F) : quadraticFormCount Q t = quadraticFormCount P t := by
  have he := e.toEquiv.subtypeEquiv (p := fun x => Q x = t) (q := fun y => P y = t)
    (fun x => by rw [e.map_app])
  unfold quadraticFormCount
  rw [← Fintype.card_subtype, ← Fintype.card_subtype, Fintype.card_congr he]

theorem quadraticFormCount_weightedSumSquares {n : ℕ} (w : Fin n → Fˣ) (t : F) :
    quadraticFormCount (weightedSumSquares F w) t =
      diagonalQuadraticCount (fun i => (w i : F)) t := by
  unfold quadraticFormCount diagonalQuadraticCount
  congr 2
  ext x
  simp only [mem_filter, mem_univ, true_and, weightedSumSquares_apply,
    Units.smul_def, smul_eq_mul, diagonalQuadraticValue, pow_two]

section MatrixRepresentation

variable [Invertible (2 : F)] {n : ℕ}

/-- The associated matrix of the quadratic form of a symmetric matrix is that matrix. -/
theorem symmetricMatrix_quadratic_toMatrix (M : Matrix (Fin n) (Fin n) F)
    (hM : M.IsSymm) : M.toQuadraticForm'.toMatrix' = M := by
  have hs (x y : Fin n → F) :
      Matrix.toLinearMap₂' F M x y = Matrix.toLinearMap₂' F M y x := by
    simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    have hij : M j i = M i j := congrFun (congrFun hM i) j
    rw [hij]
    ring
  unfold QuadraticForm.toMatrix' Matrix.toQuadraticForm'
  rw [associated_left_inverse F hs]
  exact (LinearMap.toMatrix₂' F).apply_symm_apply M

/-- A weighted sum of squares has the diagonal matrix of its coefficients. -/
theorem weightedSumSquares_toMatrix (w : Fin n → Fˣ) :
    (weightedSumSquares F w).toMatrix' = diagonal (fun i => (w i : F)) := by
  have he : weightedSumSquares F w = (diagonal (fun i => (w i : F))).toQuadraticForm' := by
    ext x
    simp only [weightedSumSquares_apply, Units.smul_def, smul_eq_mul,
      Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply', dotProduct, mulVec_diagonal]
    apply sum_congr rfl
    intro i _
    ring
  rw [he, symmetricMatrix_quadratic_toMatrix _ (isSymm_diagonal _)]

/-- Nonsingularity produces an actual diagonal model with the same discriminant character. -/
theorem quadraticFormCount_diagonal_model (Q : QuadraticForm F (Fin n → F))
    (hQ : Q.discr' ≠ 0) :
    ∃ w : Fin n → Fˣ,
      (∀ t, quadraticFormCount Q t = diagonalQuadraticCount (fun i => (w i : F)) t) ∧
      quadraticChar F Q.discr' = quadraticChar F (∏ i, (w i : F)) := by
  have hsep : Q.associated.SeparatingLeft :=
    LinearMap.separatingLeft_toMatrix₂'_iff.mp (Matrix.separatingLeft_iff_det_ne_zero.mpr hQ)
  have hex : ∃ w : Fin n → Fˣ, Q.Equivalent (weightedSumSquares F w) := by
    simpa only [Module.finrank_fin_fun] using
      QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q hsep
  obtain ⟨w, ⟨e⟩⟩ := hex
  refine ⟨w, fun t => (quadraticFormCount_isometry e t).trans
    (quadraticFormCount_weightedSumSquares w t), ?_⟩
  have he : Q = (weightedSumSquares F w).comp e.toLinearEquiv.toLinearMap := by
    ext x
    exact (e.map_app x).symm
  have hd : Q.discr' =
      (LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det ^ 2 * ∏ i, (w i : F) := by
    conv_lhs => rw [he, QuadraticForm.discr'_comp]
    rw [QuadraticForm.discr', weightedSumSquares_toMatrix, det_diagonal, pow_two]
  have hn : (LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det ≠ 0 := by
    intro hz
    apply hQ
    rw [hd, hz, zero_pow two_ne_zero, zero_mul]
  rw [hd, map_mul, quadraticChar_sq_one' hn, one_mul]

/-- The discriminant controls every fibre in odd dimension. -/
theorem quadraticFormCount_odd (hF : ringChar F ≠ 2) (k : ℕ)
    (Q : QuadraticForm F (Fin (2 * k + 1) → F)) (hQ : Q.discr' ≠ 0) (t : F) :
    quadraticFormCount Q t = (Fintype.card F : ℤ) ^ (2 * k) +
      quadraticChar F ((-1) ^ k * Q.discr' * t) * (Fintype.card F : ℤ) ^ k := by
  obtain ⟨w, hc, hd⟩ := quadraticFormCount_diagonal_model Q hQ
  rw [hc, diagonalQuadraticCount_odd hF k _ (fun i => (w i).ne_zero)]
  simp only [map_mul, hd]

/-- The discriminant controls every fibre in positive even dimension. -/
theorem quadraticFormCount_even (hF : ringChar F ≠ 2) (k : ℕ)
    (Q : QuadraticForm F (Fin (2 * k + 2) → F)) (hQ : Q.discr' ≠ 0) (t : F) :
    quadraticFormCount Q t = (Fintype.card F : ℤ) ^ (2 * k + 1) +
      quadraticChar F ((-1) ^ (k + 1) * Q.discr') * quadraticZeroCorrection t *
        (Fintype.card F : ℤ) ^ k := by
  obtain ⟨w, hc, hd⟩ := quadraticFormCount_diagonal_model Q hQ
  rw [hc, diagonalQuadraticCount_even hF k _ (fun i => (w i).ne_zero)]
  simp only [map_mul, hd]

end MatrixRepresentation

/-- Exact affine fibre count of a nonsingular symmetric matrix in odd dimension. -/
theorem symmetricMatrix_quadraticCount_odd (hF : ringChar F ≠ 2) (k : ℕ)
    (M : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) F) (hM : M.IsSymm)
    (hdet : M.det ≠ 0) (t : F) :
    quadraticFormCount M.toQuadraticForm' t = (Fintype.card F : ℤ) ^ (2 * k) +
      quadraticChar F ((-1) ^ k * M.det * t) * (Fintype.card F : ℤ) ^ k := by
  letI := invertibleOfNonzero (Ring.two_ne_zero hF)
  have hd : M.toQuadraticForm'.discr' = M.det := by
    rw [QuadraticForm.discr', symmetricMatrix_quadratic_toMatrix M hM]
  simpa only [hd] using quadraticFormCount_odd hF k M.toQuadraticForm' (hd ▸ hdet) t

/-- Exact affine fibre count of a nonsingular symmetric matrix in positive even dimension. -/
theorem symmetricMatrix_quadraticCount_even (hF : ringChar F ≠ 2) (k : ℕ)
    (M : Matrix (Fin (2 * k + 2)) (Fin (2 * k + 2)) F) (hM : M.IsSymm)
    (hdet : M.det ≠ 0) (t : F) :
    quadraticFormCount M.toQuadraticForm' t = (Fintype.card F : ℤ) ^ (2 * k + 1) +
      quadraticChar F ((-1) ^ (k + 1) * M.det) * quadraticZeroCorrection t *
        (Fintype.card F : ℤ) ^ k := by
  letI := invertibleOfNonzero (Ring.two_ne_zero hF)
  have hd : M.toQuadraticForm'.discr' = M.det := by
    rw [QuadraticForm.discr', symmetricMatrix_quadratic_toMatrix M hM]
  simpa only [hd] using quadraticFormCount_even hF k M.toQuadraticForm' (hd ▸ hdet) t

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
