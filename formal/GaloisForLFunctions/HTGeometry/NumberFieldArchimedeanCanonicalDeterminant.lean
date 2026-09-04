import GaloisForLFunctions.HTGeometry.ComplexMatrixRealificationDeterminant
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanDeterminantProfile
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanPrimitiveMinimum

/-!
# Determinant of the canonical number-field archimedean form

The canonical real form is a fixed coordinate congruence of its real and doubled-complex local
blocks.  This file computes its determinant exactly.  Real places occur once and complex places
twice, so the variable factor is the exponential of the multiplicity-weighted local
log-determinant profile.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder Matrix NumberField BigOperators

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-- The real block-coordinate index has the canonical number-field dimension. -/
theorem card_numberFieldArchimedeanBlockIndex :
    Fintype.card (numberFieldArchimedeanBlockIndex K n) =
      n * Module.finrank ℚ K := by
  have h := LinearEquiv.finrank_eq
    (numberFieldCanonicalToArchimedeanBlockCoordinates K n)
  simpa using h.symm

/-- A fixed relabelling of archimedean block coordinates by canonical coordinates. -/
def numberFieldArchimedeanBlockIndexEquivFin :
    numberFieldArchimedeanBlockIndex K n ≃ Fin (n * Module.finrank ℚ K) :=
  Fintype.equivOfCardEq (by
    simpa using (card_numberFieldArchimedeanBlockIndex (K := K) (n := n)))

/-- Square coordinate matrix obtained by relabelling the block rows canonically. -/
def numberFieldArchimedeanSquareCoordinateMatrix :
    Matrix (Fin (n * Module.finrank ℚ K))
      (Fin (n * Module.finrank ℚ K)) ℝ :=
  Matrix.reindex numberFieldArchimedeanBlockIndexEquivFin (Equiv.refl _)
    (numberFieldArchimedeanCoordinateMatrix K n)

/-- Relabelling a rectangular congruence turns it into an ordinary square congruence. -/
theorem reindex_rectangular_real_congruence
    {m q : Type*} [Fintype m] [DecidableEq m] [Fintype q] [DecidableEq q]
    (e : m ≃ q) (P : Matrix m q ℝ) (B : Matrix m m ℝ) :
    Matrix.conjTranspose P * B * P =
      Matrix.conjTranspose (Matrix.reindex e (Equiv.refl q) P) *
        Matrix.reindex e e B * Matrix.reindex e (Equiv.refl q) P := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm]
  rw [← e.sum_comp]
  simp only [Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  rw [← e.sum_comp]
  simp

/-- The relabelled coordinate matrix is the matrix of the coordinate equivalence in a relabelled
codomain basis. -/
theorem numberFieldArchimedeanSquareCoordinateMatrix_eq_toMatrix :
    numberFieldArchimedeanSquareCoordinateMatrix (K := K) (n := n) =
      LinearMap.toMatrix
        (Pi.basisFun ℝ (Fin (n * Module.finrank ℚ K)))
        ((Pi.basisFun ℝ (numberFieldArchimedeanBlockIndex K n)).reindex
          numberFieldArchimedeanBlockIndexEquivFin)
        (numberFieldCanonicalToArchimedeanBlockCoordinates K n).toLinearMap := by
  ext i j
  rfl

/-- The fixed coordinate-volume factor is nonzero. -/
theorem numberFieldArchimedeanSquareCoordinateMatrix_det_ne_zero :
    (numberFieldArchimedeanSquareCoordinateMatrix (K := K) (n := n)).det ≠ 0 := by
  rw [numberFieldArchimedeanSquareCoordinateMatrix_eq_toMatrix]
  exact (LinearEquiv.isUnit_det
    (numberFieldCanonicalToArchimedeanBlockCoordinates K n)
    (Pi.basisFun ℝ (Fin (n * Module.finrank ℚ K)))
    ((Pi.basisFun ℝ (numberFieldArchimedeanBlockIndex K n)).reindex
      numberFieldArchimedeanBlockIndexEquivFin)).ne_zero

/-- Canonical determinant is the fixed coordinate-volume square times the block determinant. -/
theorem det_numberFieldArchimedeanCanonicalMatrix
    (A : numberFieldArchimedeanPositiveForms K n) :
    (numberFieldArchimedeanCanonicalMatrix A).det =
      (numberFieldArchimedeanSquareCoordinateMatrix
        (K := K) (n := n)).det ^ 2 *
        (numberFieldArchimedeanBlockMatrix A).det := by
  rw [numberFieldArchimedeanCanonicalMatrix]
  rw [reindex_rectangular_real_congruence
    numberFieldArchimedeanBlockIndexEquivFin
    (numberFieldArchimedeanCoordinateMatrix K n)
    (numberFieldArchimedeanBlockMatrix A)]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  rw [Matrix.det_reindex_self]
  simp only [star_trivial]
  simp [numberFieldArchimedeanSquareCoordinateMatrix, mul_comm]
  ring

/-- Positive complex Hermitian blocks have squared real determinant norm. -/
theorem normSq_det_eq_re_sq_of_posDef
    {d : Type*} [Fintype d] [DecidableEq d]
    {A : Matrix d d ℂ} (hA : A.PosDef) :
    Complex.normSq A.det = A.det.re ^ 2 := by
  have hreal : (A.det.re : ℂ) = A.det := by
    rw [hA.isHermitian.det_eq_prod_eigenvalues]
    norm_cast
  rw [← hreal]
  simp [Complex.normSq_apply, pow_two]

/-- The assembled block determinant is the real determinant product times squared complex
determinant products. -/
theorem det_numberFieldArchimedeanBlockMatrix
    (A : numberFieldArchimedeanPositiveForms K n) :
    (numberFieldArchimedeanBlockMatrix A).det =
      (∏ w : {w : InfinitePlace K // w.IsReal},
        (A.1.1 w : Matrix (Fin n) (Fin n) ℝ).det) *
      ∏ w : {w : InfinitePlace K // w.IsComplex},
        ((A.1.2 w : Matrix (Fin n) (Fin n) ℂ).det.re) ^ 2 := by
  rw [numberFieldArchimedeanBlockMatrix, det_matrixOrthogonalSum,
    det_matrixFamilyBlockDiagonal, det_matrixFamilyBlockDiagonal]
  congr 1
  apply Finset.prod_congr rfl
  intro w hw
  rw [det_complexMatrixRowRealification]
  exact normSq_det_eq_re_sq_of_posDef (A.2.2 w)

/-- Infinite places split into real and complex places. -/
def numberFieldInfinitePlaceRealComplexEquiv :
    InfinitePlace K ≃
      {w : InfinitePlace K // w.IsReal} ⊕ {w : InfinitePlace K // w.IsComplex} where
  toFun w := if hw : w.IsReal then Sum.inl ⟨w, hw⟩ else
    Sum.inr ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩
  invFun
    | Sum.inl w => w.1
    | Sum.inr w => w.1
  left_inv w := by
    by_cases hw : w.IsReal <;> simp [hw]
  right_inv w := by
    rcases w with w | w
    · simp [w.2]
    · have hw : ¬w.1.IsReal :=
        InfinitePlace.not_isReal_iff_isComplex.mpr w.2
      simp [hw]

/-- The weighted logarithmic determinant sum is the real-place sum plus twice the complex-place
sum. -/
theorem sum_mult_log_numberFieldArchimedeanDet
    (A : numberFieldArchimedeanPositiveForms K n) :
    (∑ w : InfinitePlace K,
      (mult w : ℝ) * Real.log (numberFieldArchimedeanDet A w)) =
      (∑ w : {w : InfinitePlace K // w.IsReal},
        Real.log ((A.1.1 w : Matrix (Fin n) (Fin n) ℝ).det)) +
      ∑ w : {w : InfinitePlace K // w.IsComplex},
        2 * Real.log ((A.1.2 w : Matrix (Fin n) (Fin n) ℂ).det.re) := by
  let g : {w : InfinitePlace K // w.IsReal} ⊕
      {w : InfinitePlace K // w.IsComplex} → ℝ
    | Sum.inl w => Real.log ((A.1.1 w : Matrix (Fin n) (Fin n) ℝ).det)
    | Sum.inr w => 2 * Real.log ((A.1.2 w : Matrix (Fin n) (Fin n) ℂ).det.re)
  calc
    (∑ w : InfinitePlace K,
        (mult w : ℝ) * Real.log (numberFieldArchimedeanDet A w)) =
        ∑ w : InfinitePlace K, g (numberFieldInfinitePlaceRealComplexEquiv w) := by
      apply Finset.sum_congr rfl
      intro w hw
      by_cases hreal : w.IsReal
      · simp [g, numberFieldInfinitePlaceRealComplexEquiv,
          numberFieldArchimedeanDet, InfinitePlace.mult, hreal]
      · have hcomplex : w.IsComplex :=
          InfinitePlace.not_isReal_iff_isComplex.mp hreal
        simp [g, numberFieldInfinitePlaceRealComplexEquiv,
          numberFieldArchimedeanDet, InfinitePlace.mult, hreal, hcomplex]
    _ = ∑ w : {w : InfinitePlace K // w.IsReal} ⊕
        {w : InfinitePlace K // w.IsComplex}, g w :=
      (numberFieldInfinitePlaceRealComplexEquiv.sum_comp g)
    _ = _ := by
      simp [g, Fintype.sum_sum_type]

/-- The block determinant is the exponential of the multiplicity-weighted local log-determinant
sum. -/
theorem det_numberFieldArchimedeanBlockMatrix_eq_exp_weightedSum
    (A : numberFieldArchimedeanPositiveForms K n) :
    (numberFieldArchimedeanBlockMatrix A).det =
      Real.exp (∑ w : InfinitePlace K,
        (mult w : ℝ) * Real.log (numberFieldArchimedeanDet A w)) := by
  let J : NumberFieldArchimedeanJacobiData A :=
    Classical.choice (exists_numberFieldArchimedeanJacobiData A)
  have hreal (w : {w : InfinitePlace K // w.IsReal}) :
      0 < (A.1.1 w : Matrix (Fin n) (Fin n) ℝ).det := by
    simpa [numberFieldArchimedeanDet, w.2] using
      numberFieldArchimedeanDet_pos J w.1
  have hcomplex (w : {w : InfinitePlace K // w.IsComplex}) :
      0 < (A.1.2 w : Matrix (Fin n) (Fin n) ℂ).det.re := by
    have hw : ¬w.1.IsReal :=
      InfinitePlace.not_isReal_iff_isComplex.mpr w.2
    simpa [numberFieldArchimedeanDet, hw] using
      numberFieldArchimedeanDet_pos J w.1
  rw [det_numberFieldArchimedeanBlockMatrix,
    sum_mult_log_numberFieldArchimedeanDet, Real.exp_add]
  congr 1
  · rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro w hw
    exact (Real.exp_log (hreal w)).symm
  · rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro w hw
    rw [show 2 * Real.log
        ((A.1.2 w : Matrix (Fin n) (Fin n) ℂ).det.re) =
        Real.log ((A.1.2 w : Matrix (Fin n) (Fin n) ℂ).det.re) +
          Real.log ((A.1.2 w : Matrix (Fin n) (Fin n) ℂ).det.re) by ring,
      Real.exp_add, Real.exp_log (hcomplex w)]
    ring

/-- The canonical determinant is the fixed coordinate-volume square times the weighted local
geometric determinant. -/
theorem det_numberFieldArchimedeanCanonicalMatrix_eq_coordinate_exp
    (A : numberFieldArchimedeanPositiveForms K n) :
    (numberFieldArchimedeanCanonicalMatrix A).det =
      (numberFieldArchimedeanSquareCoordinateMatrix
        (K := K) (n := n)).det ^ 2 *
      Real.exp (numberFieldInfinitePlaceWeight (K := K) *
        numberFieldWeightedPlaceMean
          (fun w ↦ Real.log (numberFieldArchimedeanDet A w))) := by
  rw [det_numberFieldArchimedeanCanonicalMatrix,
    det_numberFieldArchimedeanBlockMatrix_eq_exp_weightedSum]
  congr 2
  unfold numberFieldWeightedPlaceMean
  field_simp [ne_of_gt (numberFieldInfinitePlaceWeight_pos (K := K))]

/-- Total archimedean place multiplicity is the degree of the number field. -/
theorem numberFieldInfinitePlaceWeight_eq_finrank :
    numberFieldInfinitePlaceWeight (K := K) = Module.finrank ℚ K := by
  have hcard := card_numberFieldArchimedeanBlockIndex (K := K) (n := 1)
  have hsum : numberFieldInfinitePlaceWeight (K := K) =
      (Fintype.card {w : InfinitePlace K // w.IsReal} : ℝ) +
        2 * Fintype.card {w : InfinitePlace K // w.IsComplex} := by
    unfold numberFieldInfinitePlaceWeight
    let g : {w : InfinitePlace K // w.IsReal} ⊕
        {w : InfinitePlace K // w.IsComplex} → ℝ
      | Sum.inl _ => 1
      | Sum.inr _ => 2
    calc
      (∑ w : InfinitePlace K, (mult w : ℝ)) =
          ∑ w : InfinitePlace K,
            g (numberFieldInfinitePlaceRealComplexEquiv w) := by
        apply Finset.sum_congr rfl
        intro w hw
        by_cases hreal : w.IsReal
        · simp [g, numberFieldInfinitePlaceRealComplexEquiv,
            InfinitePlace.mult, hreal]
        · simp [g, numberFieldInfinitePlaceRealComplexEquiv,
            InfinitePlace.mult, hreal]
      _ = ∑ w : {w : InfinitePlace K // w.IsReal} ⊕
          {w : InfinitePlace K // w.IsComplex}, g w :=
        numberFieldInfinitePlaceRealComplexEquiv.sum_comp g
      _ = _ := by
        simp [g, Fintype.sum_sum_type]
        ring
  rw [hsum]
  norm_num [numberFieldArchimedeanBlockIndex] at hcard
  have hnat : Fintype.card {w : InfinitePlace K // w.IsReal} +
      2 * Fintype.card {w : InfinitePlace K // w.IsComplex} =
        Module.finrank ℚ K := by omega
  exact_mod_cast hnat

end

end GaloisForLFunctions.HTGeometry
