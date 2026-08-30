import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanCone
import GaloisForLFunctions.HTGeometry.NumberFieldDetOneUnitDiagonal
import GaloisForLFunctions.HTGeometry.NumberFieldDetOneUnitPositiveWeightBalancing

/-!
# Determinant-one unit balancing on the number-field archimedean cone

The diagonal entries of a positive real/Hermitian placewise form give an automatically positive
weight table.  Evaluation of a product-one unit diagonal shows that congruence multiplies its
`i,w` entry by the exact factor `|u_i|_w²`.  The unconditional Dirichlet-unit covering theorem
therefore balances every cone point with one field-only radius.  No positivity, condition-number,
chosen-unit, or determinant-one premise remains.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-- Positive diagonal weight at an infinite place, using the real diagonal of a Hermitian block. -/
def numberFieldArchimedeanDiagonalWeight
    (A : numberFieldArchimedeanPositiveForms K n)
    (i : Fin n) (w : InfinitePlace K) : ℝ :=
  if hw : w.IsReal then
    ((A.1.1 ⟨w, hw⟩ : selfAdjoint (Matrix (Fin n) (Fin n) ℝ)) :
      Matrix (Fin n) (Fin n) ℝ) i i
  else
    (((A.1.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩ :
        selfAdjoint (Matrix (Fin n) (Fin n) ℂ)) :
      Matrix (Fin n) (Fin n) ℂ) i i).re

omit [NumberField K] in
theorem numberFieldArchimedeanDiagonalWeight_pos
    (A : numberFieldArchimedeanPositiveForms K n)
    (i : Fin n) (w : InfinitePlace K) :
    0 < numberFieldArchimedeanDiagonalWeight A i w := by
  classical
  rw [numberFieldArchimedeanDiagonalWeight]
  split_ifs with hw
  · exact (A.2.1 ⟨w, hw⟩).diag_pos
  · have hpos : 0 <
        (((A.1.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩ :
            selfAdjoint (Matrix (Fin n) (Fin n) ℂ)) :
          Matrix (Fin n) (Fin n) ℂ) i i) :=
      (A.2.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).diag_pos
    simpa using (Complex.lt_def.1 hpos).1

omit [NumberField K] in
theorem numberFieldRealOrderMatrixAt_unitDiagonal
    (w : {w : InfinitePlace K // w.IsReal})
    (u : Fin n → (𝓞 K)ˣ) :
    numberFieldRealOrderMatrixAt w (numberFieldUnitDiagonal u) =
      Matrix.diagonal fun i =>
        w.1.embedding_of_isReal w.2 (((u i : 𝓞 K) : K)) := by
  simp [numberFieldRealOrderMatrixAt, numberFieldUnitDiagonal]

omit [NumberField K] in
theorem numberFieldComplexOrderMatrixAt_unitDiagonal
    (w : {w : InfinitePlace K // w.IsComplex})
    (u : Fin n → (𝓞 K)ˣ) :
    numberFieldComplexOrderMatrixAt w (numberFieldUnitDiagonal u) =
      Matrix.diagonal fun i => w.1.embedding (((u i : 𝓞 K) : K)) := by
  simp [numberFieldComplexOrderMatrixAt, numberFieldUnitDiagonal]

omit [NumberField K] in
/-- A product-one unit congruence rescales each local diagonal weight by the square of its place
absolute value. -/
theorem numberFieldArchimedeanDiagonalWeight_unitConj
    (u : Fin n → (𝓞 K)ˣ) (hu : ∏ i, u i = 1)
    (A : numberFieldArchimedeanPositiveForms K n)
    (i : Fin n) (w : InfinitePlace K) :
    numberFieldArchimedeanDiagonalWeight
        ((numberFieldUnitSpecialLinear u hu) • A) i w =
      numberFieldArchimedeanDiagonalWeight A i w *
        (w (((u i : 𝓞 K) : K))) ^ 2 := by
  classical
  by_cases hw : w.IsReal
  · rw [numberFieldArchimedeanDiagonalWeight, dif_pos hw,
      numberFieldArchimedeanDiagonalWeight, dif_pos hw]
    let wr : {w : InfinitePlace K // w.IsReal} := ⟨w, hw⟩
    let z : ℝ := w.embedding_of_isReal hw (((u i : 𝓞 K) : K))
    have hmatrix :
        numberFieldRealOrderMatrixAt wr
            ((numberFieldUnitSpecialLinear u hu :
              Matrix.SpecialLinearGroup (Fin n) (𝓞 K)) :
              Matrix (Fin n) (Fin n) (𝓞 K)) =
          Matrix.diagonal fun j =>
            w.embedding_of_isReal hw (((u j : 𝓞 K) : K)) := by
      exact numberFieldRealOrderMatrixAt_unitDiagonal wr u
    change
      ((numberFieldArchimedeanConj (numberFieldUnitSpecialLinear u hu) A.1).1 wr :
          Matrix (Fin n) (Fin n) ℝ) i i = _
    rw [show ((numberFieldArchimedeanConj (numberFieldUnitSpecialLinear u hu) A.1).1 wr :
          Matrix (Fin n) (Fin n) ℝ) =
        let G := numberFieldRealOrderMatrixAt wr
          ((numberFieldUnitSpecialLinear u hu :
            Matrix.SpecialLinearGroup (Fin n) (𝓞 K)) : Matrix (Fin n) (Fin n) (𝓞 K))
        G * (A.1.1 wr : Matrix (Fin n) (Fin n) ℝ) * Gᴴ by rfl]
    rw [hmatrix]
    dsimp only
    rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
    change z * ((A.1.1 wr : Matrix (Fin n) (Fin n) ℝ) i i) * z =
      ((A.1.1 wr : Matrix (Fin n) (Fin n) ℝ) i i) * (w (((u i : 𝓞 K) : K))) ^ 2
    have hz : z ^ 2 = (w (((u i : 𝓞 K) : K))) ^ 2 := by
      rw [← w.norm_embedding_of_isReal hw (((u i : 𝓞 K) : K)), Real.norm_eq_abs,
        sq_abs]
    calc
      z * ((A.1.1 wr : Matrix (Fin n) (Fin n) ℝ) i i) * z =
          ((A.1.1 wr : Matrix (Fin n) (Fin n) ℝ) i i) * z ^ 2 := by ring
      _ = ((A.1.1 wr : Matrix (Fin n) (Fin n) ℝ) i i) *
          (w (((u i : 𝓞 K) : K))) ^ 2 := by rw [hz]
  · have hc : w.IsComplex := not_isReal_iff_isComplex.mp hw
    rw [numberFieldArchimedeanDiagonalWeight, dif_neg hw,
      numberFieldArchimedeanDiagonalWeight, dif_neg hw]
    let wc : {w : InfinitePlace K // w.IsComplex} := ⟨w, hc⟩
    let z : ℂ := w.embedding (((u i : 𝓞 K) : K))
    have hmatrix :
        numberFieldComplexOrderMatrixAt wc
            ((numberFieldUnitSpecialLinear u hu :
              Matrix.SpecialLinearGroup (Fin n) (𝓞 K)) :
              Matrix (Fin n) (Fin n) (𝓞 K)) =
          Matrix.diagonal fun j => w.embedding (((u j : 𝓞 K) : K)) := by
      exact numberFieldComplexOrderMatrixAt_unitDiagonal wc u
    change
      (((numberFieldArchimedeanConj (numberFieldUnitSpecialLinear u hu) A.1).2 wc :
          Matrix (Fin n) (Fin n) ℂ) i i).re = _
    rw [show ((numberFieldArchimedeanConj (numberFieldUnitSpecialLinear u hu) A.1).2 wc :
          Matrix (Fin n) (Fin n) ℂ) =
        let G := numberFieldComplexOrderMatrixAt wc
          ((numberFieldUnitSpecialLinear u hu :
            Matrix.SpecialLinearGroup (Fin n) (𝓞 K)) : Matrix (Fin n) (Fin n) (𝓞 K))
        G * (A.1.2 wc : Matrix (Fin n) (Fin n) ℂ) * Gᴴ by rfl]
    rw [hmatrix]
    dsimp only
    rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
    let a : ℂ := (A.1.2 wc : Matrix (Fin n) (Fin n) ℂ) i i
    change (z * a * star z).re = a.re * (w (((u i : 𝓞 K) : K))) ^ 2
    have hfactor : z * a * star z = (Complex.normSq z : ℂ) * a := by
      calc
        z * a * star z = (z * star z) * a := by ring
        _ = (Complex.normSq z : ℂ) * a := by
          exact congrArg (fun q : ℂ => q * a) (Complex.mul_conj z)
    rw [hfactor]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hz : Complex.normSq z = (w (((u i : 𝓞 K) : K))) ^ 2 := by
      rw [← Complex.sq_norm, w.norm_embedding_eq]
    rw [hz]
    ring

/-- Every positive archimedean form admits determinant-one unit diagonal balancing with a
field-only radius.  Positivity of the weight table is derived from the cone point. -/
theorem exists_numberFieldArchimedeanUnitDiagonal_balancingRadius :
    ∃ R : ℝ, 0 < R ∧ ∀ (m : ℕ)
      (A : numberFieldArchimedeanPositiveForms K (m + 1)),
      ∃ u : Fin (m + 1) → (𝓞 K)ˣ,
        ∃ hu : ∏ i, u i = 1,
          ∀ i w,
            Real.exp (-(2 * (m + 1 : ℝ) * R)) *
                  (Real.exp (numberFieldWeightedPlaceMean
                      (fun v => Real.log (numberFieldArchimedeanDiagonalWeight A i v))) *
                    Real.exp (numberFieldCenteredPlaceProfileAverage
                      (fun j v => Real.log (numberFieldArchimedeanDiagonalWeight A j v)) w)) ≤
              numberFieldArchimedeanDiagonalWeight
                ((numberFieldUnitSpecialLinear u hu) • A) i w ∧
            numberFieldArchimedeanDiagonalWeight
                ((numberFieldUnitSpecialLinear u hu) • A) i w ≤
              Real.exp (2 * (m + 1 : ℝ) * R) *
                  (Real.exp (numberFieldWeightedPlaceMean
                      (fun v => Real.log (numberFieldArchimedeanDiagonalWeight A i v))) *
                    Real.exp (numberFieldCenteredPlaceProfileAverage
                      (fun j v => Real.log (numberFieldArchimedeanDiagonalWeight A j v)) w)) := by
  obtain ⟨R, hR, hbalance⟩ :=
    exists_numberFieldDetOneUnit_positiveWeight_balancingRadius (K := K)
  refine ⟨R, hR, ?_⟩
  intro m A
  obtain ⟨u, hu, hbounds⟩ := hbalance m
    (fun i w => numberFieldArchimedeanDiagonalWeight A i w)
    (fun i w => numberFieldArchimedeanDiagonalWeight_pos A i w)
  refine ⟨u, hu, ?_⟩
  intro i w
  rw [numberFieldArchimedeanDiagonalWeight_unitConj u hu A i w]
  exact hbounds i w

end

end GaloisForLFunctions.HTGeometry
