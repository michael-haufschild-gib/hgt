import GaloisForLFunctions.HTGeometry.JacobiDiagonalRescale
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanUnitBalancing

/-!
# Determinant-one unit transport of archimedean Jacobi data

The integral determinant-one unit action transports simultaneous real/complex Jacobi
decompositions.  Every structural property is reconstructed, and each positive Jacobi weight is
multiplied by the exact squared infinite-place modulus of its corresponding unit.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

omit [NumberField K] in
def numberFieldArchimedeanJacobiUnitConj
    (A : numberFieldArchimedeanPositiveForms K n)
    (J : NumberFieldArchimedeanJacobiData A)
    (u : Fin n → (𝓞 K)ˣ) (hu : ∏ i, u i = 1) :
    NumberFieldArchimedeanJacobiData ((numberFieldUnitSpecialLinear u hu) • A) where
  realU w :=
    realJacobiDiagonalRescaleU
      (fun i => w.1.embedding_of_isReal w.2 (((u i : 𝓞 K) : K))) (J.realU w)
  realD w :=
    realJacobiDiagonalRescaleD
      (fun i => w.1.embedding_of_isReal w.2 (((u i : 𝓞 K) : K))) (J.realD w)
  realPos w := by
    apply realJacobiDiagonalRescaleD_pos
    · intro i
      apply (map_ne_zero (w.1.embedding_of_isReal w.2)).2
      exact_mod_cast Units.ne_zero (u i)
    · exact J.realPos w
  realUpper w := realJacobiDiagonalRescaleU_upper _ (J.realUpper w)
  realUnit w := by
    apply realJacobiDiagonalRescaleU_unit
    · intro i
      apply (map_ne_zero (w.1.embedding_of_isReal w.2)).2
      exact_mod_cast Units.ne_zero (u i)
    · exact J.realUnit w
  realForm w := by
    let g : Fin n → ℝ := fun i =>
      w.1.embedding_of_isReal w.2 (((u i : 𝓞 K) : K))
    have hg : ∀ i, g i ≠ 0 := by
      intro i
      apply (map_ne_zero (w.1.embedding_of_isReal w.2)).2
      exact_mod_cast Units.ne_zero (u i)
    change
      ((numberFieldArchimedeanConj (numberFieldUnitSpecialLinear u hu) A.1).1 w :
          Matrix (Fin n) (Fin n) ℝ) = _
    rw [show ((numberFieldArchimedeanConj (numberFieldUnitSpecialLinear u hu) A.1).1 w :
          Matrix (Fin n) (Fin n) ℝ) =
        let G := numberFieldRealOrderMatrixAt w
          ((numberFieldUnitSpecialLinear u hu :
            Matrix.SpecialLinearGroup (Fin n) (𝓞 K)) :
            Matrix (Fin n) (Fin n) (𝓞 K))
        G * (A.1.1 w : Matrix (Fin n) (Fin n) ℝ) * Gᴴ by rfl]
    change
      (let G := numberFieldRealOrderMatrixAt w (numberFieldUnitDiagonal u)
       G * (A.1.1 w : Matrix (Fin n) (Fin n) ℝ) * Gᴴ) = _
    rw [numberFieldRealOrderMatrixAt_unitDiagonal w u]
    dsimp only
    rw [Matrix.diagonal_conjTranspose, J.realForm w]
    exact realJacobiDiagonalRescale_form g (J.realD w) hg (J.realU w)
  complexU w :=
    complexJacobiDiagonalRescaleU
      (fun i => w.1.embedding (((u i : 𝓞 K) : K))) (J.complexU w)
  complexD w :=
    complexJacobiDiagonalRescaleD
      (fun i => w.1.embedding (((u i : 𝓞 K) : K))) (J.complexD w)
  complexPos w := by
    apply complexJacobiDiagonalRescaleD_pos
    · intro i
      apply (map_ne_zero w.1.embedding).2
      exact_mod_cast Units.ne_zero (u i)
    · exact J.complexPos w
  complexUpper w := complexJacobiDiagonalRescaleU_upper _ (J.complexUpper w)
  complexUnit w := by
    apply complexJacobiDiagonalRescaleU_unit
    · intro i
      apply (map_ne_zero w.1.embedding).2
      exact_mod_cast Units.ne_zero (u i)
    · exact J.complexUnit w
  complexForm w := by
    let z : Fin n → ℂ := fun i => w.1.embedding (((u i : 𝓞 K) : K))
    have hz : ∀ i, z i ≠ 0 := by
      intro i
      apply (map_ne_zero w.1.embedding).2
      exact_mod_cast Units.ne_zero (u i)
    change
      ((numberFieldArchimedeanConj (numberFieldUnitSpecialLinear u hu) A.1).2 w :
          Matrix (Fin n) (Fin n) ℂ) = _
    rw [show ((numberFieldArchimedeanConj (numberFieldUnitSpecialLinear u hu) A.1).2 w :
          Matrix (Fin n) (Fin n) ℂ) =
        let G := numberFieldComplexOrderMatrixAt w
          ((numberFieldUnitSpecialLinear u hu :
            Matrix.SpecialLinearGroup (Fin n) (𝓞 K)) :
            Matrix (Fin n) (Fin n) (𝓞 K))
        G * (A.1.2 w : Matrix (Fin n) (Fin n) ℂ) * Gᴴ by rfl]
    change
      (let G := numberFieldComplexOrderMatrixAt w (numberFieldUnitDiagonal u)
       G * (A.1.2 w : Matrix (Fin n) (Fin n) ℂ) * Gᴴ) = _
    rw [numberFieldComplexOrderMatrixAt_unitDiagonal w u]
    dsimp only
    rw [Matrix.diagonal_conjTranspose, J.complexForm w]
    exact complexJacobiDiagonalRescale_form z (J.complexD w) hz (J.complexU w)

omit [NumberField K] in
theorem numberFieldArchimedeanJacobiWeight_unitConj
    (A : numberFieldArchimedeanPositiveForms K n)
    (J : NumberFieldArchimedeanJacobiData A)
    (u : Fin n → (𝓞 K)ˣ) (hu : ∏ i, u i = 1)
    (i : Fin n) (w : InfinitePlace K) :
    numberFieldArchimedeanJacobiWeight
        (numberFieldArchimedeanJacobiUnitConj A J u hu) i w =
      numberFieldArchimedeanJacobiWeight J i w *
        (w (((u i : 𝓞 K) : K))) ^ 2 := by
  classical
  by_cases hw : w.IsReal
  · rw [numberFieldArchimedeanJacobiWeight, dif_pos hw,
      numberFieldArchimedeanJacobiWeight, dif_pos hw]
    change realJacobiDiagonalRescaleD
        (fun j => w.embedding_of_isReal hw (((u j : 𝓞 K) : K)))
        (J.realD ⟨w, hw⟩) i = _
    rw [realJacobiDiagonalRescaleD]
    congr 1
    rw [← w.norm_embedding_of_isReal hw (((u i : 𝓞 K) : K)), Real.norm_eq_abs,
      sq_abs]
  · have hc : w.IsComplex := not_isReal_iff_isComplex.mp hw
    rw [numberFieldArchimedeanJacobiWeight, dif_neg hw,
      numberFieldArchimedeanJacobiWeight, dif_neg hw]
    let z : ℂ := w.embedding (((u i : 𝓞 K) : K))
    let d : ℂ := J.complexD ⟨w, hc⟩ i
    change (complexJacobiDiagonalRescaleD
      (fun j => w.embedding (((u j : 𝓞 K) : K))) (J.complexD ⟨w, hc⟩) i).re =
        d.re * (w (((u i : 𝓞 K) : K))) ^ 2
    have hfactor : complexJacobiDiagonalRescaleD
        (fun j => w.embedding (((u j : 𝓞 K) : K)))
        (J.complexD ⟨w, hc⟩) i = (Complex.normSq z : ℂ) * d := by
      rw [complexJacobiDiagonalRescaleD]
      change z * d * star z = _
      calc
        z * d * star z = (z * star z) * d := by ring
        _ = (Complex.normSq z : ℂ) * d := by
          exact congrArg (fun q : ℂ => q * d) (Complex.mul_conj z)
    rw [hfactor]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hz : Complex.normSq z = (w (((u i : 𝓞 K) : K))) ^ 2 := by
      rw [← Complex.sq_norm, w.norm_embedding_eq]
    rw [hz]
    ring

end

end GaloisForLFunctions.HTGeometry
