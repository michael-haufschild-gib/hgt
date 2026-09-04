import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanCanonicalDetRootProfile
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanRationalCuspChart
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanFirstGreedy

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder Matrix NumberField BigOperators

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-- Energy of a field scalar times a coordinate vector, split by infinite places. -/
theorem numberFieldArchimedeanEnergy_fieldScalarCoordinate
    (A : numberFieldArchimedeanPositiveForms K n)
    (s : K) (j : Fin n) :
    numberFieldArchimedeanEnergy A
        (numberFieldVectorEmbedding (fun i => if i = j then s else 0)) =
      (∑ w : {w : InfinitePlace K // w.IsReal},
        (w.1 s) ^ 2 *
          (A.1.1 w : Matrix (Fin n) (Fin n) ℝ) j j) +
      ∑ w : {w : InfinitePlace K // w.IsComplex},
        (w.1 s) ^ 2 *
          ((A.1.2 w : Matrix (Fin n) (Fin n) ℂ) j j).re := by
  unfold numberFieldArchimedeanEnergy
  congr 1
  · apply Finset.sum_congr rfl
    intro w hw
    have hz : (fun i =>
        (numberFieldVectorEmbedding (fun q => if q = j then s else 0) i).1 w) =
        Pi.single j (w.1.embedding_of_isReal w.2 s) := by
      funext i
      by_cases hij : i = j
      · subst i
        simp
      · simp [hij]
    rw [hz]
    simp only [dotProduct, Matrix.mulVec_single]
    rw [Finset.sum_eq_single j]
    · have hn : ‖w.1.embedding s‖ ^ 2 =
          (w.1.embedding_of_isReal w.2 s) ^ 2 := by
        rw [Complex.sq_norm]
        rw [← w.1.embedding_of_isReal_apply w.2 s]
        change (w.1.embedding_of_isReal w.2 s) *
            (w.1.embedding_of_isReal w.2 s) + 0 * 0 =
          (w.1.embedding_of_isReal w.2 s) ^ 2
        ring
      rw [← w.1.norm_embedding_eq s, hn]
      simp
      ring
    · intro b hb hbj
      simp [hbj]
    · simp
  · apply Finset.sum_congr rfl
    intro w hw
    have hz : (fun i =>
        (numberFieldVectorEmbedding (fun q => if q = j then s else 0) i).2 w) =
        Pi.single j (w.1.embedding s) := by
      funext i
      by_cases hij : i = j
      · subst i
        simp
      · simp [hij]
    rw [hz]
    have hstar : star (Pi.single j (w.1.embedding s) : Fin n → ℂ) =
        Pi.single j (star (w.1.embedding s)) := by
      funext i
      by_cases hij : i = j <;> simp [hij]
    rw [hstar]
    simp only [dotProduct, Matrix.mulVec_single]
    rw [Finset.sum_eq_single j]
    · rw [← w.1.norm_embedding_eq s, Complex.sq_norm]
      have hdiag : ((A.1.2 w : Matrix (Fin n) (Fin n) ℂ) j j).im = 0 := by
        have hherm := (A.1.2 w).prop
        have h := congrFun (congrFun hherm j) j
        have him := congrArg Complex.im h
        simp at him
        linarith
      simp [Complex.normSq_apply, hdiag, Complex.mul_re, Complex.mul_im]
      ring
    · intro b hb hbj
      simp [hbj]
    · simp

/-- A scalar coordinate energy is the sum of squared-place-scaled head Jacobi weights. -/
theorem numberFieldArchimedeanEnergy_fieldScalarCoordinate_eq_weight_sum
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A)
    (s : K) {j : Fin n} (hj : (j : ℕ) = 0) :
    numberFieldArchimedeanEnergy A
        (numberFieldVectorEmbedding (fun i => if i = j then s else 0)) =
      ∑ w : InfinitePlace K,
        numberFieldArchimedeanJacobiWeight J j w * (w s) ^ 2 := by
  rw [numberFieldArchimedeanEnergy_fieldScalarCoordinate]
  let g : {w : InfinitePlace K // w.IsReal} ⊕
      {w : InfinitePlace K // w.IsComplex} → ℝ
    | Sum.inl w => J.realD w j * (w.1 s) ^ 2
    | Sum.inr w => (J.complexD w j).re * (w.1 s) ^ 2
  have hreal (w : {w : InfinitePlace K // w.IsReal}) :
      (A.1.1 w : Matrix (Fin n) (Fin n) ℝ) j j = J.realD w j := by
    rw [← J.realJacobiData_form]
    exact (J.realJacobiData w).form_diag_zero hj
  have hcomplex (w : {w : InfinitePlace K // w.IsComplex}) :
      ((A.1.2 w : Matrix (Fin n) (Fin n) ℂ) j j).re =
        (J.complexD w j).re := by
    rw [← J.complexJacobiData_form]
    exact (J.complexJacobiData w).form_diag_zero hj
  rw [show (∑ w : {w : InfinitePlace K // w.IsReal},
        (w.1 s) ^ 2 * (A.1.1 w : Matrix (Fin n) (Fin n) ℝ) j j) =
      ∑ w : {w : InfinitePlace K // w.IsReal}, g (Sum.inl w) by
        apply Finset.sum_congr rfl
        intro w hw
        simp [g, hreal w, mul_comm],
    show (∑ w : {w : InfinitePlace K // w.IsComplex},
        (w.1 s) ^ 2 * ((A.1.2 w : Matrix (Fin n) (Fin n) ℂ) j j).re) =
      ∑ w : {w : InfinitePlace K // w.IsComplex}, g (Sum.inr w) by
        apply Finset.sum_congr rfl
        intro w hw
        simp [g, hcomplex w, mul_comm]]
  rw [← Fintype.sum_sum_type]
  rw [← numberFieldInfinitePlaceRealComplexEquiv.sum_comp g]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hrealw : w.IsReal
  · simp [g, numberFieldInfinitePlaceRealComplexEquiv,
      numberFieldArchimedeanJacobiWeight, hrealw, mul_comm]
  · simp [g, numberFieldInfinitePlaceRealComplexEquiv,
      numberFieldArchimedeanJacobiWeight, hrealw, mul_comm]

/-- In a rank-two cusp chart, scalar multiples of the cusp vector have energy equal to the
corresponding squared-place-scaled head Jacobi-weight sum. -/
theorem numberFieldRankTwoCuspChart_scaled_energy_eq_weight_sum
    (v : Fin 2 → K) (hv : v ≠ 0)
    (B : numberFieldArchimedeanPositiveForms K 2)
    (J : NumberFieldArchimedeanJacobiData
      (numberFieldRankTwoCuspChart v hv B))
    (s : K) :
    numberFieldArchimedeanEnergy B
        (numberFieldVectorEmbedding (fun i => s * v i)) =
      ∑ w : InfinitePlace K,
        numberFieldArchimedeanJacobiWeight J (0 : Fin 2) w * (w s) ^ 2 := by
  let F := numberFieldRankTwoCuspFrame K v hv
  have hF : F.det = 1 := numberFieldRankTwoCuspFrame_det K v hv
  let b : Fin 2 → K := fun i => if i = 0 then s else 0
  have hmul : F.mulVec b = fun i => s * v i := by
    funext i
    fin_cases i <;>
      simp [F, b, numberFieldRankTwoCuspFrame, Matrix.mulVec, dotProduct] <;> ring
  calc
    numberFieldArchimedeanEnergy B
        (numberFieldVectorEmbedding (fun i => s * v i)) =
        numberFieldArchimedeanEnergy B
          (numberFieldVectorEmbedding (F.mulVec b)) := by rw [hmul]
    _ = numberFieldArchimedeanEnergy
        (numberFieldRankTwoCuspChart v hv B)
        (numberFieldVectorEmbedding b) := by
      exact (numberFieldArchimedeanEnergy_transposeRational F hF B b).symm
    _ = _ := by
      exact numberFieldArchimedeanEnergy_fieldScalarCoordinate_eq_weight_sum
        J s rfl

end

end GaloisForLFunctions.HTGeometry
