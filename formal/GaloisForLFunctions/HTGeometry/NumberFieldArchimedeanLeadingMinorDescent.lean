import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanCongruenceFrame
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanSiegelData

/-!
# Global leading-minor descent over a number field

Real and Hermitian Siegel estimates are put on one interface.  One maximal minor of the transpose
of an integral special-linear matrix is selected globally.  At every real or complex infinite
place the matching prescribed-minor estimate is applied to that same minor.  Its weighted total
logarithm is nonnegative by the algebraic-integer product formula, which yields the all-place
leading-minor descent without any false placewise lower bound.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder NumberField BigOperators

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n k : ℕ}

/-- Product of the first `k` real Jacobi weights at an arbitrary infinite place. -/
def numberFieldArchimedeanLeadingJacobiProduct
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A) (hk : k ≤ n)
    (w : InfinitePlace K) : ℝ :=
  if hw : w.IsReal then
    ∏ j : Fin k, J.realD ⟨w, hw⟩ (Fin.castLE hk j)
  else
    ∏ j : Fin k, (J.complexD
      ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩ (Fin.castLE hk j)).re

/-- Determinant of the leading `k`-block, using the real determinant at a real place and the real
part of the Hermitian determinant at a complex place. -/
def numberFieldArchimedeanLeadingDet
    (A : numberFieldArchimedeanPositiveForms K n) (hk : k ≤ n)
    (w : InfinitePlace K) : ℝ :=
  if hw : w.IsReal then
    (leadingBlock hk (A.1.1 ⟨w, hw⟩ : Matrix (Fin n) (Fin n) ℝ)).det
  else
    (complexLeadingBlock hk
      (A.1.2 ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩ :
        Matrix (Fin n) (Fin n) ℂ)).det.re

omit [NumberField K] in
/-- Every leading Jacobi product is strictly positive. -/
theorem numberFieldArchimedeanLeadingJacobiProduct_pos
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A) (hk : k ≤ n)
    (w : InfinitePlace K) :
    0 < numberFieldArchimedeanLeadingJacobiProduct J hk w := by
  classical
  rw [numberFieldArchimedeanLeadingJacobiProduct]
  split_ifs with hw
  · exact Finset.prod_pos fun j _ => J.realPos ⟨w, hw⟩ _
  · exact Finset.prod_pos fun j _ =>
      (Complex.lt_def.1 (J.complexPos
        ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩ _)).1

/-- A nonsingular row-selected square minor forces the row selector to be injective. -/
theorem rows_injective_of_submatrix_det_ne_zero
    {R : Type*} [CommRing R] (M : Matrix (Fin n) (Fin k) R)
    (rows : Fin k → Fin n) (hdet : (M.submatrix rows id).det ≠ 0) :
    Function.Injective rows := by
  classical
  intro a b hab
  by_contra hne
  apply hdet
  exact Matrix.det_zero_of_row_eq hne (by
    funext c
    simp [hab])

/-- One positive quasi-diagonal constant works simultaneously for real symmetric and complex
Hermitian Siegel data. -/
theorem exists_real_complex_siegel_quasiDiagonal
    (n : ℕ) (t u : ℝ) (ht : 1 ≤ t) :
    ∃ c : ℝ, 0 < c ∧
      (∀ J : JacobiData n, J.IsSiegel t u → ∀ v : Fin n → ℝ,
        c * (∑ i, J.d i * (v i) ^ 2) ≤ v ⬝ᵥ J.form.mulVec v) ∧
      (∀ J : ComplexJacobiData n, J.IsSiegel t u → ∀ v : Fin n → ℂ,
        c * (∑ i, J.d i * ‖v i‖ ^ 2) ≤
          (star v ⬝ᵥ J.form.mulVec v).re) := by
  obtain ⟨cr, hcr, hreal⟩ := exists_quasiDiagonal n t u ht
  obtain ⟨cc, hcc, hcomplex⟩ := exists_complexSiegel_quasiDiagonal n t u ht
  refine ⟨min cr cc, lt_min hcr hcc, ?_, ?_⟩
  · intro J hJ v
    refine le_trans (mul_le_mul_of_nonneg_right (min_le_left cr cc) ?_) (hreal J hJ v)
    exact Finset.sum_nonneg fun i _ => mul_nonneg (J.pos i).le (sq_nonneg _)
  · intro J hJ v
    refine le_trans (mul_le_mul_of_nonneg_right (min_le_right cr cc) ?_) (hcomplex J hJ v)
    exact Finset.sum_nonneg fun i _ => mul_nonneg (J.pos i).le (sq_nonneg _)

omit [NumberField K] in
/-- The real leading block of the number-field action is the Gram form on the transpose frame. -/
theorem numberFieldReal_action_leadingBlock_eq_frame
    (A : numberFieldArchimedeanPositiveForms K n)
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
    (w : {w : InfinitePlace K // w.IsReal}) (hk : k ≤ n) :
    leadingBlock hk (((g • A).1.1 w : selfAdjoint (Matrix (Fin n) (Fin n) ℝ)) :
      Matrix (Fin n) (Fin n) ℝ) =
      let G := numberFieldRealOrderMatrixAt w
        (g : Matrix (Fin n) (Fin n) (𝓞 K))
      let C := (Matrix.transpose G).submatrix id (Fin.castLE hk)
      Matrix.transpose C * (A.1.1 w : Matrix (Fin n) (Fin n) ℝ) * C := by
  let G := numberFieldRealOrderMatrixAt w
    (g : Matrix (Fin n) (Fin n) (𝓞 K))
  change leadingBlock hk (G * (A.1.1 w : Matrix (Fin n) (Fin n) ℝ) *
    Matrix.conjTranspose G) = _
  have hstar : Matrix.conjTranspose G = Matrix.transpose G := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  rw [hstar]
  simpa [G] using
    (leadingBlock_congr_frame hk (A.1.1 w : Matrix (Fin n) (Fin n) ℝ)
      (Matrix.transpose G))

omit [NumberField K] in
/-- The complex leading block of the number-field action is the Hermitian Gram form on the
conjugate-transpose frame. -/
theorem numberFieldComplex_action_leadingBlock_eq_frame
    (A : numberFieldArchimedeanPositiveForms K n)
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
    (w : {w : InfinitePlace K // w.IsComplex}) (hk : k ≤ n) :
    complexLeadingBlock hk
      (((g • A).1.2 w : selfAdjoint (Matrix (Fin n) (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) =
      let G := numberFieldComplexOrderMatrixAt w
        (g : Matrix (Fin n) (Fin n) (𝓞 K))
      let C := (Matrix.conjTranspose G).submatrix id (Fin.castLE hk)
      Matrix.conjTranspose C * (A.1.2 w : Matrix (Fin n) (Fin n) ℂ) * C := by
  let G := numberFieldComplexOrderMatrixAt w
    (g : Matrix (Fin n) (Fin n) (𝓞 K))
  change complexLeadingBlock hk
    (G * (A.1.2 w : Matrix (Fin n) (Fin n) ℂ) * Matrix.conjTranspose G) = _
  simpa [G] using
    (complexLeadingBlock_congr_frame hk
      (A.1.2 w : Matrix (Fin n) (Fin n) ℂ) (Matrix.conjTranspose G))

omit [NumberField K] in
/-- Real-place selected-minor bound for the actual number-field action. -/
theorem numberFieldReal_siegel_selectedMinor_bound
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A)
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
    (w : {w : InfinitePlace K // w.IsReal})
    {t u c : ℝ} (ht : 1 ≤ t) (hc : 0 < c)
    (hS : (J.realJacobiData w).IsSiegel t u)
    (hquasi : ∀ v : Fin n → ℝ,
      c * (∑ i, J.realD w i * (v i) ^ 2) ≤
        v ⬝ᵥ (A.1.1 w : Matrix (Fin n) (Fin n) ℝ).mulVec v)
    (hk : k ≤ n) (rows : Fin k → Fin n) (hrows : Function.Injective rows) :
    c ^ k * numberFieldArchimedeanLeadingJacobiProduct J hk w.1 *
        (w.1 (((((Matrix.transpose
          (g : Matrix (Fin n) (Fin n) (𝓞 K))).submatrix rows
            (Fin.castLE hk)).det : 𝓞 K) : K))) ^ 2 ≤
      (Nat.factorial k : ℝ) * (t ^ n) ^ k *
        numberFieldArchimedeanLeadingDet (g • A) hk w.1 := by
  classical
  let G := numberFieldRealOrderMatrixAt w
    (g : Matrix (Fin n) (Fin n) (𝓞 K))
  let γ := Matrix.transpose G
  let C := γ.submatrix id (Fin.castLE hk)
  have hγdet : γ.det = 1 := by
    rw [show γ.det = G.det by simp [γ]]
    exact numberFieldRealSpecialLinearAt_det w g
  have hγunit : IsUnit γ := by
    rw [Matrix.isUnit_iff_isUnit_det, hγdet]
    exact isUnit_one
  have hC : Function.Injective C.mulVec :=
    leadingFrame_mulVec_injective hk (Matrix.mulVec_injective_of_isUnit hγunit)
  have hsel := real_siegel_selectedMinor_bound ht hc (J.realJacobiData w) hS
    (fun v => by
      rw [J.realJacobiData_form w]
      exact hquasi v)
    hk C hC rows hrows
  have hz : ((C.submatrix rows id).det) ^ 2 =
      (w.1 (((((Matrix.transpose
        (g : Matrix (Fin n) (Fin n) (𝓞 K))).submatrix rows
          (Fin.castLE hk)).det : 𝓞 K) : K))) ^ 2 := by
    calc
      ((C.submatrix rows id).det) ^ 2 = |(C.submatrix rows id).det| ^ 2 :=
        (sq_abs _).symm
      _ = (w.1 (((((Matrix.transpose
          (g : Matrix (Fin n) (Fin n) (𝓞 K))).submatrix rows
            (Fin.castLE hk)).det : 𝓞 K) : K))) ^ 2 := by
        rw [show |(C.submatrix rows id).det| =
            w.1 (((((Matrix.transpose
              (g : Matrix (Fin n) (Fin n) (𝓞 K))).submatrix rows
                (Fin.castLE hk)).det : 𝓞 K) : K)) by
          simpa [C, γ, G] using
            (abs_numberFieldReal_transposeFrame_minor_det w
              (g : Matrix (Fin n) (Fin n) (𝓞 K)) hk rows)]
  have hy : (Matrix.transpose C *
      (A.1.1 w : Matrix (Fin n) (Fin n) ℝ) * C).det =
      (leadingBlock hk
        (((g • A).1.1 w : selfAdjoint (Matrix (Fin n) (Fin n) ℝ)) :
          Matrix (Fin n) (Fin n) ℝ)).det := by
    simpa [C, γ, G] using
      (congrArg Matrix.det
        (numberFieldReal_action_leadingBlock_eq_frame A g w hk)).symm
  rw [J.realJacobiData_form w, hz, hy] at hsel
  simpa [numberFieldArchimedeanLeadingJacobiProduct,
    numberFieldArchimedeanLeadingDet,
    NumberFieldArchimedeanJacobiData.realJacobiData, dif_pos w.2] using hsel

omit [NumberField K] in
/-- Complex-place selected-minor bound for the actual number-field action. -/
theorem numberFieldComplex_siegel_selectedMinor_bound
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A)
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
    (w : {w : InfinitePlace K // w.IsComplex})
    {t u c : ℝ} (ht : 1 ≤ t) (hc : 0 < c)
    (hS : (J.complexJacobiData w).IsSiegel t u)
    (hquasi : ∀ v : Fin n → ℂ,
      c * (∑ i, (J.complexD w i).re * ‖v i‖ ^ 2) ≤
        (star v ⬝ᵥ
          (A.1.2 w : Matrix (Fin n) (Fin n) ℂ).mulVec v).re)
    (hk : k ≤ n) (rows : Fin k → Fin n) (hrows : Function.Injective rows) :
    c ^ k * numberFieldArchimedeanLeadingJacobiProduct J hk w.1 *
        (w.1 (((((Matrix.transpose
          (g : Matrix (Fin n) (Fin n) (𝓞 K))).submatrix rows
            (Fin.castLE hk)).det : 𝓞 K) : K))) ^ 2 ≤
      (Nat.factorial k : ℝ) * (t ^ n) ^ k *
        numberFieldArchimedeanLeadingDet (g • A) hk w.1 := by
  classical
  let G := numberFieldComplexOrderMatrixAt w
    (g : Matrix (Fin n) (Fin n) (𝓞 K))
  let γ := Matrix.conjTranspose G
  let C := γ.submatrix id (Fin.castLE hk)
  have hγdet : γ.det = 1 := by
    rw [show γ.det = star G.det by simp [γ]]
    rw [numberFieldComplexSpecialLinearAt_det, star_one]
  have hγunit : IsUnit γ := by
    rw [Matrix.isUnit_iff_isUnit_det, hγdet]
    exact isUnit_one
  have hC : Function.Injective C.mulVec :=
    leadingFrame_mulVec_injective hk (Matrix.mulVec_injective_of_isUnit hγunit)
  have hsel := complex_siegel_selectedMinor_bound ht hc (J.complexJacobiData w) hS
    (fun v => by
      rw [J.complexJacobiData_form w]
      exact hquasi v)
    hk C hC rows hrows
  have hz : ‖(C.submatrix rows id).det‖ ^ 2 =
      (w.1 (((((Matrix.transpose
        (g : Matrix (Fin n) (Fin n) (𝓞 K))).submatrix rows
          (Fin.castLE hk)).det : 𝓞 K) : K))) ^ 2 := by
    rw [show ‖(C.submatrix rows id).det‖ =
        w.1 (((((Matrix.transpose
          (g : Matrix (Fin n) (Fin n) (𝓞 K))).submatrix rows
            (Fin.castLE hk)).det : 𝓞 K) : K)) by
      simpa [C, γ, G] using
        (norm_numberFieldComplex_conjTransposeFrame_minor_det w
          (g : Matrix (Fin n) (Fin n) (𝓞 K)) hk rows)]
  have hy : (Matrix.conjTranspose C *
      (A.1.2 w : Matrix (Fin n) (Fin n) ℂ) * C).det.re =
      (complexLeadingBlock hk
        (((g • A).1.2 w : selfAdjoint (Matrix (Fin n) (Fin n) ℂ)) :
          Matrix (Fin n) (Fin n) ℂ)).det.re := by
    simpa [C, γ, G] using
      (congrArg (fun M : Matrix (Fin k) (Fin k) ℂ => M.det.re)
        (numberFieldComplex_action_leadingBlock_eq_frame A g w hk)).symm
  rw [J.complexJacobiData_form w, hz, hy] at hsel
  simpa [numberFieldArchimedeanLeadingJacobiProduct,
    numberFieldArchimedeanLeadingDet, dif_neg
      (InfinitePlace.not_isReal_iff_isComplex.mpr w.2),
    NumberFieldArchimedeanJacobiData.complexJacobiData] using hsel

/-- One globally selected algebraic-integer minor gives the all-place logarithmic leading-minor
descent for simultaneous real/Hermitian Siegel data. -/
theorem exists_numberFieldArchimedean_globalLeadingMinor_descent
    (n : ℕ) (t u : ℝ) (ht : 1 ≤ t) :
    ∃ c : ℝ, 0 < c ∧ ∀
      (A : numberFieldArchimedeanPositiveForms K n)
      (J : NumberFieldArchimedeanJacobiData A),
      J.IsSiegel t u →
      ∀ (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
        (k : ℕ) (hk : k ≤ n),
      ∃ rows : Fin k → Fin n, Function.Injective rows ∧
        ∑ w : InfinitePlace K, (mult w : ℝ) *
            Real.log (numberFieldArchimedeanLeadingJacobiProduct J hk w) ≤
          (∑ w : InfinitePlace K, (mult w : ℝ)) *
              (Real.log ((Nat.factorial k : ℝ) * (t ^ n) ^ k) -
                Real.log (c ^ k)) +
            ∑ w : InfinitePlace K, (mult w : ℝ) *
              Real.log (numberFieldArchimedeanLeadingDet (g • A) hk w) := by
  classical
  obtain ⟨c, hc, hreal, hcomplex⟩ :=
    exists_real_complex_siegel_quasiDiagonal n t u ht
  refine ⟨c, hc, ?_⟩
  intro A J hS g k hk
  let gT : Matrix.SpecialLinearGroup (Fin n) (𝓞 K) :=
    numberFieldTransposeSpecialLinear
      (g : Matrix (Fin n) (Fin n) (𝓞 K))
      (Matrix.SpecialLinearGroup.det_coe g)
  obtain ⟨rows, hminor, _hEmbeddingProduct⟩ :=
    exists_numberFieldSpecialLinear_leadingMinor_productFormula gT hk
  let α : 𝓞 K := ((Matrix.transpose
    (g : Matrix (Fin n) (Fin n) (𝓞 K))).submatrix rows (Fin.castLE hk)).det
  have hα : α ≠ 0 := by
    simpa [α, gT, numberFieldTransposeSpecialLinear] using hminor
  have hrows : Function.Injective rows := by
    apply rows_injective_of_submatrix_det_ne_zero
      ((Matrix.transpose (g : Matrix (Fin n) (Fin n) (𝓞 K))).submatrix
        id (Fin.castLE hk)) rows
    simpa [α] using hα
  refine ⟨rows, hrows, ?_⟩
  let p : InfinitePlace K → ℝ :=
    numberFieldArchimedeanLeadingJacobiProduct J hk
  let z : InfinitePlace K → ℝ := fun w => w (α : K)
  let y : InfinitePlace K → ℝ :=
    numberFieldArchimedeanLeadingDet (g • A) hk
  let a : ℝ := c ^ k
  let b : ℝ := (Nat.factorial k : ℝ) * (t ^ n) ^ k
  have ha : 0 < a := pow_pos hc k
  have hb : 0 < b := by
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    exact mul_pos (by positivity) (pow_pos (pow_pos ht0 n) k)
  have hp (w : InfinitePlace K) : 0 < p w :=
    numberFieldArchimedeanLeadingJacobiProduct_pos J hk w
  have hαK : (α : K) ≠ 0 := by
    exact_mod_cast hα
  have hz (w : InfinitePlace K) : 0 < z w := by
    change 0 < w (α : K)
    rw [← w.norm_embedding_eq, norm_pos_iff]
    exact (map_ne_zero w.embedding).2 hαK
  have hmul (w : InfinitePlace K) : a * p w * (z w) ^ 2 ≤ b * y w := by
    rcases InfinitePlace.isReal_or_isComplex w with hw | hw
    · simpa [a, b, p, z, y, α] using
        (numberFieldReal_siegel_selectedMinor_bound J g ⟨w, hw⟩ ht hc
          (hS.1 ⟨w, hw⟩)
          (fun v => by
            have hq := hreal (J.realJacobiData ⟨w, hw⟩)
              (hS.1 ⟨w, hw⟩) v
            rw [J.realJacobiData_form ⟨w, hw⟩] at hq
            simpa [NumberFieldArchimedeanJacobiData.realJacobiData] using hq)
          hk rows hrows)
    · simpa [a, b, p, z, y, α] using
        (numberFieldComplex_siegel_selectedMinor_bound J g ⟨w, hw⟩ ht hc
          (hS.2 ⟨w, hw⟩)
          (fun v => by
            have hq := hcomplex (J.complexJacobiData ⟨w, hw⟩)
              (hS.2 ⟨w, hw⟩) v
            rw [J.complexJacobiData_form ⟨w, hw⟩] at hq
            simpa [NumberFieldArchimedeanJacobiData.complexJacobiData] using hq)
          hk rows hrows)
  have hy (w : InfinitePlace K) : 0 < y w := by
    have hleft : 0 < a * p w * (z w) ^ 2 :=
      mul_pos (mul_pos ha (hp w)) (sq_pos_of_pos (hz w))
    have hby : 0 < b * y w := lt_of_lt_of_le hleft (hmul w)
    by_contra hnot
    have hy0 : y w ≤ 0 := le_of_not_gt hnot
    have hby0 : b * y w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb.le hy0
    exact (not_lt_of_ge hby0) hby
  have hlocal (w : InfinitePlace K) :
      Real.log a + Real.log (p w) + 2 * Real.log (z w) ≤
        Real.log b + Real.log (y w) :=
    log_mul_sq_le_log_mul ha (hp w) (hz w) hb (hy w) (hmul w)
  have hzsum : 0 ≤ ∑ w : InfinitePlace K,
      (mult w : ℝ) * Real.log (z w) := by
    simpa [z] using weightedSum_numberFieldIntegerPlaceLog_nonneg α hα
  simpa [a, b, p, y] using
    (weighted_log_sum_le
      (fun w : InfinitePlace K => (mult w : ℝ)) p z y
      (fun w => Nat.cast_nonneg (mult w)) hlocal hzsum)

end

end GaloisForLFunctions.HTGeometry
