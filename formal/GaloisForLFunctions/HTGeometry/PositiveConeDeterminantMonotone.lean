import GaloisForLFunctions.HTGeometry.PencilCauchySchwarz

/-!
# Determinant monotonicity on the positive cone

If `0 ⪯ A ⪯ C` then `det A ≤ det C`.

When `C` is singular its kernel is contained in the kernel of `A`, so both determinants vanish.
When `C` is invertible, write `C = S S` with `S` the positive square root and set `T = S⁻¹ A S⁻¹`.
Then `A = S T S`, so `det A = (det S)² det T = det C · det T`, and `T` is squeezed between `0` and
`1`, so all its eigenvalues lie in `[0,1]` and `det T ≤ 1`.
-/

open Finset Matrix
open scoped MatrixOrder ComplexOrder

namespace GaloisForLFunctions.HTGeometry

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## Eigenvalues of a matrix below the identity -/

omit [DecidableEq d] in
/-- The quadratic form of a nonzero vector against itself is a positive real. -/
theorem dotProduct_star_self_pos {v : d → ℂ} (hv : v ≠ 0) :
    0 < ∑ l, ‖v l‖ ^ 2 := by
  obtain ⟨l, hl⟩ : ∃ l, v l ≠ 0 := by
    by_contra h
    exact hv (funext fun l => not_not.mp fun hne => h ⟨l, hne⟩)
  refine Finset.sum_pos' (fun i _ => by positivity) ⟨l, Finset.mem_univ l, ?_⟩
  have : ‖v l‖ ≠ 0 := norm_ne_zero_iff.mpr hl
  positivity

/-- **Below the identity the eigenvalues are at most one.** -/
theorem eigenvalues_le_one_of_one_sub_posSemidef {T : Matrix d d ℂ} (hT : T.IsHermitian)
    (h : ((1 : Matrix d d ℂ) - T).PosSemidef) (i : d) : hT.eigenvalues i ≤ 1 := by
  set u : d → ℂ := (hT.eigenvectorBasis i).ofLp with hu
  have hunorm : ‖hT.eigenvectorBasis i‖ = 1 := (hT.eigenvectorBasis).orthonormal.1 i
  have hsum_one : ∑ l, ‖u l‖ ^ 2 = 1 := by
    have hn : ‖hT.eigenvectorBasis i‖ = Real.sqrt (∑ l, ‖u l‖ ^ 2) :=
      EuclideanSpace.norm_eq _
    rw [hunorm] at hn
    have hsq : Real.sqrt (∑ l, ‖u l‖ ^ 2) ^ 2 = 1 ^ 2 := by rw [← hn]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun l _ => by positivity)] at hsq
    simpa using hsq
  have hmul : T *ᵥ u = hT.eigenvalues i • u := hT.mulVec_eigenvectorBasis i
  have hquad : star u ⬝ᵥ (((1 : Matrix d d ℂ) - T) *ᵥ u)
      = ((1 - hT.eigenvalues i : ℝ) : ℂ) * ((∑ l, ‖u l‖ ^ 2 : ℝ) : ℂ) := by
    have hself : star u ⬝ᵥ u = ((∑ l, ‖u l‖ ^ 2 : ℝ) : ℂ) := by
      rw [dotProduct]
      push_cast
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]
      norm_cast
      exact Complex.normSq_eq_norm_sq _
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hmul, dotProduct_sub, hself, dotProduct_smul,
      hself, Complex.real_smul]
    push_cast
    ring
  have hpos : (0 : ℝ) < ∑ l, ‖u l‖ ^ 2 := by rw [hsum_one]; norm_num
  have hnn := Matrix.PosSemidef.dotProduct_mulVec_nonneg h u
  rw [hquad, ← Complex.ofReal_mul] at hnn
  have hnnR : 0 ≤ (1 - hT.eigenvalues i) * ∑ l, ‖u l‖ ^ 2 := Complex.zero_le_real.mp hnn
  nlinarith [hnnR, hpos]

/-- The determinant of a matrix squeezed between `0` and `1` is at most `1`. -/
theorem det_le_one_of_le_one {T : Matrix d d ℂ} (hT : T.PosSemidef)
    (h : ((1 : Matrix d d ℂ) - T).PosSemidef) :
    ∏ i, hT.isHermitian.eigenvalues i ≤ 1 := by
  refine Finset.prod_le_one (fun i _ => hT.eigenvalues_nonneg i) fun i _ => ?_
  exact eigenvalues_le_one_of_one_sub_posSemidef hT.isHermitian h i

/-! ## The singular case -/

omit [DecidableEq d] in
/-- A vector in the kernel of the larger matrix is in the kernel of the smaller one. -/
theorem mulVec_eq_zero_of_loewner {A C : Matrix d d ℂ} (hA : A.PosSemidef)
    (hAC : (C - A).PosSemidef) {v : d → ℂ} (hv : C *ᵥ v = 0) : A *ᵥ v = 0 := by
  have hC0 : star v ⬝ᵥ (C *ᵥ v) = 0 := by rw [hv, dotProduct_zero]
  have hdiff := Matrix.PosSemidef.dotProduct_mulVec_nonneg hAC v
  rw [Matrix.sub_mulVec, dotProduct_sub, hC0, zero_sub] at hdiff
  have hAle : star v ⬝ᵥ (A *ᵥ v) ≤ 0 := by
    have := neg_nonneg.mp hdiff
    exact this
  have hAge := Matrix.PosSemidef.dotProduct_mulVec_nonneg hA v
  have : star v ⬝ᵥ (A *ᵥ v) = 0 := le_antisymm hAle hAge
  exact (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hA v).mp this

/-! ## Determinant monotonicity -/

/-- **Determinant monotonicity on the positive cone.**  If `0 ⪯ A ⪯ C` then `det A ≤ det C`. -/
theorem det_le_det_of_loewner {A C : Matrix d d ℂ} (hA : A.PosSemidef) (hC : C.PosSemidef)
    (hAC : (C - A).PosSemidef) : A.det ≤ C.det := by
  by_cases hCdet : C.det = 0
  · -- singular: both determinants vanish
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hCdet
    have hAv : A *ᵥ v = 0 := mulVec_eq_zero_of_loewner hA hAC hv
    have hAdet : A.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hAv⟩
    rw [hAdet, hCdet]
  · -- invertible: conjugate into the unit ball
    have hCpd : C.PosDef := (Matrix.PosSemidef.posDef_iff_det_ne_zero hC).mpr hCdet
    set S : Matrix d d ℂ := CFC.sqrt C with hSdef
    have hSpd : S.PosDef := positiveMatrixSqrt_posDef hCpd
    have hSS : S * S = C := positiveMatrixSqrt_mul_self hCpd
    have hSherm : Sᴴ = S := hSpd.isHermitian.eq
    have hSunit : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSpd.isUnit
    set R : Matrix d d ℂ := S⁻¹ with hRdef
    have hRherm : Rᴴ = R := by rw [hRdef, Matrix.conjTranspose_nonsing_inv, hSherm]
    have hSR : S * R = 1 := Matrix.mul_nonsing_inv S hSunit
    have hRS : R * S = 1 := Matrix.nonsing_inv_mul S hSunit
    set T : Matrix d d ℂ := R * A * R with hTdef
    have hTpsd : T.PosSemidef := by
      have := Matrix.PosSemidef.mul_mul_conjTranspose_same hA R
      rwa [hRherm] at this
    have hRCR : R * C * R = 1 := by
      rw [← hSS, show R * (S * S) * R = (R * S) * (S * R) from by simp [Matrix.mul_assoc], hRS,
        hSR, Matrix.one_mul]
    have hone_sub : (1 : Matrix d d ℂ) - T = R * (C - A) * R := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hRCR, hTdef]
    have hone_psd : ((1 : Matrix d d ℂ) - T).PosSemidef := by
      rw [hone_sub]
      have := Matrix.PosSemidef.mul_mul_conjTranspose_same hAC R
      rwa [hRherm] at this
    have hSTS : S * T * S = A := by
      rw [hTdef,
        show S * (R * A * R) * S = (S * R) * A * (R * S) from by simp [Matrix.mul_assoc], hSR,
        hRS, Matrix.one_mul, Matrix.mul_one]
    -- determinant factorisation
    have hdetC : S.det * S.det = C.det := by rw [← Matrix.det_mul, hSS]
    have hdetA : A.det = C.det * T.det := by
      rw [← hSTS, Matrix.det_mul, Matrix.det_mul, ← hdetC]
      ring
    -- real comparison
    have hTeig : T.det = ((∏ i, hTpsd.isHermitian.eigenvalues i : ℝ) : ℂ) := by
      rw [hTpsd.isHermitian.det_eq_prod_eigenvalues]
      push_cast
      rfl
    have hCeig : C.det = ((∏ i, hC.isHermitian.eigenvalues i : ℝ) : ℂ) := by
      rw [hC.isHermitian.det_eq_prod_eigenvalues]
      push_cast
      rfl
    have hCnn : (0 : ℝ) ≤ ∏ i, hC.isHermitian.eigenvalues i :=
      Finset.prod_nonneg fun i _ => hC.eigenvalues_nonneg i
    have hTle : ∏ i, hTpsd.isHermitian.eigenvalues i ≤ 1 := det_le_one_of_le_one hTpsd hone_psd
    rw [hdetA, hTeig, hCeig, ← Complex.ofReal_mul]
    refine Complex.real_le_real.mpr ?_
    nlinarith [hCnn, hTle]

end GaloisForLFunctions.HTGeometry
