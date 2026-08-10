import GaloisForLFunctions.RHTower.GaussPrincipalStep
import GaloisForLFunctions.RHTower.GaussQuasiInnerNorm

/-!
# The one-step scalar tames the normalization

The normalized shifted blocks carry the factors `(conj d_n)^(-1)` and `d_n^(-1)`, whose norms blow
up as `n → ∞`.  The scalar `p · conj(d_n) · d_n` of the one-step factorization cancels one of them
exactly:

`(p conj(d_n) d_n) · S(v) = p · conj(d_n) · e_(-n) D (e_n v)`,

whose norm is at most `p |d_n| M ‖v‖` — and `|d_n| → 0`.  The same happens with the conjugate
block.  This is what makes the error of the one-step estimate propagate: an `L²` error is never
divided by `d_n`.
-/

namespace RHTower

open MeasureTheory

noncomputable section

theorem norm_fourierMulBlock_le (n : ℤ) : ‖fourierMulBlock n‖ ≤ 1 :=
  MeasureTheory.norm_lpBoundedMulCLM_le _ _ _

theorem norm_fourierMulBlock_apply_le (n : ℤ)
    (v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    ‖fourierMulBlock n v‖ ≤ ‖v‖ := by
  have h := (fourierMulBlock n).le_opNorm v
  refine h.trans ?_
  exact mul_le_of_le_one_left (norm_nonneg v) (norm_fourierMulBlock_le n)

/-- The one-step scalar applied to the unconjugated shifted block. -/
theorem smul_gaussShiftedBlockDiag {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {n : ℤ} (hn : n ≠ 0) (v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (((p : ℝ) : ℂ) *
        (starRingEnd ℂ (gaussSampleValue k p n) * gaussSampleValue k p n)) •
      gaussShiftedBlockDiag hm k p n v
      = (((p : ℝ) : ℂ) * starRingEnd ℂ (gaussSampleValue k p n)) •
        fourierMulBlock (-n) (gaussDiagonalBlock hm k p (fourierMulBlock n v)) := by
  have hne : gaussSampleValue k p n ≠ 0 := gaussSampleValue_ne_zero hm k p hn
  rw [gaussShiftedBlockDiag, smul_smul]
  congr 1
  field_simp

/-- **The scalar tames the normalization.** -/
theorem norm_smul_gaussShiftedBlockDiag_le {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {n : ℤ} (hn : n ≠ 0) (v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    ‖(((p : ℝ) : ℂ) *
        (starRingEnd ℂ (gaussSampleValue k p n) * gaussSampleValue k p n)) •
      gaussShiftedBlockDiag hm k p n v‖
      ≤ (p : ℝ) * ‖gaussSampleValue k p n‖ * gaussSampleValueBound hm k p * ‖v‖ := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    linarith
  have hM := gaussSampleValueBound_nonneg hm k p
  rw [smul_gaussShiftedBlockDiag hm k p hn, norm_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hppos, RCLike.norm_conj]
  have hchain :
      ‖fourierMulBlock (-n) (gaussDiagonalBlock hm k p (fourierMulBlock n v))‖
        ≤ gaussSampleValueBound hm k p * ‖v‖ := by
    refine le_trans (norm_fourierMulBlock_apply_le (-n) _) ?_
    refine le_trans ((gaussDiagonalBlock hm k p).le_opNorm _) ?_
    refine le_trans (mul_le_mul_of_nonneg_right (norm_gaussDiagonalBlock_le hm k p)
      (norm_nonneg _)) ?_
    exact mul_le_mul_of_nonneg_left (norm_fourierMulBlock_apply_le n v) hM
  calc (p : ℝ) * ‖gaussSampleValue k p n‖ *
      ‖fourierMulBlock (-n) (gaussDiagonalBlock hm k p (fourierMulBlock n v))‖
      ≤ (p : ℝ) * ‖gaussSampleValue k p n‖ * (gaussSampleValueBound hm k p * ‖v‖) := by
        refine mul_le_mul_of_nonneg_left hchain (by positivity)
    _ = (p : ℝ) * ‖gaussSampleValue k p n‖ * gaussSampleValueBound hm k p * ‖v‖ := by ring

/-- The one-step scalar applied to the conjugate shifted block. -/
theorem smul_gaussShiftedBlockOf {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {n : ℤ} (hn : n ≠ 0) (v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (((p : ℝ) : ℂ) *
        (starRingEnd ℂ (gaussSampleValue k p n) * gaussSampleValue k p n)) •
      gaussShiftedBlockOf hm k p n v
      = (((p : ℝ) : ℂ) * gaussSampleValue k p n) •
        fourierMulBlock (-n) (gaussDiagonalBlockStar hm k p (fourierMulBlock n v)) := by
  have hne : starRingEnd ℂ (gaussSampleValue k p n) ≠ 0 := by
    simpa using gaussSampleValue_ne_zero hm k p hn
  rw [gaussShiftedBlockOf, smul_smul]
  congr 1
  field_simp

theorem norm_smul_gaussShiftedBlockOf_le {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {n : ℤ} (hn : n ≠ 0) (v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    ‖(((p : ℝ) : ℂ) *
        (starRingEnd ℂ (gaussSampleValue k p n) * gaussSampleValue k p n)) •
      gaussShiftedBlockOf hm k p n v‖
      ≤ (p : ℝ) * ‖gaussSampleValue k p n‖ * gaussSampleValueBound hm k p * ‖v‖ := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    linarith
  have hM := gaussSampleValueBound_nonneg hm k p
  rw [smul_gaussShiftedBlockOf hm k p hn, norm_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hppos]
  have hchain :
      ‖fourierMulBlock (-n) (gaussDiagonalBlockStar hm k p (fourierMulBlock n v))‖
        ≤ gaussSampleValueBound hm k p * ‖v‖ := by
    refine le_trans (norm_fourierMulBlock_apply_le (-n) _) ?_
    refine le_trans ((gaussDiagonalBlockStar hm k p).le_opNorm _) ?_
    refine le_trans (mul_le_mul_of_nonneg_right (norm_gaussDiagonalBlockStar_le hm k p)
      (norm_nonneg _)) ?_
    exact mul_le_mul_of_nonneg_left (norm_fourierMulBlock_apply_le n v) hM
  calc (p : ℝ) * ‖gaussSampleValue k p n‖ *
      ‖fourierMulBlock (-n) (gaussDiagonalBlockStar hm k p (fourierMulBlock n v))‖
      ≤ (p : ℝ) * ‖gaussSampleValue k p n‖ * (gaussSampleValueBound hm k p * ‖v‖) := by
        refine mul_le_mul_of_nonneg_left hchain (by positivity)
    _ = (p : ℝ) * ‖gaussSampleValue k p n‖ * gaussSampleValueBound hm k p * ‖v‖ := by ring

end

end RHTower
