import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Node refinement of Turán data is not monotone

The single `(0,2,1)` Turán minor of a nodal reweighting is not monotone under node refinement:
an explicit conjugation-symmetric configuration in the right half of the closed unit disk — one
real atom `1/2` with multiplicity `6` and one non-real pair `(3 ± 4i)/10` — has *nonnegative*
plain datum (`1/125`), while adjoining the single rational node `1/2` (which annihilates the
real atom) makes the reweighted datum *negative* (`-4/625`).

Hence a countable nodal criterion family carries no refinement-monotone order: passing a
coarser instance never implies passing a finer one, and any exhaustion of the family is by
enumeration, not by domination.

The mechanism in closed form is the single-pair identity
`(wW + w̄W̄)(w³W + w̄³W̄) − (w²W + w̄²W̄)² = WW̄·ww̄·(w − w̄)²`: once a nodal weight reduces a
configuration to a single off-line conjugate pair, its datum equals `-4|W|²|w|²·Im(w)²` and is
strictly negative.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- **The single-pair minor identity**: the `(0,2,1)` Turán minor of the moment sequence of one
weighted pair `(w, W), (w̄, W̄)` factors as `WW̄ · ww̄ · (w − w̄)²`. -/
theorem pair_minor_identity (w W wb Wb : ℂ) :
    (w * W + wb * Wb) * (w ^ 3 * W + wb ^ 3 * Wb) - (w ^ 2 * W + wb ^ 2 * Wb) ^ 2 =
      W * Wb * (w * wb) * (w - wb) ^ 2 := by
  ring

/-- For a genuine conjugate pair the single-pair minor is `-4·|W|²·|w|²·Im(w)²`: strictly
negative whenever the pair is off the real axis and the weight does not vanish on it. -/
theorem pair_minor_re_neg {w W : ℂ} (hw : w ≠ 0) (him : w.im ≠ 0) (hW : W ≠ 0) :
    ((w * W + (starRingEnd ℂ) w * (starRingEnd ℂ) W) *
      (w ^ 3 * W + ((starRingEnd ℂ) w) ^ 3 * (starRingEnd ℂ) W) -
      (w ^ 2 * W + ((starRingEnd ℂ) w) ^ 2 * (starRingEnd ℂ) W) ^ 2).re < 0 := by
  have hid := pair_minor_identity w W ((starRingEnd ℂ) w) ((starRingEnd ℂ) W)
  have hval : W * (starRingEnd ℂ) W * (w * (starRingEnd ℂ) w) *
      (w - (starRingEnd ℂ) w) ^ 2 =
      ((-(4 * (Complex.normSq W * (Complex.normSq w * w.im ^ 2))) : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.mul_conj, Complex.sub_conj, mul_pow, Complex.I_sq]
    push_cast
    ring
  rw [hid, hval, Complex.ofReal_re]
  have hW0 : 0 < Complex.normSq W := Complex.normSq_pos.mpr hW
  have hw0 : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
  have him2 : 0 < w.im ^ 2 := by positivity
  have hpos : 0 < Complex.normSq W * (Complex.normSq w * w.im ^ 2) :=
    mul_pos hW0 (mul_pos hw0 him2)
  linarith

/-- **Node refinement is not monotone**: an explicit conjugation-symmetric configuration in the
right half unit disk whose plain `(0,2,1)` Turán datum is nonnegative, while the datum
reweighted by the single rational node `1/2` is negative.  A nodal criterion family admits no
refinement-monotone order. -/
theorem exists_config_turanMinor_nonneg_nodal_refinement_neg :
    ∃ (v : Fin 3 → ℂ) (c : Fin 3 → ℕ) (r : ℝ),
      (∀ i, 0 < c i) ∧ (∀ i, ‖v i‖ ≤ 1) ∧ (∀ i, 0 < (v i).re) ∧
      (∀ i, ∃ j, v j = (starRingEnd ℂ) (v i) ∧ c j = c i) ∧
      (0 < r ∧ r ≤ 1) ∧
      0 ≤ ((∑ i, (c i : ℂ) * v i ^ 1) * (∑ i, (c i : ℂ) * v i ^ 3) -
        (∑ i, (c i : ℂ) * v i ^ 2) ^ 2).re ∧
      ((∑ i, (c i : ℂ) * v i ^ 1 * (v i - ((r : ℝ) : ℂ)) ^ 2) *
        (∑ i, (c i : ℂ) * v i ^ 3 * (v i - ((r : ℝ) : ℂ)) ^ 2) -
        (∑ i, (c i : ℂ) * v i ^ 2 * (v i - ((r : ℝ) : ℂ)) ^ 2) ^ 2).re < 0 := by
  classical
  set a : ℂ := ((1 / 2 : ℝ) : ℂ) with ha
  set w : ℂ := ((3 / 10 : ℝ) : ℂ) + ((2 / 5 : ℝ) : ℂ) * I with hw
  set w' : ℂ := ((3 / 10 : ℝ) : ℂ) - ((2 / 5 : ℝ) : ℂ) * I with hw'
  have hv2 : (![a, w, w'] : Fin 3 → ℂ) 2 = w' := rfl
  have hc2 : (![6, 1, 1] : Fin 3 → ℕ) 2 = 1 := rfl
  refine ⟨![a, w, w'], ![6, 1, 1], 1 / 2, ?_, ?_, ?_, ?_,
    ⟨by norm_num, by norm_num⟩, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · intro i
    have hwn : ‖w‖ ^ 2 = 1 / 4 := by
      rw [Complex.sq_norm, hw]
      norm_num [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    have hw'n : ‖w'‖ ^ 2 = 1 / 4 := by
      rw [Complex.sq_norm, hw']
      norm_num [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    fin_cases i
    · show ‖a‖ ≤ 1
      rw [ha, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    · show ‖w‖ ≤ 1
      nlinarith [norm_nonneg w]
    · show ‖w'‖ ≤ 1
      nlinarith [norm_nonneg w']
  · intro i
    fin_cases i
    · show 0 < a.re
      rw [ha, Complex.ofReal_re]
      norm_num
    · show 0 < w.re
      rw [hw]
      norm_num [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im]
    · show 0 < w'.re
      rw [hw']
      norm_num [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im]
  · intro i
    have haconj : a = (starRingEnd ℂ) a := by
      rw [ha, Complex.conj_ofReal]
    have hwconj : w' = (starRingEnd ℂ) w := by
      rw [hw, hw', map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
        Complex.conj_I]
      ring
    have hw'conj : w = (starRingEnd ℂ) w' := by
      rw [hw, hw', map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
        Complex.conj_I]
      ring
    fin_cases i
    · exact ⟨0, by simpa using haconj, rfl⟩
    · exact ⟨2, by simpa using hwconj, rfl⟩
    · exact ⟨1, by simpa using hw'conj, rfl⟩
  · have hMa : (6 : ℂ) * a ^ 1 + (1 : ℂ) * w ^ 1 + (1 : ℂ) * w' ^ 1 =
        ((18 / 5 : ℝ) : ℂ) := by
      rw [ha, hw, hw']
      push_cast
      ring
    have hMb : (6 : ℂ) * a ^ 2 + (1 : ℂ) * w ^ 2 + (1 : ℂ) * w' ^ 2 =
        ((34 / 25 : ℝ) : ℂ) := by
      rw [ha, hw, hw']
      push_cast
      linear_combination (8 / 25 : ℂ) * Complex.I_sq
    have hMc : (6 : ℂ) * a ^ 3 + (1 : ℂ) * w ^ 3 + (1 : ℂ) * w' ^ 3 =
        ((129 / 250 : ℝ) : ℂ) := by
      rw [ha, hw, hw']
      push_cast
      linear_combination (36 / 125 : ℂ) * Complex.I_sq
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      hv2, hc2, Nat.cast_ofNat, Nat.cast_one]
    rw [hMa, hMb, hMc, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.ofReal_re]
    norm_num
  · have hNa : (6 : ℂ) * a ^ 1 * (a - ((1 / 2 : ℝ) : ℂ)) ^ 2 +
        (1 : ℂ) * w ^ 1 * (w - ((1 / 2 : ℝ) : ℂ)) ^ 2 +
        (1 : ℂ) * w' ^ 1 * (w' - ((1 / 2 : ℝ) : ℂ)) ^ 2 = ((7 / 125 : ℝ) : ℂ) := by
      rw [ha, hw, hw']
      push_cast
      linear_combination (-(4 / 125) : ℂ) * Complex.I_sq
    have hNb : (6 : ℂ) * a ^ 2 * (a - ((1 / 2 : ℝ) : ℂ)) ^ 2 +
        (1 : ℂ) * w ^ 2 * (w - ((1 / 2 : ℝ) : ℂ)) ^ 2 +
        (1 : ℂ) * w' ^ 2 * (w' - ((1 / 2 : ℝ) : ℂ)) ^ 2 = ((117 / 1250 : ℝ) : ℂ) := by
      rw [ha, hw, hw']
      push_cast
      linear_combination ((32 / 625 : ℂ) * Complex.I ^ 2 - 54 / 625) * Complex.I_sq
    have hNc : (6 : ℂ) * a ^ 3 * (a - ((1 / 2 : ℝ) : ℂ)) ^ 2 +
        (1 : ℂ) * w ^ 3 * (w - ((1 / 2 : ℝ) : ℂ)) ^ 2 +
        (1 : ℂ) * w' ^ 3 * (w' - ((1 / 2 : ℝ) : ℂ)) ^ 2 = ((527 / 12500 : ℝ) : ℂ) := by
      rw [ha, hw, hw']
      push_cast
      linear_combination ((16 / 625 : ℂ) * Complex.I ^ 2 - 1 / 25) * Complex.I_sq
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      hv2, hc2, Nat.cast_ofNat, Nat.cast_one]
    rw [hNa, hNb, hNc, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.ofReal_re]
    norm_num

end GaloisForLFunctions.HTGeometry
