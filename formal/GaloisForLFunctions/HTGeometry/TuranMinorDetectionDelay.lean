import GaloisForLFunctions.HTGeometry.TuranMinorNodeRefinementNonmonotone

/-!
# The detection-delay dichotomy for Turán minors

Two facts about how long an off-line conjugate pair can hide from the Turán minor ladder.

*No delay for bare pairs*: a configuration consisting of a single off-line conjugate pair has
strictly negative Turán minor at **every** index — substituting `W ↦ wⁿW` in the single-pair
identity gives `M(n)M(n+2) − M(n+1)² = −4|W|²|w|^{2n+2}·Im(w)²`.

*Delay through a level real atom*: a real atom at the same modulus carries no resonant
self-penalty, so its phased cross term with the pair can dominate the pair's negativity for an
initial window.  The explicit configuration — real atom `1` with weight `14` and the pair
`(12 ± 5i)/13` with weights `1 ± 2i`, all on the unit circle — has nonnegative `(n, n+2, n+1)`
Turán minors for every `n < 7` while containing an off-line copy of nonzero weight.  Hence no
constant-size truncation window can detect off-line copies: the detection window must depend on
the level data, and oscillation-masking requires real atoms at the level.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- **No delay for bare pairs**: a single off-line conjugate pair has strictly negative Turán
minor at every index. -/
theorem pair_minor_re_neg_at_index {w W : ℂ} (hw : w ≠ 0) (him : w.im ≠ 0) (hW : W ≠ 0)
    (n : ℕ) :
    ((w ^ (n + 1) * W + ((starRingEnd ℂ) w) ^ (n + 1) * (starRingEnd ℂ) W) *
      (w ^ (n + 3) * W + ((starRingEnd ℂ) w) ^ (n + 3) * (starRingEnd ℂ) W) -
      (w ^ (n + 2) * W + ((starRingEnd ℂ) w) ^ (n + 2) * (starRingEnd ℂ) W) ^ 2).re < 0 := by
  have key := pair_minor_re_neg hw him (mul_ne_zero (pow_ne_zero n hw) hW)
  have hshape : (w ^ (n + 1) * W + ((starRingEnd ℂ) w) ^ (n + 1) * (starRingEnd ℂ) W) *
      (w ^ (n + 3) * W + ((starRingEnd ℂ) w) ^ (n + 3) * (starRingEnd ℂ) W) -
      (w ^ (n + 2) * W + ((starRingEnd ℂ) w) ^ (n + 2) * (starRingEnd ℂ) W) ^ 2 =
      (w * (w ^ n * W) + (starRingEnd ℂ) w * (starRingEnd ℂ) (w ^ n * W)) *
        (w ^ 3 * (w ^ n * W) + ((starRingEnd ℂ) w) ^ 3 * (starRingEnd ℂ) (w ^ n * W)) -
        (w ^ 2 * (w ^ n * W) + ((starRingEnd ℂ) w) ^ 2 * (starRingEnd ℂ) (w ^ n * W)) ^ 2 := by
    rw [map_mul, map_pow]
    ring
  rw [hshape]
  exact key

set_option maxHeartbeats 1600000 in
/-- **Delay through a level real atom**: an explicit conjugation-symmetric configuration on the
unit circle — real atom `1` with weight `14`, pair `(12 ± 5i)/13` with weights `1 ± 2i` — whose
Turán minors are nonnegative for every index `n < 7` while an off-line copy of nonzero weight
is present.  No constant truncation window detects off-line copies. -/
theorem exists_offline_config_minors_nonneg_below_seven :
    ∃ (v : Fin 3 → ℂ) (Wf : Fin 3 → ℂ),
      (∀ i, ‖v i‖ = 1) ∧ (∀ i, 0 < (v i).re) ∧
      (∀ i, ∃ j, v j = (starRingEnd ℂ) (v i) ∧ Wf j = (starRingEnd ℂ) (Wf i)) ∧
      (∃ i, (v i).im ≠ 0 ∧ Wf i ≠ 0) ∧
      ∀ n : ℕ, n < 7 → 0 ≤ ((∑ i, Wf i * v i ^ (n + 1)) * (∑ i, Wf i * v i ^ (n + 3)) -
        (∑ i, Wf i * v i ^ (n + 2)) ^ 2).re := by
  classical
  set vv : ℂ := ((12 / 13 : ℝ) : ℂ) + ((5 / 13 : ℝ) : ℂ) * I with hvv
  set vb : ℂ := ((12 / 13 : ℝ) : ℂ) - ((5 / 13 : ℝ) : ℂ) * I with hvb
  set Wp : ℂ := ((1 : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * I with hWp
  set Wm : ℂ := ((1 : ℝ) : ℂ) - ((2 : ℝ) : ℂ) * I with hWm
  have hv2' : (![((1 : ℝ) : ℂ), vv, vb] : Fin 3 → ℂ) 2 = vb := rfl
  have hW2' : (![((14 : ℝ) : ℂ), Wp, Wm] : Fin 3 → ℂ) 2 = Wm := rfl
  refine ⟨![((1 : ℝ) : ℂ), vv, vb], ![((14 : ℝ) : ℂ), Wp, Wm], ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hvvn : ‖vv‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, hvv]
      norm_num [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    have hvbn : ‖vb‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, hvb]
      norm_num [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    fin_cases i
    · show ‖((1 : ℝ) : ℂ)‖ = 1
      rw [Complex.norm_real, Real.norm_eq_abs]
      norm_num
    · show ‖vv‖ = 1
      have hfac : (‖vv‖ - 1) * (‖vv‖ + 1) = 0 := by nlinarith [hvvn]
      rcases mul_eq_zero.mp hfac with h | h
      · linarith
      · linarith [norm_nonneg vv]
    · show ‖vb‖ = 1
      have hfac : (‖vb‖ - 1) * (‖vb‖ + 1) = 0 := by nlinarith [hvbn]
      rcases mul_eq_zero.mp hfac with h | h
      · linarith
      · linarith [norm_nonneg vb]
  · intro i
    fin_cases i
    · show 0 < (((1 : ℝ) : ℂ)).re
      rw [Complex.ofReal_re]
      norm_num
    · show 0 < vv.re
      rw [hvv]
      norm_num [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im]
    · show 0 < vb.re
      rw [hvb]
      norm_num [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im]
  · intro i
    have h1conj : ((1 : ℝ) : ℂ) = (starRingEnd ℂ) ((1 : ℝ) : ℂ) := by
      rw [Complex.conj_ofReal]
    have h14conj : ((14 : ℝ) : ℂ) = (starRingEnd ℂ) ((14 : ℝ) : ℂ) := by
      rw [Complex.conj_ofReal]
    have hvconj : vb = (starRingEnd ℂ) vv := by
      rw [hvv, hvb, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
        Complex.conj_I]
      ring
    have hvconj' : vv = (starRingEnd ℂ) vb := by
      rw [hvv, hvb, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
        Complex.conj_I]
      ring
    have hWconj : Wm = (starRingEnd ℂ) Wp := by
      rw [hWp, hWm, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
        Complex.conj_I]
      ring
    have hWconj' : Wp = (starRingEnd ℂ) Wm := by
      rw [hWp, hWm, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
        Complex.conj_I]
      ring
    fin_cases i
    · exact ⟨0, by simp, by simpa using h14conj⟩
    · exact ⟨2, by simpa using hvconj, by simpa using hWconj⟩
    · exact ⟨1, by simpa using hvconj', by simpa using hWconj'⟩
  · refine ⟨1, ?_, ?_⟩
    · show vv.im ≠ 0
      rw [hvv]
      norm_num [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re]
    · show Wp ≠ 0
      rw [hWp]
      intro h
      have him := congrArg Complex.im h
      norm_num [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.zero_im] at him
  · -- the weighted moment chain `Wp · vv^k` as explicit Gaussian-rational values
    have hy1 : Wp * vv ^ 1 = ((2 / 13 : ℝ) : ℂ) + ((29 / 13 : ℝ) : ℂ) * I := by
      rw [hWp, hvv, pow_one]
      push_cast
      linear_combination (10 / 13 : ℂ) * Complex.I_sq
    have hy2 : Wp * vv ^ 2 = ((-121 / 169 : ℝ) : ℂ) + ((358 / 169 : ℝ) : ℂ) * I := by
      rw [show Wp * vv ^ 2 = Wp * vv ^ 1 * vv by ring, hy1, hvv]
      push_cast
      linear_combination (145 / 169 : ℂ) * Complex.I_sq
    have hy3 : Wp * vv ^ 3 = ((-3242 / 2197 : ℝ) : ℂ) + ((3691 / 2197 : ℝ) : ℂ) * I := by
      rw [show Wp * vv ^ 3 = Wp * vv ^ 2 * vv by ring, hy2, hvv]
      push_cast
      linear_combination (1790 / 2197 : ℂ) * Complex.I_sq
    have hy4 : Wp * vv ^ 4 = ((-57359 / 28561 : ℝ) : ℂ) +
        ((28082 / 28561 : ℝ) : ℂ) * I := by
      rw [show Wp * vv ^ 4 = Wp * vv ^ 3 * vv by ring, hy3, hvv]
      push_cast
      linear_combination (18455 / 28561 : ℂ) * Complex.I_sq
    have hy5 : Wp * vv ^ 5 = ((-828718 / 371293 : ℝ) : ℂ) +
        ((50189 / 371293 : ℝ) : ℂ) * I := by
      rw [show Wp * vv ^ 5 = Wp * vv ^ 4 * vv by ring, hy4, hvv]
      push_cast
      linear_combination (140410 / 371293 : ℂ) * Complex.I_sq
    have hy6 : Wp * vv ^ 6 = ((-10195561 / 4826809 : ℝ) : ℂ) +
        ((-3541322 / 4826809 : ℝ) : ℂ) * I := by
      rw [show Wp * vv ^ 6 = Wp * vv ^ 5 * vv by ring, hy5, hvv]
      push_cast
      linear_combination (250945 / 4826809 : ℂ) * Complex.I_sq
    have hy7 : Wp * vv ^ 7 = ((-104640122 / 62748517 : ℝ) : ℂ) +
        ((-93473669 / 62748517 : ℝ) : ℂ) * I := by
      rw [show Wp * vv ^ 7 = Wp * vv ^ 6 * vv by ring, hy6, hvv]
      push_cast
      linear_combination (-17706610 / 62748517 : ℂ) * Complex.I_sq
    have hy8 : Wp * vv ^ 8 = ((-788313119 / 815730721 : ℝ) : ℂ) +
        ((-1644884638 / 815730721 : ℝ) : ℂ) * I := by
      rw [show Wp * vv ^ 8 = Wp * vv ^ 7 * vv by ring, hy7, hvv]
      push_cast
      linear_combination (-467368345 / 815730721 : ℂ) * Complex.I_sq
    have hy9 : Wp * vv ^ 9 = ((-1235334238 / 10604499373 : ℝ) : ℂ) +
        ((-23680181251 / 10604499373 : ℝ) : ℂ) * I := by
      rw [show Wp * vv ^ 9 = Wp * vv ^ 8 * vv by ring, hy8, hvv]
      push_cast
      linear_combination (-8224423190 / 10604499373 : ℂ) * Complex.I_sq
    -- conjugate side and the real moment values
    have hvconj : vb = (starRingEnd ℂ) vv := by
      rw [hvv, hvb, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
        Complex.conj_I]
      ring
    have hWconj : Wm = (starRingEnd ℂ) Wp := by
      rw [hWp, hWm, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
        Complex.conj_I]
      ring
    have hcv : ∀ k : ℕ, Wm * vb ^ k = (starRingEnd ℂ) (Wp * vv ^ k) := by
      intro k
      rw [hvconj, hWconj, ← map_pow, ← map_mul]
    have hMof : ∀ (k : ℕ) (x y M : ℝ), Wp * vv ^ k = ((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I →
        14 + 2 * x = M →
        ((14 : ℝ) : ℂ) * ((1 : ℝ) : ℂ) ^ k + Wp * vv ^ k + Wm * vb ^ k = ((M : ℝ) : ℂ) := by
      intro k x y M hxy hM
      rw [hcv k, hxy, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
        Complex.conj_I, ← hM]
      push_cast
      ring
    have hM1 := hMof 1 _ _ _ hy1 (by norm_num : (14 : ℝ) + 2 * (2 / 13) = 186 / 13)
    have hM2 := hMof 2 _ _ _ hy2
      (by norm_num : (14 : ℝ) + 2 * (-121 / 169) = 2124 / 169)
    have hM3 := hMof 3 _ _ _ hy3
      (by norm_num : (14 : ℝ) + 2 * (-3242 / 2197) = 24274 / 2197)
    have hM4 := hMof 4 _ _ _ hy4
      (by norm_num : (14 : ℝ) + 2 * (-57359 / 28561) = 285136 / 28561)
    have hM5 := hMof 5 _ _ _ hy5
      (by norm_num : (14 : ℝ) + 2 * (-828718 / 371293) = 3540666 / 371293)
    have hM6 := hMof 6 _ _ _ hy6
      (by norm_num : (14 : ℝ) + 2 * (-10195561 / 4826809) = 47184204 / 4826809)
    have hM7 := hMof 7 _ _ _ hy7
      (by norm_num : (14 : ℝ) + 2 * (-104640122 / 62748517) = 669198994 / 62748517)
    have hM8 := hMof 8 _ _ _ hy8
      (by norm_num : (14 : ℝ) + 2 * (-788313119 / 815730721) = 9843603856 / 815730721)
    have hM9 := hMof 9 _ _ _ hy9
      (by norm_num :
        (14 : ℝ) + 2 * (-1235334238 / 10604499373) = 145992322746 / 10604499373)
    intro n hn
    have hsplit : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, hv2', hW2']
    rcases hsplit with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num only [] <;>
      [rw [hM1, hM3, hM2]; rw [hM2, hM4, hM3]; rw [hM3, hM5, hM4]; rw [hM4, hM6, hM5];
        rw [hM5, hM7, hM6]; rw [hM6, hM8, hM7]; rw [hM7, hM9, hM8]] <;>
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
        Complex.ofReal_re] <;>
      norm_num

end GaloisForLFunctions.HTGeometry
