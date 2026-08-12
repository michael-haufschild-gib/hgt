import GaloisForLFunctions.HTGeometry.WeightedUnitPowerSumOscillation

/-!
# Sub-edge masking: plain Turán minors do not detect below the geometric mean

There is a finite conjugation-symmetric configuration in the open right unit half-disk,
not contained in the real axis, all of whose moments are nonnegative and all of whose plain
Turán minors are nonnegative.  Two real atoms `12/25` and `5/12` of multiplicity `100`
dominate: their mutual pair mass sits at the scale `(1/5)^(n+1)`, while a non-real conjugate
pair at `w = 50/149 + (35/149) i` has `|w| < 5/12`, so every pair interaction involving `w`
also sits at scale at most `(1/5)^(n+1)` and the multiplicity `100^2` of the real-real pairs
beats the multiplicity `100` of the cross pairs uniformly in `n`.

Consequently the inference "all plain Turán minors nonnegative ⟹ all points real" is false
for configurations satisfying every structural hypothesis of the level-cleansing machinery
(conjugation symmetry, norms at most one, positive real parts): a non-real pair hides below
the geometric mean of two larger real atoms.  Detection of such a pair requires a weight
vanishing on the larger atoms — the polynomial quantifier of the weighted Turán criterion is
not removable.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 1600000 in
/-- **Sub-edge masking.**  A conjugation-symmetric configuration in the open right unit
half-disk with a non-real point, whose moment sequence has all moments nonnegative and all
plain Turán minors nonnegative. -/
theorem exists_nonreal_config_forall_turanMinor_re_nonneg :
    ∃ (v : Fin 4 → ℂ) (c : Fin 4 → ℕ),
      (∀ i, 0 < c i) ∧
      (∀ i, ‖v i‖ ≤ 1) ∧
      (∀ i, 0 < (v i).re) ∧
      (∀ i, ∃ j, v j = (starRingEnd ℂ) (v i) ∧ c j = c i) ∧
      (∃ i, (v i).im ≠ 0) ∧
      (∀ k : ℕ, 0 ≤ (∑ i, (c i : ℂ) * v i ^ (k + 1)).re) ∧
      (∀ n : ℕ,
        0 ≤ ((∑ i, (c i : ℂ) * v i ^ (n + 1)) * (∑ i, (c i : ℂ) * v i ^ (n + 3)) -
          (∑ i, (c i : ℂ) * v i ^ (n + 2)) ^ 2).re) := by
  classical
  set a : ℂ := ((12/25 : ℝ) : ℂ) with ha
  set b : ℂ := ((5/12 : ℝ) : ℂ) with hb
  set w : ℂ := ((50/149 : ℝ) : ℂ) + ((35/149 : ℝ) : ℂ) * Complex.I with hw
  set w' : ℂ := ((50/149 : ℝ) : ℂ) - ((35/149 : ℝ) : ℂ) * Complex.I with hw'
  -- component facts
  have hwre : w.re = 50/149 := by
    simp [hw]
  have hwim : w.im = 35/149 := by
    simp [hw]
  have hw'conj : w' = (starRingEnd ℂ) w := by
    rw [hw, hw', map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
      Complex.conj_I]
    ring
  have haconj : (starRingEnd ℂ) a = a := by
    rw [ha]
    exact Complex.conj_ofReal _
  have hbconj : (starRingEnd ℂ) b = b := by
    rw [hb]
    exact Complex.conj_ofReal _
  have hnorma : ‖a‖ = 12/25 := by
    rw [ha, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by norm_num)
  have hnormb : ‖b‖ = 5/12 := by
    rw [hb, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by norm_num)
  have hnormsqw : Complex.normSq w = 25/149 := by
    rw [Complex.normSq_apply, hwre, hwim]
    norm_num
  have hnormw : ‖w‖ ≤ 5/12 := by
    have h2 : ‖w‖ ^ 2 ≤ (5/12 : ℝ) ^ 2 := by
      rw [Complex.sq_norm, hnormsqw]
      norm_num
    nlinarith [norm_nonneg w]
  have hnormaw : ‖a * w‖ ≤ 1/5 := by
    rw [norm_mul, hnorma]
    calc (12/25 : ℝ) * ‖w‖ ≤ (12/25) * (5/12) :=
          mul_le_mul_of_nonneg_left hnormw (by norm_num)
      _ = 1/5 := by norm_num
  have hnormbw : ‖b * w‖ ≤ 1/5 := by
    rw [norm_mul, hnormb]
    calc (5/12 : ℝ) * ‖w‖ ≤ (5/12) * (5/12) :=
          mul_le_mul_of_nonneg_left hnormw (by norm_num)
      _ ≤ 1/5 := by norm_num
  have hww' : w * w' = ((25/149 : ℝ) : ℂ) := by
    rw [hw'conj, Complex.mul_conj, hnormsqw]
  have hwsub : w - w' = ((2 * (35/149) : ℝ) : ℂ) * Complex.I := by
    rw [hw'conj, Complex.sub_conj, hwim]
  have hwsubsq : (w - w') ^ 2 = ((-(4 * (35/149) ^ 2) : ℝ) : ℂ) := by
    rw [hwsub, mul_pow, Complex.I_sq]
    push_cast
    ring
  have hawre : (a - w).re = 538/3725 := by
    rw [Complex.sub_re, ha, Complex.ofReal_re, hwre]
    norm_num
  have hawim : (a - w).im = -(35/149) := by
    rw [Complex.sub_im, ha, Complex.ofReal_im, hwim]
    norm_num
  have hbwre : (b - w).re = 145/1788 := by
    rw [Complex.sub_re, hb, Complex.ofReal_re, hwre]
    norm_num
  have hbwim : (b - w).im = -(35/149) := by
    rw [Complex.sub_im, hb, Complex.ofReal_im, hwim]
    norm_num
  have hA1 : Complex.normSq (a - w) = (538/3725) * (538/3725) + (35/149) * (35/149) := by
    rw [Complex.normSq_apply, hawre, hawim]
    ring
  have hA2 : Complex.normSq (b - w) = (145/1788) * (145/1788) + (35/149) * (35/149) := by
    rw [Complex.normSq_apply, hbwre, hbwim]
    ring
  have hnormsq_ge : ∀ z : ℂ, ‖z ^ 2‖ = Complex.normSq z := by
    intro z
    rw [norm_pow, Complex.sq_norm]
  have hnormw' : ‖w'‖ = ‖w‖ := by
    rw [hw'conj, RCLike.norm_conj]
  have hw're : w'.re = 50/149 := by
    rw [hw'conj, Complex.conj_re, hwre]
  have hconjw' : (starRingEnd ℂ) w' = w := by
    rw [hw'conj, Complex.conj_conj]
  have hv2 : (![a, b, w, w'] : Fin 4 → ℂ) 2 = w := rfl
  have hv3 : (![a, b, w, w'] : Fin 4 → ℂ) 3 = w' := rfl
  have hc2 : (![100, 100, 1, 1] : Fin 4 → ℕ) 2 = 1 := rfl
  have hc3 : (![100, 100, 1, 1] : Fin 4 → ℕ) 3 = 1 := rfl
  refine ⟨![a, b, w, w'], ![100, 100, 1, 1], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> decide
  · intro i
    fin_cases i
    · show ‖a‖ ≤ 1
      rw [hnorma]
      norm_num
    · show ‖b‖ ≤ 1
      rw [hnormb]
      norm_num
    · show ‖w‖ ≤ 1
      linarith [hnormw]
    · show ‖w'‖ ≤ 1
      rw [hnormw']
      linarith [hnormw]
  · intro i
    fin_cases i
    · show 0 < a.re
      rw [ha, Complex.ofReal_re]
      norm_num
    · show 0 < b.re
      rw [hb, Complex.ofReal_re]
      norm_num
    · show 0 < w.re
      rw [hwre]
      norm_num
    · show 0 < w'.re
      rw [hw're]
      norm_num
  · intro i
    fin_cases i
    · exact ⟨0, haconj.symm, rfl⟩
    · exact ⟨1, hbconj.symm, rfl⟩
    · exact ⟨3, hw'conj, rfl⟩
    · exact ⟨2, hconjw'.symm, rfl⟩
  · refine ⟨2, ?_⟩
    show w.im ≠ 0
    rw [hwim]
    norm_num
  -- nonnegative moments
  · intro k
    have hMc : (∑ i, ((![100, 100, 1, 1] : Fin 4 → ℕ) i : ℂ) *
        (![a, b, w, w'] : Fin 4 → ℂ) i ^ (k + 1)) =
        100 * a ^ (k + 1) + 100 * b ^ (k + 1) + w ^ (k + 1) + w' ^ (k + 1) := by
      rw [Fin.sum_univ_four]
      norm_num [hv2, hv3, hc2, hc3]
    rw [hMc]
    have hconjpow : w' ^ (k + 1) = (starRingEnd ℂ) (w ^ (k + 1)) := by
      rw [hw'conj, ← map_pow]
    have hre : (100 * a ^ (k + 1) + 100 * b ^ (k + 1) + w ^ (k + 1) + w' ^ (k + 1)).re =
        100 * (12/25 : ℝ) ^ (k + 1) + 100 * (5/12 : ℝ) ^ (k + 1) +
          2 * (w ^ (k + 1)).re := by
      have h1 : (100 : ℂ) * a ^ (k + 1) + 100 * b ^ (k + 1) =
          ((100 * (12/25 : ℝ) ^ (k + 1) + 100 * (5/12 : ℝ) ^ (k + 1) : ℝ) : ℂ) := by
        rw [ha, hb]
        push_cast
        ring
      have h2 : w ^ (k + 1) + w' ^ (k + 1) = ((2 * (w ^ (k + 1)).re : ℝ) : ℂ) := by
        rw [hconjpow, Complex.add_conj]
      calc (100 * a ^ (k + 1) + 100 * b ^ (k + 1) + w ^ (k + 1) + w' ^ (k + 1)).re
          = (((100 * (12/25 : ℝ) ^ (k + 1) + 100 * (5/12 : ℝ) ^ (k + 1) : ℝ) : ℂ) +
              ((2 * (w ^ (k + 1)).re : ℝ) : ℂ)).re := by
            rw [← h1, ← h2]
            congr 1
            ring
        _ = 100 * (12/25 : ℝ) ^ (k + 1) + 100 * (5/12 : ℝ) ^ (k + 1) +
              2 * (w ^ (k + 1)).re := by
            rw [Complex.add_re, Complex.ofReal_re, Complex.ofReal_re]
    rw [hre]
    have hwlea : ‖w‖ ≤ 12/25 := by
      have h2 : ‖w‖ ^ 2 ≤ (12/25 : ℝ) ^ 2 := by
        rw [Complex.sq_norm, hnormsqw]
        norm_num
      nlinarith [norm_nonneg w]
    have hlow : -((12/25 : ℝ) ^ (k + 1)) ≤ (w ^ (k + 1)).re := by
      have h1 := Complex.abs_re_le_norm (w ^ (k + 1))
      have h2 := neg_abs_le (w ^ (k + 1)).re
      have h3 : ‖w ^ (k + 1)‖ ≤ (12/25 : ℝ) ^ (k + 1) := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hwlea _
      linarith
    have hp1 : (0 : ℝ) ≤ (12/25 : ℝ) ^ (k + 1) := by positivity
    have hp2 : (0 : ℝ) ≤ (5/12 : ℝ) ^ (k + 1) := by positivity
    linarith
  -- nonnegative Turán minors
  · intro n
    have hM1 : (∑ i, ((![100, 100, 1, 1] : Fin 4 → ℕ) i : ℂ) *
        (![a, b, w, w'] : Fin 4 → ℂ) i ^ (n + 1)) =
        100 * a ^ (n + 1) + 100 * b ^ (n + 1) + w ^ (n + 1) + w' ^ (n + 1) := by
      rw [Fin.sum_univ_four]
      norm_num [hv2, hv3, hc2, hc3]
    have hM2 : (∑ i, ((![100, 100, 1, 1] : Fin 4 → ℕ) i : ℂ) *
        (![a, b, w, w'] : Fin 4 → ℂ) i ^ (n + 2)) =
        100 * a ^ (n + 2) + 100 * b ^ (n + 2) + w ^ (n + 2) + w' ^ (n + 2) := by
      rw [Fin.sum_univ_four]
      norm_num [hv2, hv3, hc2, hc3]
    have hM3 : (∑ i, ((![100, 100, 1, 1] : Fin 4 → ℕ) i : ℂ) *
        (![a, b, w, w'] : Fin 4 → ℂ) i ^ (n + 3)) =
        100 * a ^ (n + 3) + 100 * b ^ (n + 3) + w ^ (n + 3) + w' ^ (n + 3) := by
      rw [Fin.sum_univ_four]
      norm_num [hv2, hv3, hc2, hc3]
    rw [hM1, hM2, hM3]
    have hexp : 2 * ((100 * a ^ (n + 1) + 100 * b ^ (n + 1) + w ^ (n + 1) + w' ^ (n + 1)) *
        (100 * a ^ (n + 3) + 100 * b ^ (n + 3) + w ^ (n + 3) + w' ^ (n + 3)) -
        (100 * a ^ (n + 2) + 100 * b ^ (n + 2) + w ^ (n + 2) + w' ^ (n + 2)) ^ 2) =
        2 * 100 ^ 2 * ((a * b) ^ (n + 1) * (a - b) ^ 2) +
        (2 * 100 * ((a * w) ^ (n + 1) * (a - w) ^ 2) +
          2 * 100 * ((a * w') ^ (n + 1) * (a - w') ^ 2)) +
        (2 * 100 * ((b * w) ^ (n + 1) * (b - w) ^ 2) +
          2 * 100 * ((b * w') ^ (n + 1) * (b - w') ^ 2)) +
        2 * ((w * w') ^ (n + 1) * (w - w') ^ 2) := by
      ring
    have hT0 : (a * b) ^ (n + 1) * (a - b) ^ 2 =
        (((1/5 : ℝ) ^ (n + 1) * (19/300) ^ 2 : ℝ) : ℂ) := by
      have hab : a * b = ((1/5 : ℝ) : ℂ) := by
        rw [ha, hb, ← Complex.ofReal_mul]
        norm_num
      have habs : a - b = ((19/300 : ℝ) : ℂ) := by
        rw [ha, hb, ← Complex.ofReal_sub]
        norm_num
      rw [hab, habs]
      push_cast
      ring
    have hT1conj : (a * w') ^ (n + 1) * (a - w') ^ 2 =
        (starRingEnd ℂ) ((a * w) ^ (n + 1) * (a - w) ^ 2) := by
      rw [hw'conj]
      simp only [map_mul, map_pow, map_sub, haconj]
    have hT2conj : (b * w') ^ (n + 1) * (b - w') ^ 2 =
        (starRingEnd ℂ) ((b * w) ^ (n + 1) * (b - w) ^ 2) := by
      rw [hw'conj]
      simp only [map_mul, map_pow, map_sub, hbconj]
    have hT3 : (w * w') ^ (n + 1) * (w - w') ^ 2 =
        (((25/149 : ℝ) ^ (n + 1) * (-(4 * (35/149) ^ 2)) : ℝ) : ℂ) := by
      rw [hww', hwsubsq]
      push_cast
      ring
    -- real-part identity for the pair decomposition
    have hre2 := congrArg Complex.re hexp
    rw [hT0, hT1conj, hT2conj, hT3] at hre2
    have hpairre : (2 * 100 ^ 2 * (((1/5 : ℝ) ^ (n + 1) * (19/300) ^ 2 : ℝ) : ℂ) +
        (2 * 100 * ((a * w) ^ (n + 1) * (a - w) ^ 2) +
          2 * 100 * (starRingEnd ℂ) ((a * w) ^ (n + 1) * (a - w) ^ 2)) +
        (2 * 100 * ((b * w) ^ (n + 1) * (b - w) ^ 2) +
          2 * 100 * (starRingEnd ℂ) ((b * w) ^ (n + 1) * (b - w) ^ 2)) +
        2 * (((25/149 : ℝ) ^ (n + 1) * (-(4 * (35/149) ^ 2)) : ℝ) : ℂ)).re =
        2 * 100 ^ 2 * ((1/5 : ℝ) ^ (n + 1) * (19/300) ^ 2) +
          200 * (2 * ((a * w) ^ (n + 1) * (a - w) ^ 2).re) +
          200 * (2 * ((b * w) ^ (n + 1) * (b - w) ^ 2).re) +
          2 * ((25/149 : ℝ) ^ (n + 1) * (-(4 * (35/149) ^ 2))) := by
      have e1 : (2 : ℂ) * 100 * ((a * w) ^ (n + 1) * (a - w) ^ 2) +
          2 * 100 * (starRingEnd ℂ) ((a * w) ^ (n + 1) * (a - w) ^ 2) =
          ((200 * (2 * ((a * w) ^ (n + 1) * (a - w) ^ 2).re) : ℝ) : ℂ) := by
        rw [← mul_add, Complex.add_conj]
        push_cast
        ring
      have e2 : (2 : ℂ) * 100 * ((b * w) ^ (n + 1) * (b - w) ^ 2) +
          2 * 100 * (starRingEnd ℂ) ((b * w) ^ (n + 1) * (b - w) ^ 2) =
          ((200 * (2 * ((b * w) ^ (n + 1) * (b - w) ^ 2).re) : ℝ) : ℂ) := by
        rw [← mul_add, Complex.add_conj]
        push_cast
        ring
      have e0 : (2 : ℂ) * 100 ^ 2 * (((1/5 : ℝ) ^ (n + 1) * (19/300) ^ 2 : ℝ) : ℂ) =
          ((2 * 100 ^ 2 * ((1/5 : ℝ) ^ (n + 1) * (19/300) ^ 2) : ℝ) : ℂ) := by
        push_cast
        ring
      have e3 : (2 : ℂ) * (((25/149 : ℝ) ^ (n + 1) * (-(4 * (35/149) ^ 2)) : ℝ) : ℂ) =
          ((2 * ((25/149 : ℝ) ^ (n + 1) * (-(4 * (35/149) ^ 2))) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [e0, e1, e2, e3, ← Complex.ofReal_add, ← Complex.ofReal_add, ← Complex.ofReal_add,
        Complex.ofReal_re]
    rw [hpairre] at hre2
    -- lower bounds for the cross terms
    have hcross1 : -((1/5 : ℝ) ^ (n + 1) *
        ((538/3725) * (538/3725) + (35/149) * (35/149))) ≤
        ((a * w) ^ (n + 1) * (a - w) ^ 2).re := by
      have h1 := Complex.abs_re_le_norm ((a * w) ^ (n + 1) * (a - w) ^ 2)
      have h2 := neg_abs_le ((a * w) ^ (n + 1) * (a - w) ^ 2).re
      have h3 : ‖(a * w) ^ (n + 1) * (a - w) ^ 2‖ ≤
          (1/5 : ℝ) ^ (n + 1) * ((538/3725) * (538/3725) + (35/149) * (35/149)) := by
        rw [norm_mul, norm_pow, hnormsq_ge, hA1]
        refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hnormaw _) le_rfl
          (by positivity) (by positivity)
      linarith
    have hcross2 : -((1/5 : ℝ) ^ (n + 1) *
        ((145/1788) * (145/1788) + (35/149) * (35/149))) ≤
        ((b * w) ^ (n + 1) * (b - w) ^ 2).re := by
      have h1 := Complex.abs_re_le_norm ((b * w) ^ (n + 1) * (b - w) ^ 2)
      have h2 := neg_abs_le ((b * w) ^ (n + 1) * (b - w) ^ 2).re
      have h3 : ‖(b * w) ^ (n + 1) * (b - w) ^ 2‖ ≤
          (1/5 : ℝ) ^ (n + 1) * ((145/1788) * (145/1788) + (35/149) * (35/149)) := by
        rw [norm_mul, norm_pow, hnormsq_ge, hA2]
        refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hnormbw _) le_rfl
          (by positivity) (by positivity)
      linarith
    have hpowmono : ((25/149 : ℝ)) ^ (n + 1) ≤ (1/5 : ℝ) ^ (n + 1) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    -- the master bracket
    have hbracket : (0 : ℝ) ≤ (1/5 : ℝ) ^ (n + 1) *
        (2 * 100 ^ 2 * (19/300) ^ 2 -
          400 * ((538/3725) * (538/3725) + (35/149) * (35/149)) -
          400 * ((145/1788) * (145/1788) + (35/149) * (35/149)) -
          8 * (35/149) ^ 2) := by
      have hB : (0 : ℝ) ≤ 2 * 100 ^ 2 * (19/300) ^ 2 -
          400 * ((538/3725) * (538/3725) + (35/149) * (35/149)) -
          400 * ((145/1788) * (145/1788) + (35/149) * (35/149)) -
          8 * (35/149) ^ 2 := by
        norm_num
      positivity
    have hfin : (0 : ℝ) ≤ (2 * ((100 * a ^ (n + 1) + 100 * b ^ (n + 1) + w ^ (n + 1) +
        w' ^ (n + 1)) *
        (100 * a ^ (n + 3) + 100 * b ^ (n + 3) + w ^ (n + 3) + w' ^ (n + 3)) -
        (100 * a ^ (n + 2) + 100 * b ^ (n + 2) + w ^ (n + 2) + w' ^ (n + 2)) ^ 2)).re := by
      rw [hre2]
      have hp5 : (0 : ℝ) ≤ (1/5 : ℝ) ^ (n + 1) := by positivity
      nlinarith [hcross1, hcross2, hpowmono, hbracket]
    have h2re : (2 * ((100 * a ^ (n + 1) + 100 * b ^ (n + 1) + w ^ (n + 1) +
        w' ^ (n + 1)) *
        (100 * a ^ (n + 3) + 100 * b ^ (n + 3) + w ^ (n + 3) + w' ^ (n + 3)) -
        (100 * a ^ (n + 2) + 100 * b ^ (n + 2) + w ^ (n + 2) + w' ^ (n + 2)) ^ 2)).re =
        2 * ((100 * a ^ (n + 1) + 100 * b ^ (n + 1) + w ^ (n + 1) + w' ^ (n + 1)) *
        (100 * a ^ (n + 3) + 100 * b ^ (n + 3) + w ^ (n + 3) + w' ^ (n + 3)) -
        (100 * a ^ (n + 2) + 100 * b ^ (n + 2) + w ^ (n + 2) + w' ^ (n + 2)) ^ 2).re := by
      simp [Complex.mul_re]
    rw [h2re] at hfin
    linarith

end

end GaloisForLFunctions.HTGeometry
