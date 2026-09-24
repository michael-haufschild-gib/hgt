import GaloisForLFunctions.RHTower.DlvpSharp

/-!
# A zero-free region of width `1/(100 log γ)`

Choosing `δ = 1/(16 log γ)` in the sharp de la Vallée Poussin inequality
`4/(σ − β) ≤ 3/(σ − 1) + 5 log γ + K` and assuming a zero with `1 − β < 1/(100 log γ)` gives

```text
(1600/29) log γ  <  48 log γ + 5 log γ + K ,
```

that is `(63/29) log γ < K`, impossible once `log γ ≥ 29|K|/63`.  The width `1/100` replaces the
`1/10000` of `Sieve.exists_zero_free_region`: the gain is exactly the gain in the coefficient of
`log γ`, from `400` to `5`.
-/

open Complex GaloisForLFunctions

namespace RHTower

noncomputable section

/-- **A zero-free region of width `1/(100 log γ)` for the zero copies of `ξ`.** -/
theorem exists_xiZeroCopy_zero_free_sharp :
    ∃ T : ℝ, 4 ≤ T ∧ ∀ q : XiZeroCopy, T ≤ (q.1 : ℂ).im →
      (q.1 : ℂ).re ≤ 1 - 1 / 100 / Real.log ((q.1 : ℂ).im) := by
  obtain ⟨A, hA⟩ := Sieve.exists_pole_bound
  refine ⟨max 4 (Real.exp (29 * |dlvpSharpConstant A| / 63)), le_max_left _ _, ?_⟩
  intro q hq
  set β : ℝ := (q.1 : ℂ).re with hβdef
  set γ : ℝ := (q.1 : ℂ).im with hγdef
  set K : ℝ := dlvpSharpConstant A with hKdef
  have hγ4 : (4 : ℝ) ≤ γ := le_trans (le_max_left _ _) hq
  have hγexp : Real.exp (29 * |K| / 63) ≤ γ := le_trans (le_max_right _ _) hq
  have hγ0 : (0 : ℝ) < γ := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log γ := by
    have he : Real.exp 1 < 4 := by
      have := Real.exp_one_lt_d9
      linarith
    have h : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (Real.exp_pos 1) he
    rw [Real.log_exp] at h
    exact le_trans h.le (Real.log_le_log (by norm_num) hγ4)
  have hLpos : (0 : ℝ) < Real.log γ := by linarith
  have hLbig : 29 * |K| / 63 ≤ Real.log γ := by
    have h := Real.log_le_log (Real.exp_pos (29 * |K| / 63)) hγexp
    rwa [Real.log_exp] at h
  by_contra hcon
  rw [not_le] at hcon
  -- the test abscissa
  set σ : ℝ := 1 + 1 / (16 * Real.log γ) with hσdef
  have hδpos : (0 : ℝ) < 1 / (16 * Real.log γ) := by positivity
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hσ2 : σ ≤ 2 := by
    rw [hσdef]
    have : 1 / (16 * Real.log γ) ≤ 1 / 16 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith
  have hβ1 : β < 1 := xiZeroCopy_re_lt_one q
  have hsb0 : (0 : ℝ) < σ - β := by linarith
  have hdlvp := dlvp_sharp hA hσ1 hσ2 q hγ4
  rw [← hβdef, ← hγdef, ← hKdef] at hdlvp
  -- the pole term
  have hpole : (3 : ℝ) / (σ - 1) = 48 * Real.log γ := by
    have hs1 : σ - 1 = 1 / (16 * Real.log γ) := by rw [hσdef]; ring
    rw [hs1]
    field_simp
    ring
  -- the zero term
  have hcon' : 1 - 1 / (100 * Real.log γ) < β := by
    rw [div_div] at hcon
    convert hcon using 3
  have hsb : σ - β < 29 / (400 * Real.log γ) := by
    have hsplit : (1 : ℝ) / (16 * Real.log γ) + 1 / (100 * Real.log γ)
        = 29 / (400 * Real.log γ) := by
      field_simp
      norm_num
    rw [hσdef]
    linarith [hcon', hsplit]
  have hlow : 1600 * Real.log γ / 29 < 4 / (σ - β) := by
    rw [lt_div_iff₀ hsb0]
    have hpos : (0 : ℝ) < 1600 * Real.log γ / 29 := by positivity
    have := mul_lt_mul_of_pos_left hsb hpos
    have hval : 1600 * Real.log γ / 29 * (29 / (400 * Real.log γ)) = 4 := by
      field_simp
      ring
    linarith [this, hval]
  have hKle : K ≤ |K| := le_abs_self K
  -- combine
  have hfinal : 1600 * Real.log γ / 29 < 48 * Real.log γ + 5 * Real.log γ + K := by
    rw [← hpole]
    linarith [hlow, hdlvp]
  have h63 : 63 * Real.log γ / 29 < K := by linarith [hfinal]
  have hcontra : 29 * |K| / 63 ≤ Real.log γ := hLbig
  nlinarith [h63, hcontra, hKle, hLpos]

end

end RHTower
