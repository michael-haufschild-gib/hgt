import GaloisForLFunctions.RHTower.ZetaOneLineLogPowerLowerBound
import GaloisForLFunctions.RHTower.ZetaLineLowerBound

/-!
# The Möbius function is quantitatively unpretentious

`∑_{p ≤ x} (1 + cos(t log p))/p` is the squared pretentious distance from the Liouville sequence
`p ↦ −1` to the archimedean character `p ↦ p^{it}`, and it equals
`log log x + Re ∑_{p≤x} p^{-1-it} + O(1)`, so a lower bound for `ζ` on the line
`σ = 1 + 1/log x` transfers to it directly.

Feeding in the abscissa-free bound `‖ζ(σ+it)‖ ≥ c(log|t|)^{-11}` gives

`∑_{p ≤ x} (1 + cos(t log p))/p ≥ log log x − 11 log log|t| − C`,

uniformly in the frequency.  Over a range `|t| ≤ T` with `log T` polynomial in `log x` this is
`log log x − O(log log log x)`; the corpus's earlier uniform statement over the polynomial horizon
gave only `(log log log x − C)/4`, which is smaller than the Ramaré diagonal it has to beat.
-/

namespace RHTower

open Complex

noncomputable section

/-- **The prime cosine sum from any lower bound for `ζ` on the shifted line.**  This is
`primeCosPlusSum_ge_low_freq` with the frequency restriction removed: the low-frequency hypothesis
there is used only to produce the value of `ζ` at the single point `1 + 1/log x + it`, so supplying
that value directly frees the statement of any constraint on `t`. -/
theorem primeCosPlusSum_ge_of_zeta_lower {c : ℝ} (hc0 : 0 < c) {x t : ℝ}
    (hx : Real.exp 2 ≤ x)
    (hz : c ≤ ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ))‖) :
    Real.log (Real.log x) + Real.log c + 2 * Sieve.meisselMertensConst
        - (2 * ((2 * Sieve.mertensFirstConst + 1 / 2) + 1) + zetaDeficitConst)
      ≤ primeCosPlusSum t x := by
  have hexp2 : (7 : ℝ) < Real.exp 2 := by
    have h := Real.exp_one_gt_d9
    have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [h, Real.exp_pos 1, hsq]
  have hx7 : (7 : ℝ) < x := lt_of_lt_of_le hexp2 hx
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hlogx : (2 : ℝ) ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 2) hx
    rwa [Real.log_exp] at h
  have hlogx0 : (0 : ℝ) < Real.log x := by linarith
  have hdef := abs_le.mp (abs_zeta_deficit_sub_primeClockEnergy_le (τ := t) (x := x) hx)
  have hfloor2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx2)
  have hfloor6 : (6 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
    have h : (6 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (6 : ℝ) ≤ x))
    exact_mod_cast h
  have hexp1 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hlogfloor : (1 : ℝ) ≤ Real.log ((⌊x⌋₊ : ℕ) : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ ((⌊x⌋₊ : ℕ) : ℝ) by linarith)
    rwa [Real.log_exp] at h
  have hmertens := abs_le.mp (Sieve.abs_mertensS_sub_logLog_sub_const_le hfloor2)
  have hfloorlog := abs_le.mp (abs_logLog_floor_sub_le hx)
  have hC1 : 0 ≤ 2 * Sieve.mertensFirstConst + 1 / 2 := by
    have := Sieve.mertensFirstConst_nonneg
    linarith
  have hdiv : (2 * Sieve.mertensFirstConst + 1 / 2) / Real.log ((⌊x⌋₊ : ℕ) : ℝ)
      ≤ 2 * Sieve.mertensFirstConst + 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hC1, hlogfloor]
  have hpoint : zetaLinePoint (1 + 1 / Real.log x) t
      = ((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ) := by
    rw [zetaLinePoint]
    push_cast
    ring
  have hlogzeta : Real.log c
      ≤ Real.log ‖riemannZeta (zetaLinePoint (1 + 1 / Real.log x) t)‖ := by
    rw [hpoint]
    exact Real.log_le_log hc0 hz
  rw [primeCosPlusSum_eq]
  linarith [hdef.1, hdef.2, hmertens.1, hmertens.2, hfloorlog.1, hfloorlog.2, hdiv, hlogzeta]

/-- **The quantitative unpretentiousness of `μ`.**  Uniformly in the frequency, the squared
pretentious distance from the Liouville sequence to the character `p ↦ p^{it}` is
`log log x − 11 log log|t| − C`. -/
theorem exists_primeCosPlusSum_ge_logLog :
    ∃ C t₀ : ℝ, 9 ≤ t₀ ∧ ∀ x t : ℝ, Real.exp 4 ≤ x → t₀ ≤ |t| →
      Real.log (Real.log x) - 11 * Real.log (Real.log |t|) - C ≤ primeCosPlusSum t x := by
  obtain ⟨c, t₀, hc0, ht₀, hbound⟩ := exists_lower_bound_riemannZeta_near_one_line
  refine ⟨-(Real.log c) - 2 * Sieve.meisselMertensConst
      + (2 * ((2 * Sieve.mertensFirstConst + 1 / 2) + 1) + zetaDeficitConst), t₀, ht₀, ?_⟩
  intro x t hx ht
  have hexp4 : (4 : ℝ) < Real.exp 4 := by
    have h := Real.add_one_le_exp (4 : ℝ)
    linarith
  have hx4 : (4 : ℝ) < x := lt_of_lt_of_le hexp4 hx
  have hlogx : (4 : ℝ) ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 4) hx
    rwa [Real.log_exp] at h
  have hlogx0 : (0 : ℝ) < Real.log x := by linarith
  have hxexp2 : Real.exp 2 ≤ x := by
    have hle : Real.exp 2 ≤ Real.exp 4 := Real.exp_le_exp.2 (by norm_num)
    linarith
  -- the abscissa
  set σ : ℝ := 1 + 1 / Real.log x with hσdef
  have hσ1 : (1 : ℝ) ≤ σ := by
    rw [hσdef]
    have : (0 : ℝ) < 1 / Real.log x := by positivity
    linarith
  have hσ2 : σ ≤ 5 / 4 := by
    rw [hσdef]
    have : 1 / Real.log x ≤ 1 / 4 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlogx
    linarith
  -- the frequency
  have ht9 : (9 : ℝ) ≤ |t| := le_trans ht₀ ht
  have ht8 : (8 : ℝ) ≤ |t| := by linarith
  have hL2 : (2 : ℝ) ≤ Real.log |t| := two_le_log_of_eight_le ht8
  have hL0 : (0 : ℝ) < Real.log |t| := by linarith
  have hLpow : (0 : ℝ) < (Real.log |t|) ^ 11 := by positivity
  -- the zeta lower bound at the shifted point
  have hzeta := hbound σ t hσ1 hσ2 ht
  have hcomm : ((σ : ℝ) : ℂ) + (t : ℂ) * Complex.I
      = ((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ) := by
    rw [hσdef]
    ring
  rw [hcomm] at hzeta
  have hcpos : (0 : ℝ) < c / (Real.log |t|) ^ 11 := by positivity
  have hlogc : Real.log (c / (Real.log |t|) ^ 11)
      = Real.log c - 11 * Real.log (Real.log |t|) := by
    rw [Real.log_div (ne_of_gt hc0) (by positivity), Real.log_pow]
    push_cast
    ring
  have hmain := primeCosPlusSum_ge_of_zeta_lower hcpos hxexp2 hzeta
  rw [hlogc] at hmain
  linarith [hmain]

end

end RHTower
