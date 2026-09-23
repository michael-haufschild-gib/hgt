import GaloisForLFunctions.RHTower.ZetaLineLowerBound
import GaloisForLFunctions.RHTower.ZetaOneLineLogPowerLowerBound

/-!
# The pretentious distance at every frequency

`ZetaLineLowerBound.primeCosPlusSum_ge_low_freq` converts a lower bound for `ζ` on the shifted line
into a lower bound for the positive prime cosine sum — the pretentious distance of `μ` to the
archimedean character — but it carries the frequency restriction of the bound it consumes.  The
restriction is not used anywhere in the argument: the only place the frequency enters is the value
of `ζ` at the single point `1 + 1/log x + it`.

Stating the theorem with that value as the hypothesis therefore removes the restriction, and feeding
it the corpus's own power-of-log lower bound
`ZetaOneLineLogPowerLowerBound.exists_lower_bound_riemannZeta_near_one_line` gives the distance at
*every* frequency, with the classical shape

```
    D(μ, n^{it}; x)²  ≥  log log x − 11 log log|t| − C .
```

* `primeCosPlusSum_ge_of_zeta_lower_primeCosSumHighFreq`;
* `exists_primeCosPlusSum_ge_high_freq`.
-/

namespace RHTower

open Complex

noncomputable section

/-- **The positive prime cosine sum, bounded by the value of `ζ` at the shifted point.**  No
restriction on the frequency. -/
theorem primeCosPlusSum_ge_of_zeta_lower_primeCosSumHighFreq {c : ℝ} (hc0 : 0 < c) {x t : ℝ}
    (hx : Real.exp 2 ≤ x)
    (hzeta : c ≤ ‖riemannZeta (((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ))‖) :
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
  have hexp1 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hlogfloor : (1 : ℝ) ≤ Real.log ((⌊x⌋₊ : ℕ) : ℝ) := by
    have hfloor6 : (6 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
      have h : (6 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (6 : ℝ) ≤ x))
      exact_mod_cast h
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
    exact Real.log_le_log hc0 hzeta
  rw [primeCosPlusSum_eq]
  linarith [hdef.1, hdef.2, hmertens.1, hmertens.2, hfloorlog.1, hfloorlog.2, hdiv, hlogzeta]

/-- **The pretentious distance at every frequency.**  Over the whole frequency range the positive
prime cosine sum keeps its full harmonic size up to `11 log log|t|`, which is the classical shape
Halász's theorem consumes. -/
theorem exists_primeCosPlusSum_ge_high_freq :
    ∃ C t₀ : ℝ, 9 ≤ t₀ ∧ ∀ x t : ℝ, Real.exp 4 ≤ x → t₀ ≤ |t| →
      Real.log (Real.log x) - 11 * Real.log (Real.log |t|) - C ≤ primeCosPlusSum t x := by
  obtain ⟨c, t₀, hc0, ht₀, hT⟩ := exists_lower_bound_riemannZeta_near_one_line
  refine ⟨(2 * ((2 * Sieve.mertensFirstConst + 1 / 2) + 1) + zetaDeficitConst)
      - Real.log c - 2 * Sieve.meisselMertensConst, t₀, ht₀, ?_⟩
  intro x t hx ht
  have hexp24 : Real.exp 2 ≤ Real.exp 4 := Real.exp_le_exp.mpr (by norm_num)
  have hx2 : Real.exp 2 ≤ x := le_trans hexp24 hx
  have hlogx4 : (4 : ℝ) ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 4) hx
    rwa [Real.log_exp] at h
  have hlogx0 : (0 : ℝ) < Real.log x := by linarith
  have hσ1 : (1 : ℝ) ≤ 1 + 1 / Real.log x := by
    have : (0 : ℝ) < 1 / Real.log x := by positivity
    linarith
  have hσ2 : 1 + 1 / Real.log x ≤ 5 / 4 := by
    have h : 1 / Real.log x ≤ 1 / 4 := by
      rw [div_le_div_iff₀ hlogx0 (by norm_num)]
      linarith
    linarith
  have ht9 : (9 : ℝ) ≤ |t| := le_trans ht₀ ht
  have hlogt : (2 : ℝ) ≤ Real.log |t| := two_le_log_of_eight_le (by linarith)
  have hlogt0 : (0 : ℝ) < Real.log |t| := by linarith
  have hpow0 : (0 : ℝ) < (Real.log |t|) ^ (11 : ℕ) := by positivity
  have hzeta := hT (1 + 1 / Real.log x) t hσ1 hσ2 ht
  have hpt : ((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I
      = ((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ) := by ring
  rw [hpt] at hzeta
  have hcpos : (0 : ℝ) < c / (Real.log |t|) ^ (11 : ℕ) := by positivity
  have hmain := primeCosPlusSum_ge_of_zeta_lower_primeCosSumHighFreq hcpos hx2 hzeta
  have hlogdiv : Real.log (c / (Real.log |t|) ^ (11 : ℕ))
      = Real.log c - 11 * Real.log (Real.log |t|) := by
    rw [Real.log_div (ne_of_gt hc0) (ne_of_gt hpow0), Real.log_pow]
    push_cast
    ring
  rw [hlogdiv] at hmain
  linarith [hmain]

end

end RHTower
