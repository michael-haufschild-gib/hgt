import GaloisForLFunctions.RHTower.PrimeSymbolDecoupling

/-!
# Every prime contributes at most four to the Weil prime symbol

By the decoupling of the previous module the prime side of the Weil explicit formula is a sum of
independent local contributions,

```text
P(ξ) = Σ_p X_p(θ_p),      X_p(θ) = 2 log p · L(p^{-1/2}, cos θ),   θ_p = ξ log p mod 2π,
```

and the local factor has the sharp attained range `L ∈ [-x/(1+x), x/(1-x)]` with `x = p^{-1/2}`.
Since `x/(1-x) = 1/(√p - 1)` and `x/(1+x) = 1/(√p + 1)`, the local amplitude is controlled by

```text
|X_p| ≤ 2 log p / (√p - 1).
```

That quantity is **uniformly bounded by 4**, for a one-line reason: applying `log u ≤ u - 1` to
`u = √p` gives `log p = 2 log √p ≤ 2(√p - 1)`.  So no prime, however small, contributes more than
four to the prime symbol, and the whole prime side is a sum of independent contributions each of
modulus at most `4`.

This is the uniform amplitude input for any concentration estimate on the prime symbol: together
with the exact per-prime second moment `E[L²] = x²/(2(1-x²))`, giving variance
`2(log p)²/(p-1)` at `p`, it makes the prime symbol a sum of independent, mean-zero, uniformly
bounded random variables on the Bohr torus with completely explicit constants.
-/

open Real

noncomputable section

namespace RHTower

/-- `log t ≤ 2(√t - 1)` for `t ≥ 1`: apply `log u ≤ u - 1` at `u = √t` and double. -/
theorem log_le_two_mul_sqrt_sub_one {t : ℝ} (ht : 1 ≤ t) :
    Real.log t ≤ 2 * (Real.sqrt t - 1) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hlog : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 := Real.log_le_sub_one_of_pos hs
  have hhalf : Real.log (Real.sqrt t) = Real.log t / 2 := Real.log_sqrt ht0.le
  rw [hhalf] at hlog
  linarith

/-- `√t - 1 > 0` for `t ≥ 2`. -/
theorem sqrt_sub_one_pos {t : ℝ} (ht : 2 ≤ t) : 0 < Real.sqrt t - 1 := by
  have h1 : (1 : ℝ) < Real.sqrt t := by
    have : Real.sqrt 1 < Real.sqrt t := by
      refine Real.sqrt_lt_sqrt (by norm_num) ?_
      linarith
    simpa using this
  linarith

/-- **Uniform amplitude bound.**  The local amplitude `2 log p/(√p - 1)` never exceeds `4`. -/
theorem primeAmplitude_le_four {t : ℝ} (ht : 2 ≤ t) :
    2 * Real.log t / (Real.sqrt t - 1) ≤ 4 := by
  have hpos := sqrt_sub_one_pos ht
  have hlog := log_le_two_mul_sqrt_sub_one (le_trans (by norm_num) ht)
  rw [div_le_iff₀ hpos]
  linarith

/-- The lower amplitude is dominated by the upper one, hence also at most `4`. -/
theorem primeAmplitude_lower_le_upper {t : ℝ} (ht : 2 ≤ t) :
    2 * Real.log t / (Real.sqrt t + 1) ≤ 2 * Real.log t / (Real.sqrt t - 1) := by
  have hpos := sqrt_sub_one_pos ht
  have hplus : (0 : ℝ) < Real.sqrt t + 1 := by
    have := Real.sqrt_nonneg t; linarith
  have hnum : 0 ≤ 2 * Real.log t := by
    have : (0 : ℝ) ≤ Real.log t := Real.log_nonneg (by linarith)
    linarith
  exact div_le_div_of_nonneg_left hnum hpos (by linarith)

/-- **The local contribution of a prime to the Weil prime symbol is bounded by `4` in modulus,
uniformly in the prime and in the frequency.**  Upper side. -/
theorem localContribution_le_four {t c : ℝ} (ht : 2 ≤ t) (hc : |c| ≤ 1) :
    2 * Real.log t * primeLocalSymbol (1 / Real.sqrt t) c ≤ 4 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hs1 : (1 : ℝ) < Real.sqrt t := by have := sqrt_sub_one_pos ht; linarith
  have hx : 0 < 1 / Real.sqrt t := by positivity
  have hx1 : 1 / Real.sqrt t < 1 := by
    rw [div_lt_one hs]; exact hs1
  have hL := primeLocalSymbol_le hx hx1 hc
  have hval : (1 / Real.sqrt t) / (1 - 1 / Real.sqrt t) = 1 / (Real.sqrt t - 1) := by
    have h1 : Real.sqrt t ≠ 0 := ne_of_gt hs
    have h2 : Real.sqrt t - 1 ≠ 0 := ne_of_gt (sqrt_sub_one_pos ht)
    field_simp
  rw [hval] at hL
  have hlognn : (0 : ℝ) ≤ 2 * Real.log t := by
    have : (0 : ℝ) ≤ Real.log t := Real.log_nonneg (by linarith)
    linarith
  have hstep : 2 * Real.log t * primeLocalSymbol (1 / Real.sqrt t) c
      ≤ 2 * Real.log t * (1 / (Real.sqrt t - 1)) := by
    exact mul_le_mul_of_nonneg_left hL hlognn
  have hfin : 2 * Real.log t * (1 / (Real.sqrt t - 1)) ≤ 4 := by
    have := primeAmplitude_le_four ht
    rw [div_eq_mul_one_div] at this
    linarith
  linarith

/-- Lower side of the same bound. -/
theorem neg_four_le_localContribution {t c : ℝ} (ht : 2 ≤ t) (hc : |c| ≤ 1) :
    -4 ≤ 2 * Real.log t * primeLocalSymbol (1 / Real.sqrt t) c := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hs1 : (1 : ℝ) < Real.sqrt t := by have := sqrt_sub_one_pos ht; linarith
  have hx : 0 < 1 / Real.sqrt t := by positivity
  have hx1 : 1 / Real.sqrt t < 1 := by rw [div_lt_one hs]; exact hs1
  have hL := primeLocalSymbol_ge hx hx1 hc
  have hval : (1 / Real.sqrt t) / (1 + 1 / Real.sqrt t) = 1 / (Real.sqrt t + 1) := by
    have h1 : Real.sqrt t ≠ 0 := ne_of_gt hs
    have h2 : Real.sqrt t + 1 ≠ 0 := by positivity
    field_simp
  rw [hval] at hL
  have hlognn : (0 : ℝ) ≤ 2 * Real.log t := by
    have : (0 : ℝ) ≤ Real.log t := Real.log_nonneg (by linarith)
    linarith
  have hstep : 2 * Real.log t * (-(1 / (Real.sqrt t + 1)))
      ≤ 2 * Real.log t * primeLocalSymbol (1 / Real.sqrt t) c :=
    mul_le_mul_of_nonneg_left hL hlognn
  have hfin : -4 ≤ 2 * Real.log t * (-(1 / (Real.sqrt t + 1))) := by
    have h1 := primeAmplitude_lower_le_upper ht
    have h2 := primeAmplitude_le_four ht
    have h3 : 2 * Real.log t / (Real.sqrt t + 1) ≤ 4 := le_trans h1 h2
    rw [div_eq_mul_one_div] at h3
    linarith
  linarith

end RHTower
