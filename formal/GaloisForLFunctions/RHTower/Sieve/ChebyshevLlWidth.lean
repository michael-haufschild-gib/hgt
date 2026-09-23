import GaloisForLFunctions.RHTower.Sieve.ChebyshevLittlewoodWidth
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLlShape

/-!
# The smoothing width when the depth grows with the height

The smoothing ratio must be balanced against the saving, and the saving is now
`chebSavingLl c N = ½√(c·log N·log log N)`.  The collapse leaves a sixth of the factor's exponent,
so the ratio may be at most a sixth of the saving in the exponent:

```text
chebRatioLl c N = exp(chebSavingLl c N/6) ,      chebWidthLl c N = N / chebRatioLl c N .
```

The width is therefore `N·exp(-c'√(log N·log log N))`, narrower than the fixed-depth
`N·exp(-c'√(log N))` by exactly the Littlewood factor.
-/

namespace RHTower.Sieve

/-- The smoothing ratio balanced against the saving. -/
noncomputable def chebRatioLl (c N : ℝ) : ℝ := Real.exp (chebSavingLl c N / 6)

/-- The smoothing width. -/
noncomputable def chebWidthLl (c N : ℝ) : ℝ := N / chebRatioLl c N

theorem chebRatioLl_pos (c N : ℝ) : 0 < chebRatioLl c N := Real.exp_pos _

theorem one_le_chebRatioLl (c N : ℝ) : 1 ≤ chebRatioLl c N := by
  rw [chebRatioLl]
  exact Real.one_le_exp (by positivity [chebSavingLl_nonneg c N])

theorem chebWidthLl_le {c N : ℝ} (hN0 : 0 ≤ N) : chebWidthLl c N ≤ N := by
  rw [chebWidthLl]
  exact div_le_self hN0 (one_le_chebRatioLl c N)

theorem chebWidthLl_nonneg {c N : ℝ} (hN0 : 0 ≤ N) : 0 ≤ chebWidthLl c N := by
  rw [chebWidthLl]
  exact div_nonneg hN0 (chebRatioLl_pos c N).le

theorem div_chebWidthLl {c N : ℝ} (hN0 : 0 < N) : N / chebWidthLl c N = chebRatioLl c N := by
  rw [chebWidthLl]
  field_simp

/-- The balanced quantity never exceeds `log²N`, so the saving never exceeds `½log N`. -/
theorem chebSavingLl_le_half_log {c N : ℝ} (hc : c ≤ 1)
    (hN1 : 1 ≤ Real.log N) : chebSavingLl c N ≤ Real.log N / 2 := by
  have hLL : Real.log (Real.log N) ≤ Real.log N := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < Real.log N by linarith)]
  have hLL0 : (0 : ℝ) ≤ Real.log (Real.log N) := Real.log_nonneg hN1
  have hQ : chebQuadLl c N ≤ Real.log N ^ (2 : ℕ) := by
    rw [chebQuadLl]
    have hstep1 : c * (Real.log N * Real.log (Real.log N))
        ≤ 1 * (Real.log N * Real.log (Real.log N)) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg (by linarith) hLL0)
    have hstep2 : Real.log N * Real.log (Real.log N) ≤ Real.log N * Real.log N :=
      mul_le_mul_of_nonneg_left hLL (by linarith)
    linarith [hstep1, hstep2]
  have hsq : Real.sqrt (chebQuadLl c N) ≤ Real.log N := by
    have h := Real.sqrt_le_sqrt hQ
    rwa [Real.sqrt_sq (by linarith)] at h
  rw [chebSavingLl]
  linarith

theorem one_le_chebWidthLl {c N : ℝ} (hc : c ≤ 1) (hN0 : 0 < N)
    (hN1 : 1 ≤ Real.log N) : 1 ≤ chebWidthLl c N := by
  rw [chebWidthLl, le_div_iff₀ (chebRatioLl_pos c N), one_mul, chebRatioLl]
  have hhalf := chebSavingLl_le_half_log hc hN1
  have hle : chebSavingLl c N / 6 ≤ Real.log N := by linarith
  calc Real.exp (chebSavingLl c N / 6) ≤ Real.exp (Real.log N) := Real.exp_le_exp.mpr hle
    _ = N := Real.exp_log hN0

/-- The square of the smoothing ratio, as an exponential. -/
theorem sq_chebRatioLl_le (c N : ℝ) :
    (chebRatioLl c N + 2) ^ (2 : ℕ) ≤ 9 * Real.exp (chebSavingLl c N / 3) := by
  have h1 : (1 : ℝ) ≤ chebRatioLl c N := one_le_chebRatioLl c N
  have hsq : chebRatioLl c N ^ (2 : ℕ) = Real.exp (chebSavingLl c N / 3) := by
    rw [chebRatioLl, sq, ← Real.exp_add]
    ring_nf
  calc (chebRatioLl c N + 2) ^ (2 : ℕ) ≤ (3 * chebRatioLl c N) ^ (2 : ℕ) := by nlinarith
    _ = 9 * chebRatioLl c N ^ (2 : ℕ) := by ring
    _ = 9 * Real.exp (chebSavingLl c N / 3) := by rw [hsq]

/-- The saving grows with the cutoff. -/
theorem chebSavingLl_mono {c N Z : ℝ} (hc0 : 0 ≤ c) (hN0 : 0 < N) (hN1 : 1 ≤ Real.log N)
    (hNZ : N ≤ Z) : chebSavingLl c N ≤ chebSavingLl c Z := by
  have hlog : Real.log N ≤ Real.log Z := Real.log_le_log hN0 hNZ
  have hLL : Real.log (Real.log N) ≤ Real.log (Real.log Z) :=
    Real.log_le_log (by linarith) hlog
  have hLL0 : (0 : ℝ) ≤ Real.log (Real.log N) := Real.log_nonneg hN1
  have hQ : chebQuadLl c N ≤ chebQuadLl c Z := by
    rw [chebQuadLl, chebQuadLl]
    have hprod : Real.log N * Real.log (Real.log N) ≤ Real.log Z * Real.log (Real.log Z) := by
      nlinarith [hlog, hLL, hLL0, hN1]
    exact mul_le_mul_of_nonneg_left hprod hc0
  rw [chebSavingLl, chebSavingLl]
  have := Real.sqrt_le_sqrt hQ
  linarith

/-- **The smoothing price against the edge factor.**  A sixth of the factor's exponent survives. -/
theorem one_add_width_mul_factor_le_ll {c Cm N Z : ℝ} (hc0 : 0 ≤ c) (hCm : 0 ≤ Cm)
    (hN0 : 0 < N) (hN1 : 1 ≤ Real.log N) (hNZ : N ≤ Z) :
    (1 + Cm * (9 * Real.exp (chebSavingLl c N / 3))) * chebFactorLl c Z
      ≤ (3 + 27 * Cm) * Real.exp (-(chebSavingLl c Z / 3)) := by
  have hmono : chebSavingLl c N ≤ chebSavingLl c Z := chebSavingLl_mono hc0 hN0 hN1 hNZ
  have hsZ : (0 : ℝ) ≤ chebSavingLl c Z := chebSavingLl_nonneg c Z
  have hfac : chebFactorLl c Z = 3 * Real.exp (-(chebSavingLl c Z)) := rfl
  rw [hfac]
  -- the constant summand
  have h1 : (3 : ℝ) * Real.exp (-(chebSavingLl c Z))
      ≤ 3 * Real.exp (-(chebSavingLl c Z / 3)) := by
    have := Real.exp_le_exp.mpr
      (by linarith : -(chebSavingLl c Z) ≤ -(chebSavingLl c Z / 3))
    linarith
  -- the price summand
  have h2 : Cm * (9 * Real.exp (chebSavingLl c N / 3)) * (3 * Real.exp (-(chebSavingLl c Z)))
      ≤ 27 * Cm * Real.exp (-(chebSavingLl c Z / 3)) := by
    have hmerge : Real.exp (chebSavingLl c N / 3) * Real.exp (-(chebSavingLl c Z))
        = Real.exp (chebSavingLl c N / 3 - chebSavingLl c Z) := by
      rw [← Real.exp_add]; ring_nf
    have hexp : Real.exp (chebSavingLl c N / 3 - chebSavingLl c Z)
        ≤ Real.exp (-(chebSavingLl c Z / 3)) := Real.exp_le_exp.mpr (by linarith)
    have hstep : Real.exp (chebSavingLl c N / 3) * Real.exp (-(chebSavingLl c Z))
        ≤ Real.exp (-(chebSavingLl c Z / 3)) := by rw [hmerge]; exact hexp
    nlinarith [hstep, hCm, Real.exp_pos (-(chebSavingLl c Z / 3))]
  nlinarith [h1, h2]

end RHTower.Sieve
