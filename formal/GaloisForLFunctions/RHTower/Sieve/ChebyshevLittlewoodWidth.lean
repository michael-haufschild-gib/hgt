import GaloisForLFunctions.RHTower.Sieve.ChebyshevWidthOne
import GaloisForLFunctions.RHTower.Sieve.ChebyshevBalanceOne
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLittlewoodCollapse

/-!
# The smoothing width at depth `A`

The smoothing ratio must be balanced against the saving.  At depth `A` the edge factor is
`3exp(-√A·√(log Z)/2)` and the collapse leaves a third of that exponent, so the price of the
smoothing, which is the *square* of the ratio, may be at most `exp(√A·√(log N)/6)`:

```text
chebRatioLw A N = exp(√A·√(log N)/12) ,    chebWidthLw A N = N / chebRatioLw A N .
```

At `A = 1/40000` the exponent is `√(log N)/2400000`, where the exponent-one chain uses
`√(log N)/240000`; the difference is that its height is not re-optimised, so its edge factor is ten
times weaker.
-/

namespace RHTower.Sieve

/-- The smoothing ratio balanced against the depth-`A` saving. -/
noncomputable def chebRatioLw (A N : ℝ) : ℝ :=
  Real.exp (Real.sqrt A * Real.sqrt (Real.log N) / 12)

/-- The smoothing width at depth `A`. -/
noncomputable def chebWidthLw (A N : ℝ) : ℝ := N / chebRatioLw A N

theorem chebRatioLw_pos (A N : ℝ) : 0 < chebRatioLw A N := Real.exp_pos _

theorem one_le_chebRatioLw (A N : ℝ) : 1 ≤ chebRatioLw A N := by
  rw [chebRatioLw]
  exact Real.one_le_exp (by positivity)

theorem chebWidthLw_le {A N : ℝ} (hN0 : 0 ≤ N) : chebWidthLw A N ≤ N := by
  rw [chebWidthLw]
  exact div_le_self hN0 (one_le_chebRatioLw A N)

theorem chebWidthLw_nonneg {A N : ℝ} (hN0 : 0 ≤ N) : 0 ≤ chebWidthLw A N := by
  rw [chebWidthLw]
  exact div_nonneg hN0 (chebRatioLw_pos A N).le

theorem div_chebWidthLw {A N : ℝ} (hN0 : 0 < N) : N / chebWidthLw A N = chebRatioLw A N := by
  rw [chebWidthLw]
  field_simp

theorem chebWidthLw_eq (A N : ℝ) :
    chebWidthLw A N = N * Real.exp (-(Real.sqrt A * Real.sqrt (Real.log N) / 12)) := by
  rw [chebWidthLw, chebRatioLw, Real.exp_neg, div_eq_mul_inv]

theorem one_le_chebWidthLw {A N : ℝ} (hAN : A ≤ Real.log N) (hN0 : 0 < N)
    (hN : 1 ≤ Real.log N) : 1 ≤ chebWidthLw A N := by
  rw [chebWidthLw, le_div_iff₀ (chebRatioLw_pos A N), one_mul, chebRatioLw]
  have hsA : Real.sqrt A ≤ Real.sqrt (Real.log N) := Real.sqrt_le_sqrt hAN
  have hsq : Real.sqrt (Real.log N) * Real.sqrt (Real.log N) = Real.log N :=
    Real.mul_self_sqrt (by linarith)
  have hnn : (0 : ℝ) ≤ Real.sqrt (Real.log N) := Real.sqrt_nonneg _
  have hle : Real.sqrt A * Real.sqrt (Real.log N) / 12 ≤ Real.log N := by
    nlinarith [hsA, hsq, hnn]
  calc Real.exp (Real.sqrt A * Real.sqrt (Real.log N) / 12) ≤ Real.exp (Real.log N) :=
        Real.exp_le_exp.mpr hle
    _ = N := Real.exp_log hN0

/-- The square of the smoothing ratio, as an exponential. -/
theorem sq_chebRatioLw_le (A N : ℝ) :
    (chebRatioLw A N + 2) ^ 2
      ≤ 9 * Real.exp (Real.sqrt A * Real.sqrt (Real.log N) / 6) := by
  have h1 : (1 : ℝ) ≤ chebRatioLw A N := one_le_chebRatioLw A N
  have hsq : chebRatioLw A N ^ 2
      = Real.exp (Real.sqrt A * Real.sqrt (Real.log N) / 6) := by
    rw [chebRatioLw, sq, ← Real.exp_add]
    ring_nf
  calc (chebRatioLw A N + 2) ^ 2 ≤ (3 * chebRatioLw A N) ^ 2 := by nlinarith
    _ = 9 * chebRatioLw A N ^ 2 := by ring
    _ = 9 * Real.exp (Real.sqrt A * Real.sqrt (Real.log N) / 6) := by rw [hsq]

/-- **The price of the smoothing, against an arbitrary bound on the ratio.**  `width_price_le` is
the case where the bound is the exponent-one exponential. -/
theorem width_price_le_gen {N H L Cm B : ℝ} (hH1 : 1 ≤ H) (hN0 : 0 ≤ N) (hL : N / H ≤ L)
    (hCm : 0 ≤ Cm) (hLb : (L + 2) ^ 2 ≤ B) :
    Cm / H ^ 2 * (N + H + 1) ^ 2 ≤ Cm * B := by
  refine le_trans (sq_width_factor_le hH1 hN0 hL hCm) ?_
  exact mul_le_mul_of_nonneg_left hLb hCm

/-- **The smoothing price against the depth-`A` edge factor.**  A third of the factor's exponent
survives. -/
theorem one_add_width_mul_factor_le_lw {A Cm N Z : ℝ} (hA : 0 ≤ A) (hCm : 0 ≤ Cm)
    (hN0 : 0 < N) (hNZ : N ≤ Z) :
    (1 + Cm * (9 * Real.exp (Real.sqrt A * Real.sqrt (Real.log N) / 6))) * chebFactorLw A Z
      ≤ (3 + 27 * Cm) * Real.exp (-(Real.sqrt A * Real.sqrt (Real.log Z) / 6)) := by
  have hsA : (0 : ℝ) ≤ Real.sqrt A := Real.sqrt_nonneg _
  have hsZ : (0 : ℝ) ≤ Real.sqrt (Real.log Z) := Real.sqrt_nonneg _
  have hlogNZ : Real.log N ≤ Real.log Z := Real.log_le_log hN0 hNZ
  have hsNZ : Real.sqrt (Real.log N) ≤ Real.sqrt (Real.log Z) := Real.sqrt_le_sqrt hlogNZ
  have hfac : chebFactorLw A Z = 3 * Real.exp (-(Real.sqrt (A * Real.log Z) / 2)) := rfl
  have hsplit : Real.sqrt (A * Real.log Z) = Real.sqrt A * Real.sqrt (Real.log Z) :=
    Real.sqrt_mul hA _
  rw [hfac, hsplit]
  -- the constant summand
  have h1 : (3 : ℝ) * Real.exp (-(Real.sqrt A * Real.sqrt (Real.log Z) / 2))
      ≤ 3 * Real.exp (-(Real.sqrt A * Real.sqrt (Real.log Z) / 6)) := by
    have := Real.exp_le_exp.mpr
      (by nlinarith [hsA, hsZ] :
        -(Real.sqrt A * Real.sqrt (Real.log Z) / 2)
          ≤ -(Real.sqrt A * Real.sqrt (Real.log Z) / 6))
    linarith
  -- the price summand
  have h2 : Cm * (9 * Real.exp (Real.sqrt A * Real.sqrt (Real.log N) / 6))
        * (3 * Real.exp (-(Real.sqrt A * Real.sqrt (Real.log Z) / 2)))
      ≤ 27 * Cm * Real.exp (-(Real.sqrt A * Real.sqrt (Real.log Z) / 6)) := by
    have hmerge : Real.exp (Real.sqrt A * Real.sqrt (Real.log N) / 6)
          * Real.exp (-(Real.sqrt A * Real.sqrt (Real.log Z) / 2))
        = Real.exp (Real.sqrt A * Real.sqrt (Real.log N) / 6
            - Real.sqrt A * Real.sqrt (Real.log Z) / 2) := by
      rw [← Real.exp_add]; ring_nf
    have hexp : Real.exp (Real.sqrt A * Real.sqrt (Real.log N) / 6
          - Real.sqrt A * Real.sqrt (Real.log Z) / 2)
        ≤ Real.exp (-(Real.sqrt A * Real.sqrt (Real.log Z) / 6)) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hsA, hsNZ, hsZ]
    have hstep : Real.exp (Real.sqrt A * Real.sqrt (Real.log N) / 6)
          * Real.exp (-(Real.sqrt A * Real.sqrt (Real.log Z) / 2))
        ≤ Real.exp (-(Real.sqrt A * Real.sqrt (Real.log Z) / 6)) := by
      rw [hmerge]; exact hexp
    nlinarith [hstep, hCm, Real.exp_pos (-(Real.sqrt A * Real.sqrt (Real.log Z) / 6))]
  nlinarith [h1, h2]

end RHTower.Sieve
