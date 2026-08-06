import GaloisForLFunctions.RHTower.Sieve.ChebyshevKappaOneCoeff

/-!
# The collapse: from the shape to a bare exponential

Two steps take the shaped bound to its final form.

First, the coefficient `1 + W` — one from the pole term, `W` from the smoothing's price — meets the
common factor `chebFactorOne Z`.  The constant summand keeps the full `exp(-√(log Z)/80000)`, and
the price summand is exactly what `price_mul_factor_le` handles, so together they are
`(3 + 27Cm)·exp(-√(log Z)/240000)`.

Second, the polynomial `log²T = 4 log Z = 4(√(log Z))²` is absorbed at the cost of halving the
exponent once more, by `sq_le_exp_div_gen` at `k = 480000`.  That halving is the last one; the
capstone's exponent is `1/480000`.
-/

namespace RHTower.Sieve

/-- **The coefficient meets the common factor.** -/
theorem one_add_width_mul_factor_le {Cm N Z : ℝ} (hCm : 0 ≤ Cm) (hN0 : 0 < N) (hNZ : N ≤ Z) :
    (1 + Cm * (9 * Real.exp (Real.sqrt (Real.log N) / 120000))) * chebFactorOne Z
      ≤ (3 + 27 * Cm) * Real.exp (-(Real.sqrt (Real.log Z) / 240000)) := by
  have hs : (0 : ℝ) ≤ Real.sqrt (Real.log Z) := Real.sqrt_nonneg _
  -- the constant summand
  have h1 : chebFactorOne Z ≤ 3 * Real.exp (-(Real.sqrt (Real.log Z) / 240000)) := by
    rw [chebFactorOne]
    have := Real.exp_le_exp.mpr
      (by linarith : -(Real.sqrt (Real.log Z) / 80000)
        ≤ -(Real.sqrt (Real.log Z) / 240000))
    linarith [this]
  -- the price summand
  have h2 : 9 * Real.exp (Real.sqrt (Real.log N) / 120000) * chebFactorOne Z
      ≤ 27 * Real.exp (-(Real.sqrt (Real.log Z) / 240000)) := price_mul_factor_le hN0 hNZ
  have h3 : Cm * (9 * Real.exp (Real.sqrt (Real.log N) / 120000) * chebFactorOne Z)
      ≤ Cm * (27 * Real.exp (-(Real.sqrt (Real.log Z) / 240000))) :=
    mul_le_mul_of_nonneg_left h2 hCm
  nlinarith [h1, h3]

/-- **The polynomial is absorbed**, at the cost of one last halving of the exponent. -/
theorem sq_mul_exp_neg_le {s : ℝ} (hs : 0 ≤ s) :
    s ^ 2 * Real.exp (-(s / 240000))
      ≤ 4 * 480000 ^ 2 * Real.exp (-(s / 480000)) := by
  have hbound := sq_le_exp_div_gen hs (k := 480000) (by norm_num)
  have hexp : Real.exp (s / 480000) * Real.exp (-(s / 240000))
      = Real.exp (-(s / 480000)) := by
    rw [← Real.exp_add]
    ring_nf
  have hpos : (0 : ℝ) < Real.exp (-(s / 240000)) := Real.exp_pos _
  calc s ^ 2 * Real.exp (-(s / 240000))
      ≤ 4 * 480000 ^ 2 * Real.exp (s / 480000) * Real.exp (-(s / 240000)) :=
        mul_le_mul_of_nonneg_right hbound hpos.le
    _ = 4 * 480000 ^ 2 * (Real.exp (s / 480000) * Real.exp (-(s / 240000))) := by ring
    _ = 4 * 480000 ^ 2 * Real.exp (-(s / 480000)) := by rw [hexp]

/-- The truncation height's logarithm, squared, is four times the cutoff's. -/
theorem sq_log_chebHeightOne (Z : ℝ) (hZ : 0 ≤ Real.log Z) :
    Real.log (chebHeightOne Z) ^ 2 = 4 * Real.log Z := by
  rw [log_chebHeightOne]
  have hsq : Real.sqrt (Real.log Z) * Real.sqrt (Real.log Z) = Real.log Z :=
    Real.mul_self_sqrt hZ
  nlinarith [hsq]

end RHTower.Sieve
