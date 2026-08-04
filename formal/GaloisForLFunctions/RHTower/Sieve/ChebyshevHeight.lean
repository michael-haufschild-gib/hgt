import GaloisForLFunctions.RHTower.Sieve.ChebyshevContourData

/-!
# The balanced truncation height

The Chebyshev contour is truncated at

    T(x) = exp((log x)^{1/10}),

so that the strip half-width is `A/log⁹T(x) = A/(log x)^{9/10}` and the saving on the left edge is
`exp(-A(log x)^{1/10})`.  The height beats every power of the logarithm and is beaten by every power
of `x`; that is exactly what the two competing edges need.

The exponent `1/10` is forced by the ninth power in the zero-free region: any smaller exponent makes
the left edge too weak, any larger one makes the right edge and the truncation error too large.
-/

namespace RHTower.Sieve

open Filter Topology

/-- The balanced truncation height attached to a cutoff of size `x`. -/
noncomputable def chebHeight (x : ℝ) : ℝ := Real.exp ((Real.log x) ^ ((1 : ℝ) / 10))

/-- The logarithm of the height is the fractional power of the logarithm. -/
theorem log_chebHeight (x : ℝ) :
    Real.log (chebHeight x) = (Real.log x) ^ ((1 : ℝ) / 10) := by
  rw [chebHeight, Real.log_exp]

/-- The ninth power of that logarithm. -/
theorem log_chebHeight_pow_nine {x : ℝ} (hx : 0 ≤ Real.log x) :
    Real.log (chebHeight x) ^ 9 = (Real.log x) ^ ((9 : ℝ) / 10) := by
  rw [log_chebHeight, ← Real.rpow_natCast ((Real.log x) ^ ((1 : ℝ) / 10)) 9,
    ← Real.rpow_mul hx]
  norm_num

/-- The height clears the threshold of the strip estimate. -/
theorem nine_le_chebHeight {x : ℝ} (hx : (Real.log 9) ^ (10 : ℕ) ≤ Real.log x) :
    9 ≤ chebHeight x := by
  have h9 : (0 : ℝ) < Real.log 9 := Real.log_pos (by norm_num)
  have hx0 : (0 : ℝ) ≤ Real.log x := le_trans (by positivity) hx
  have hstep : Real.log 9 ≤ (Real.log x) ^ ((1 : ℝ) / 10) := by
    have hbase : ((Real.log 9) ^ (10 : ℕ)) ^ ((1 : ℝ) / 10) ≤ (Real.log x) ^ ((1 : ℝ) / 10) :=
      Real.rpow_le_rpow (by positivity) hx (by norm_num)
    have hid : ((Real.log 9) ^ (10 : ℕ)) ^ ((1 : ℝ) / 10) = Real.log 9 := by
      rw [← Real.rpow_natCast (Real.log 9) 10, ← Real.rpow_mul h9.le]
      norm_num
    rwa [hid] at hbase
  calc (9 : ℝ) = Real.exp (Real.log 9) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp ((Real.log x) ^ ((1 : ℝ) / 10)) := Real.exp_le_exp.2 hstep
    _ = chebHeight x := rfl

/-- The height grows without bound. -/
theorem tendsto_chebHeight : Tendsto chebHeight atTop atTop := by
  have hlog : Tendsto (fun x : ℝ => Real.log x) atTop atTop := Real.tendsto_log_atTop
  have hpow : Tendsto (fun u : ℝ => u ^ ((1 : ℝ) / 10)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  exact Real.tendsto_exp_atTop.comp (hpow.comp hlog)

end RHTower.Sieve
