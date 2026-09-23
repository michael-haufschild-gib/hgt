import GaloisForLFunctions.RHTower.Sieve.MaynardFixedPolylogEnergy

namespace RHTower.Sieve

open Finset

noncomputable section

/-! # Fixed-polylog energy for the unraised Type-II factor

The `T₁` argument leaves its long factor unraised. Divisor-bounded coefficients still have
intrinsic Hilbert mass bounded by length times a fixed polylogarithm. Keeping that polylogarithm
explicit, rather than replacing it by a positive power of `T`, preserves the endpoint exponent. -/

/-- Literal divisor-bounded coefficients on `[A,2A]` have unraised convolution energy
`A` times an explicit fixed polylogarithm of the ambient height. -/
theorem matomakiTeravainen_unraised_energy_le_polylog
    {T C : ℝ} (hT : 1 ≤ T) (hC : 0 ≤ C)
    {N A w : ℕ} (hN : 1 ≤ N) (hNA : N ≤ 2 * A) (hAT : (A : ℝ) ≤ T)
    (a : Fin N → ℂ)
    (hpoint : ∀ n : Fin N,
      ‖a n‖ ≤ C * ((((n : ℕ) + 1).divisors.card : ℝ) ^ w)) :
    ∑ n : Fin (N ^ (1 : ℕ)), ‖convPow N 1 a n‖ ^ (2 : ℕ) ≤
      (2 * C ^ (2 : ℕ) *
        (2 * (1 + |Real.log T|)) ^ (2 ^ (2 * (w + 1)) - 1)) * (A : ℝ) := by
  let E : ℕ := 2 ^ (2 * (w + 1)) - 1
  have hbase := sum_normSq_convPow_le_fixed_polylog hN hC a hpoint (ell := 1)
  have hNAR : (N : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast hNA
  have hNAT : (N : ℝ) ≤ 2 * T := by
    calc
      (N : ℝ) ≤ 2 * (A : ℝ) := hNAR
      _ ≤ 2 * T := by gcongr
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hlogN : Real.log (N : ℝ) ≤ Real.log (2 * T) :=
    Real.log_le_log hNpos hNAT
  have hlogTwo : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogMul : Real.log (2 * T) = Real.log 2 + Real.log T := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hTpos.ne']
  have hlogTAbs : Real.log T ≤ |Real.log T| := le_abs_self _
  have hlogBound : 1 + Real.log (N : ℝ) ≤ 2 * (1 + |Real.log T|) := by
    rw [hlogMul] at hlogN
    linarith [abs_nonneg (Real.log T)]
  have hlogNonneg : 0 ≤ 1 + Real.log (N : ℝ) := by
    have hlogN0 : 0 ≤ Real.log (N : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast hN)
    linarith
  have hpow :
      (1 + Real.log (N : ℝ)) ^ E ≤
        (2 * (1 + |Real.log T|)) ^ E :=
    pow_le_pow_left₀ hlogNonneg hlogBound E
  have hC2 : 0 ≤ C ^ (2 : ℕ) := sq_nonneg C
  have hpoly0 : 0 ≤ (2 * (1 + |Real.log T|)) ^ E := by positivity
  calc
    ∑ n : Fin (N ^ (1 : ℕ)), ‖convPow N 1 a n‖ ^ (2 : ℕ)
        ≤ C ^ (2 : ℕ) * ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ E) := by
          simpa only [pow_one, Nat.cast_id, mul_one, E, Nat.cast_pow] using hbase
    _ ≤ C ^ (2 : ℕ) * ((N : ℝ) * (2 * (1 + |Real.log T|)) ^ E) := by
      gcongr
    _ ≤ C ^ (2 : ℕ) * ((2 * (A : ℝ)) * (2 * (1 + |Real.log T|)) ^ E) := by
      gcongr
    _ = (2 * C ^ (2 : ℕ) * (2 * (1 + |Real.log T|)) ^ E) * (A : ℝ) := by ring
    _ = (2 * C ^ (2 : ℕ) *
        (2 * (1 + |Real.log T|)) ^ (2 ^ (2 * (w + 1)) - 1)) * (A : ℝ) := by
      rfl

end

end RHTower.Sieve
