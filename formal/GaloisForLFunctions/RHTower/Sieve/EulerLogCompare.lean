import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries

/-!
# Comparing an Euler factor with its leading term

The Euler product for `ζ` is `exp (∑'_p −log(1 − p^{-s}))`, while the sum whose real part carries
the arithmetic information is `∑'_p p^{-s}`.  The two differ termwise by the tail of the logarithm
series, which is quadratic:

`‖−log(1 − w) − w‖ ≤ ‖w‖²/(2(1 − ‖w‖))`,  and `≤ ‖w‖²` once `‖w‖ ≤ 1/2`.

Since `‖p^{-s}‖ = p^{-σ} ≤ 1/2` for every prime and every `σ ≥ 1`, the total discrepancy is at most
`∑_p p^{-2σ} < 1`: bounded, uniformly in the frequency.  This is the step that turns a bound on
`‖ζ(σ+it)‖` into a bound on `∑_p cos(t log p)/p^σ`.
-/

namespace RHTower.Sieve

open Complex

/-- **The Euler factor differs from its leading term by a quadratic amount.** -/
theorem norm_neg_log_one_sub_sub_self_le {w : ℂ} (hw : ‖w‖ < 1) :
    ‖-Complex.log (1 - w) - w‖ ≤ ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 := by
  have hz : ‖(-w : ℂ)‖ < 1 := by rwa [norm_neg]
  have hbase := Complex.norm_log_one_add_sub_self_le hz
  rw [norm_neg] at hbase
  have hrw : (1 : ℂ) + -w = 1 - w := by ring
  rw [hrw] at hbase
  have hneg : ‖-Complex.log (1 - w) - w‖ = ‖Complex.log (1 - w) - -w‖ := by
    rw [← norm_neg]
    congr 1
    ring
  rw [hneg]
  exact hbase

/-- **The quadratic bound in the range that matters.**  For `‖w‖ ≤ 1/2` the discrepancy is at most
`‖w‖²`. -/
theorem norm_neg_log_one_sub_sub_self_le_sq {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖-Complex.log (1 - w) - w‖ ≤ ‖w‖ ^ 2 := by
  have hlt : ‖w‖ < 1 := by linarith
  refine le_trans (norm_neg_log_one_sub_sub_self_le hlt) ?_
  have hpos : (0 : ℝ) < 1 - ‖w‖ := by linarith
  have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hpos (by norm_num)]
    linarith
  have hsq : (0 : ℝ) ≤ ‖w‖ ^ 2 := sq_nonneg _
  nlinarith [hinv, hsq]

/-- Every prime power `p^{-s}` with `re s ≥ 1` has norm at most `1/2`. -/
theorem norm_prime_cpow_neg_le_half {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  have hp0 : 0 < p := by omega
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ ((-s).re) :=
    norm_natCast_cpow_of_pos hp0 (-s)
  rw [hnorm, Complex.neg_re, Real.rpow_neg (by linarith)]
  have hbase : (2 : ℝ) ^ s.re ≤ (p : ℝ) ^ s.re :=
    Real.rpow_le_rpow (by norm_num) hpR (by linarith)
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ s.re := by
    have h1 : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
    rwa [Real.rpow_one] at h1
  have hge : (2 : ℝ) ≤ (p : ℝ) ^ s.re := le_trans htwo hbase
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

/-- **The Euler factor of a prime, against its leading term.** -/
theorem norm_euler_factor_sub_le {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖-Complex.log (1 - (p : ℂ) ^ (-s)) - (p : ℂ) ^ (-s)‖
      ≤ ‖(p : ℂ) ^ (-s)‖ ^ 2 :=
  norm_neg_log_one_sub_sub_self_le_sq (norm_prime_cpow_neg_le_half hp hs)

/-- The squared norm of a prime power, as a real power. -/
theorem norm_prime_cpow_sq_eq {p : ℕ} (hp : 0 < p) (s : ℂ) :
    ‖(p : ℂ) ^ (-s)‖ ^ 2 = (p : ℝ) ^ (-(2 * s.re)) := by
  rw [norm_natCast_cpow_of_pos hp (-s), Complex.neg_re,
    ← Real.rpow_natCast ((p : ℝ) ^ (-s.re)) 2, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  ring

/-- The squared prime norms form a summable family. -/
theorem summable_prime_norm_sq {s : ℂ} (hs : 1 ≤ s.re) :
    Summable (fun p : Nat.Primes => ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2) := by
  have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 * s.re))) := by
    rw [Real.summable_nat_rpow]
    linarith
  have hsub := hnat.comp_injective Nat.Primes.coe_nat_injective
  refine hsub.congr ?_
  intro p
  exact (norm_prime_cpow_sq_eq p.2.pos s).symm

/-- The prime powers themselves are summable in the open half-plane. -/
theorem summable_prime_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℂ) ^ (-s)) := by
  refine Summable.of_norm ?_
  have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) := by
    rw [Real.summable_nat_rpow]
    linarith
  have hsub := hnat.comp_injective Nat.Primes.coe_nat_injective
  refine hsub.congr ?_
  intro p
  simp only [Function.comp_apply]
  rw [norm_natCast_cpow_of_pos p.2.pos (-s), Complex.neg_re]

/-- The Euler logarithms are summable in the open half-plane. -/
theorem summable_prime_euler_log {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s))) := by
  refine Summable.of_norm ?_
  have hbound : ∀ p : Nat.Primes,
      ‖-Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s))‖
        ≤ ‖((p : ℕ) : ℂ) ^ (-s)‖ + ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 := by
    intro p
    have hfac := norm_euler_factor_sub_le (p := (p : ℕ)) p.2.two_le (le_of_lt hs)
    have htri : ‖-Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s))‖
        ≤ ‖-Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s)) - ((p : ℕ) : ℂ) ^ (-s)‖
          + ‖((p : ℕ) : ℂ) ^ (-s)‖ := by
      have hadd := norm_add_le
        (-Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s)) - ((p : ℕ) : ℂ) ^ (-s))
        (((p : ℕ) : ℂ) ^ (-s))
      simpa using hadd
    linarith
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) hbound ?_
  exact (summable_prime_cpow hs).norm.add (summable_prime_norm_sq (le_of_lt hs))

/-- **The Euler logarithm and its leading term differ by a bounded amount.** -/
theorem norm_tsum_euler_log_sub_tsum_le {s : ℂ} (hs : 1 < s.re) :
    ‖(∑' p : Nat.Primes, -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s)))
        - ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-s)‖
      ≤ ∑' p : Nat.Primes, ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 := by
  have hlog := summable_prime_euler_log hs
  have hcpow := summable_prime_cpow hs
  have hsq := summable_prime_norm_sq (le_of_lt hs)
  rw [← hlog.tsum_sub hcpow]
  have hnorm : Summable (fun p : Nat.Primes =>
      ‖-Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s)) - ((p : ℕ) : ℂ) ^ (-s)‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => norm_euler_factor_sub_le (p := (p : ℕ)) p.2.two_le (le_of_lt hs)) hsq
  refine le_trans (norm_tsum_le_tsum_norm hnorm) ?_
  exact hnorm.tsum_le_tsum
    (fun p => norm_euler_factor_sub_le (p := (p : ℕ)) p.2.two_le (le_of_lt hs)) hsq

end RHTower.Sieve
