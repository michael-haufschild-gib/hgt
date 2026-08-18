import GaloisForLFunctions.RHTower.Sieve.DirichletPowerMeasure

/-!
# The balanced large-values estimate for a prime-supported polynomial

Choosing the power so that the lengthened polynomial `N^k` does not exceed the frequency range `T`
collapses the mean-value factor to `T log T`, and the estimate becomes

`|{|F| ≥ V} ∩ [−T,T]| ≤ 10·T·(1 + log T)·(k·G/V²)^k`,   `G = ∑|a_n|²`.

The whole dependence on the length is now inside `k`, which the argument chooses as
`⌊log T / log N⌋`.  This is the shape a large-values argument for prime polynomials consumes: the
measure decays geometrically in `k` as soon as `V² > k·G`.
-/

namespace RHTower.Sieve

open MeasureTheory

/-- **The balanced form of the prime-supported large-values estimate.** -/
theorem volume_largeValues_prime_balanced {k N : ℕ} (hk : 1 ≤ k) (hN : 2 ≤ N)
    (a : Fin N → ℂ) (hsupp : ∀ n : Fin N, a n ≠ 0 → Nat.Prime ((n : ℕ) + 1))
    {T V : ℝ} (hV : 0 < V) (hNk : ((N ^ k : ℕ) : ℝ) ≤ T) :
    volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly N a t‖}
      ≤ 10 * T * (1 + Real.log T)
          * (((k : ℝ) * (∑ n : Fin N, ‖a n‖ ^ 2)) / V ^ 2) ^ k := by
  have hNk2 : (2 : ℕ) ≤ N ^ k := le_trans hN (Nat.le_self_pow (by omega) N)
  have hNkR : (2 : ℝ) ≤ ((N ^ k : ℕ) : ℝ) := by exact_mod_cast hNk2
  have hT2 : (2 : ℝ) ≤ T := le_trans hNkR hNk
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hlogT : (0 : ℝ) ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogNk : Real.log ((N ^ k : ℕ) : ℝ) ≤ Real.log T :=
    Real.log_le_log (by linarith) hNk
  have hbase := volume_largeValues_pow_symm_le_of_prime_support k N hk a hsupp hT0 hV.le
  have hVk : (0 : ℝ) < V ^ (2 * k) := by positivity
  have hG0 : (0 : ℝ) ≤ ∑ n : Fin N, ‖a n‖ ^ 2 := by positivity
  have hmv : (T + 4 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log ((N ^ k : ℕ) : ℝ)))
      ≤ 5 * T * (1 + Real.log T) := by
    have h1 : (0 : ℝ) ≤ 1 + Real.log ((N ^ k : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ Real.log ((N ^ k : ℕ) : ℝ) := Real.log_nonneg (by linarith)
      linarith
    have h2 : ((N ^ k : ℕ) : ℝ) * (1 + Real.log ((N ^ k : ℕ) : ℝ))
        ≤ T * (1 + Real.log T) := by
      refine mul_le_mul hNk (by linarith) h1 (by linarith)
    nlinarith [hT2, hlogT, h2]
  have hstep : V ^ (2 * k) * volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly N a t‖}
      ≤ 2 * (5 * T * (1 + Real.log T) * ((k : ℝ) ^ k * (∑ n : Fin N, ‖a n‖ ^ 2) ^ k)) := by
    refine hbase.trans ?_
    have hcoef : (0 : ℝ) ≤ (k : ℝ) ^ k * (∑ n : Fin N, ‖a n‖ ^ 2) ^ k := by positivity
    have := mul_le_mul_of_nonneg_right hmv hcoef
    linarith
  have hexp : (((k : ℝ) * (∑ n : Fin N, ‖a n‖ ^ 2)) / V ^ 2) ^ k
      = ((k : ℝ) ^ k * (∑ n : Fin N, ‖a n‖ ^ 2) ^ k) / V ^ (2 * k) := by
    rw [div_pow, mul_pow, ← pow_mul, mul_comm 2 k]
  rw [hexp, show (10 : ℝ) * T * (1 + Real.log T)
        * (((k : ℝ) ^ k * (∑ n : Fin N, ‖a n‖ ^ 2) ^ k) / V ^ (2 * k))
      = (10 * T * (1 + Real.log T) * ((k : ℝ) ^ k * (∑ n : Fin N, ‖a n‖ ^ 2) ^ k))
        / V ^ (2 * k) from by ring, le_div_iff₀ hVk]
  have hmeas : (0 : ℝ) ≤ volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly N a t‖} :=
    ENNReal.toReal_nonneg
  nlinarith [hstep, hmeas]

end RHTower.Sieve
