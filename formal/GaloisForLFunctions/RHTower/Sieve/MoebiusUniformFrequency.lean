import GaloisForLFunctions.RHTower.Sieve.MoebiusFrequencyDistance
import GaloisForLFunctions.RHTower.Sieve.ZetaPoleBoxLowerBound
import GaloisForLFunctions.RHTower.Sieve.MoebiusEulerDamping

/-!
# The Möbius distance, uniformly over a frequency range

Halász's mechanism needs the *minimum* of the distance over a whole range of frequencies, not its
value at one of them.  Two bounds now cover that range without a gap:

* `|t| ≥ 9` — the zero-free strip, losing `7 log log T`;
* `|t| ≤ 9` — the compactness bound across the pole, losing an absolute constant.

Their common form is

    ∑_{p ≤ z} cos(t log p)/p  ≥  −7 log log T − C        (|t| ≤ T),

valid as soon as `log⁹T/A ≤ log z`, and hence

    min_{|t| ≤ T} D(μ, χ_t; p ≤ z)²  ≥  log log z − 7 log log T − C.

Feeding that into the damped Euler bound gives a Dirichlet sum over squarefree `z`-smooth integers
that stays below a fixed power of `log T` *however large `z` is*, while the trivial bound grows like
`log z`.  That is the unconditional Halász saving for the Möbius function.
-/

namespace RHTower.Sieve

open Finset RHTower

/-- The strip loss, keyed on the range bound rather than on the frequency. -/
theorem log_strip_bound_range {T : ℝ} (hT : 9 ≤ T) :
    Real.log (20 / zetaLowerA * Real.log T ^ 7)
      = Real.log (20 / zetaLowerA) + 7 * Real.log (Real.log T) := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hlogT : (0 : ℝ) < Real.log T := Real.log_pos (by linarith)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  push_cast
  ring

/-- The frequency range is positive on a logarithmic scale. -/
theorem log_log_range_pos {T : ℝ} (hT : 9 ≤ T) : 0 < Real.log (Real.log T) := by
  have hexp : Real.exp 1 < T := by
    have := Real.exp_one_lt_d9
    linarith
  have h1 : (1 : ℝ) < Real.log T := by
    have := Real.log_lt_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  exact Real.log_pos h1

/-- **The strip bound at a frequency, expressed through the range bound.** -/
theorem sum_cos_div_prime_ge_range {z : ℕ} {T t : ℝ} (hz : 3 ≤ z) (hT : 9 ≤ T)
    (ht9 : 9 ≤ |t|) (htT : |t| ≤ T)
    (hzt : 1 / Real.log z ≤ zetaLowerA / Real.log T ^ 9) :
    -Real.log (20 / zetaLowerA * Real.log T ^ 7) - Real.pi ^ 2 / 6
        - 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
        - (1 + Real.log 4)
      ≤ ∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log p) / (p : ℝ) := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hlogt : (0 : ℝ) < Real.log |t| := Real.log_pos (by linarith)
  have hlogT : (0 : ℝ) < Real.log T := Real.log_pos (by linarith)
  have hmono : Real.log |t| ≤ Real.log T := Real.log_le_log (by linarith) htT
  have hpow : Real.log |t| ^ 9 ≤ Real.log T ^ 9 := by
    exact pow_le_pow_left₀ hlogt.le hmono 9
  have hquot : zetaLowerA / Real.log T ^ 9 ≤ zetaLowerA / Real.log |t| ^ 9 := by
    refine div_le_div_of_nonneg_left hA0.le (by positivity) hpow
  have hzt' : 1 / Real.log z ≤ zetaLowerA / Real.log |t| ^ 9 := le_trans hzt hquot
  have hbase := sum_cos_div_prime_ge hz ht9 hzt'
  have hloss : Real.log (20 / zetaLowerA * Real.log |t| ^ 7)
      ≤ Real.log (20 / zetaLowerA * Real.log T ^ 7) := by
    refine Real.log_le_log (by positivity) ?_
    have h7 : Real.log |t| ^ 7 ≤ Real.log T ^ 7 := pow_le_pow_left₀ hlogt.le hmono 7
    have h20 : (0 : ℝ) < 20 / zetaLowerA := by positivity
    exact mul_le_mul_of_nonneg_left h7 h20.le
  linarith

/-- **The cosine sum, uniformly over a frequency range.**  Every real frequency `|t| ≤ T` is
covered: the strip handles `|t| ≥ 9` and the pole box handles the rest. -/
theorem exists_sum_cos_div_prime_ge_uniform :
    ∃ C : ℝ, ∀ (z : ℕ) (T t : ℝ), 3 ≤ z → 9 ≤ T → |t| ≤ T →
      1 / Real.log z ≤ zetaLowerA / Real.log T ^ 9 →
      -(7 * Real.log (Real.log T)) - C
        ≤ ∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log p) / (p : ℝ) := by
  obtain ⟨C₀, hC₀⟩ := exists_sum_cos_div_prime_ge_small
  refine ⟨max C₀ (Real.log (20 / zetaLowerA) + Real.pi ^ 2 / 6
    + 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
    + (1 + Real.log 4)), ?_⟩
  intro z T t hz hT htT hzt
  rcases le_or_gt (|t|) 9 with hsmall | hlarge
  · have hbase := hC₀ z hz t hsmall
    have hpos := log_log_range_pos hT
    have hmax : C₀ ≤ max C₀ (Real.log (20 / zetaLowerA) + Real.pi ^ 2 / 6
      + 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
      + (1 + Real.log 4)) := le_max_left _ _
    linarith
  · have hbase := sum_cos_div_prime_ge_range hz hT hlarge.le htT hzt
    rw [log_strip_bound_range hT] at hbase
    have hmax : Real.log (20 / zetaLowerA) + Real.pi ^ 2 / 6
        + 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
        + (1 + Real.log 4)
        ≤ max C₀ (Real.log (20 / zetaLowerA) + Real.pi ^ 2 / 6
          + 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
          + (1 + Real.log 4)) := le_max_right _ _
    linarith

/-- **The Möbius distance, uniformly over a frequency range.**  The minimum over `|t| ≤ T` of the
squared distance is at least `log log z − 7 log log T − C`. -/
theorem exists_mulDistSqPair_ge_uniform :
    ∃ C : ℝ, ∀ (f : ℕ → ℂ) (z : ℕ) (T t : ℝ), 3 ≤ z → 9 ≤ T → |t| ≤ T →
      1 / Real.log z ≤ zetaLowerA / Real.log T ^ 9 →
      (∀ p ∈ Nat.primesLE z, f p = -1) →
      logLog z - 7 * Real.log (Real.log T) - C
        ≤ mulDistSqPair f (charFn t) (Nat.primesLE z) := by
  obtain ⟨C₁, hC₁⟩ := exists_sum_cos_div_prime_ge_uniform
  refine ⟨C₁ + mertensSecondLowerConst, ?_⟩
  intro f z T t hz hT htT hzt hf
  have hmertens : logLog z - mertensSecondLowerConst ≤ ∑ p ∈ Nat.primesLE z, 1 / (p : ℝ) :=
    le_mertensS (by omega)
  have hcos := hC₁ z T t hz hT htT hzt
  rw [mulDistSqPair_neg_one_split hf t]
  linarith

/-- **The unconditional Halász saving for the Möbius function.**  The damped Dirichlet sum over
squarefree `z`-smooth integers stays below a fixed multiple of `(log T)⁷` at every frequency
`|t| ≤ T`, uniformly in the smoothness parameter `z`; the trivial bound grows like `log z`. -/
theorem exists_norm_sum_moebius_smooth_le_uniform :
    ∃ C : ℝ, ∀ (z : ℕ) (T t : ℝ), 3 ≤ z → 9 ≤ T → |t| ≤ T →
      1 / Real.log z ≤ zetaLowerA / Real.log T ^ 9 →
      ‖∑ n ∈ (Nat.primesLE z).powerset.image (fun S => ∏ p ∈ S, p),
          ((1 / (n : ℝ) : ℝ) : ℂ)
            * (moebiusC n * Complex.exp (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I))‖
        ≤ Real.exp ((∑ p ∈ Nat.primesLE z, 1 / (p : ℝ) ^ 2) + C) * Real.log T ^ 7 := by
  obtain ⟨C₁, hC₁⟩ := exists_sum_cos_div_prime_ge_uniform
  refine ⟨C₁, ?_⟩
  intro z T t hz hT htT hzt
  have hP : ∀ p ∈ Nat.primesLE z, p.Prime := fun p hp => (Nat.mem_primesLE.1 hp).2
  have hbase := norm_sum_moebius_smooth_le_exp t hP
  have hcos := hC₁ z T t hz hT htT hzt
  have hlogT : (0 : ℝ) < Real.log T := Real.log_pos (by linarith)
  have hpow : Real.exp (7 * Real.log (Real.log T)) = Real.log T ^ 7 := by
    rw [← Real.rpow_natCast (Real.log T) 7, Real.rpow_def_of_pos hlogT]
    push_cast
    ring_nf
  have hstep : Real.exp ((∑ p ∈ Nat.primesLE z, 1 / (p : ℝ) ^ 2)
      - ∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ))
      ≤ Real.exp ((∑ p ∈ Nat.primesLE z, 1 / (p : ℝ) ^ 2) + C₁
          + 7 * Real.log (Real.log T)) := by
    refine Real.exp_le_exp.2 ?_
    linarith
  refine le_trans hbase (le_trans hstep (le_of_eq ?_))
  rw [Real.exp_add, hpow]

/-- The reciprocal squares of the primes below `z` are bounded by `ζ(2)`. -/
theorem sum_inv_sq_primesLE_le (z : ℕ) :
    ∑ p ∈ Nat.primesLE z, 1 / (p : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 := by
  have hzeta : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) := hasSum_zeta_two
  exact sum_le_hasSum (Nat.primesLE z) (fun n _ => by positivity) hzeta

/-- **The Halász saving with an absolute constant.**  The damped Dirichlet sum over squarefree
`z`-smooth integers is at most `C·(log T)⁷` at every frequency `|t| ≤ T`, with `C` independent of
both the smoothness parameter and the frequency range. -/
theorem exists_norm_sum_moebius_smooth_le_absolute :
    ∃ C : ℝ, ∀ (z : ℕ) (T t : ℝ), 3 ≤ z → 9 ≤ T → |t| ≤ T →
      1 / Real.log z ≤ zetaLowerA / Real.log T ^ 9 →
      ‖∑ n ∈ (Nat.primesLE z).powerset.image (fun S => ∏ p ∈ S, p),
          ((1 / (n : ℝ) : ℝ) : ℂ)
            * (moebiusC n * Complex.exp (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I))‖
        ≤ C * Real.log T ^ 7 := by
  obtain ⟨C₁, hC₁⟩ := exists_norm_sum_moebius_smooth_le_uniform
  refine ⟨Real.exp (Real.pi ^ 2 / 6 + C₁), ?_⟩
  intro z T t hz hT htT hzt
  refine le_trans (hC₁ z T t hz hT htT hzt) ?_
  have hlogT : (0 : ℝ) < Real.log T := Real.log_pos (by linarith)
  have hpow : (0 : ℝ) ≤ Real.log T ^ 7 := by positivity
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hpow
  have := sum_inv_sq_primesLE_le z
  linarith

end RHTower.Sieve
