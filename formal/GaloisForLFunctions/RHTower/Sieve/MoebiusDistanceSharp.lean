import GaloisForLFunctions.RHTower.Sieve.PrimeCosineSum
import GaloisForLFunctions.RHTower.Sieve.ZetaWideRectangle
import GaloisForLFunctions.RHTower.Sieve.ZeroFreeCombination
import GaloisForLFunctions.RHTower.Sieve.MoebiusFrequencyDistance
import GaloisForLFunctions.RHTower.Sieve.MoebiusEulerDamping
import GaloisForLFunctions.RHTower.Sieve.ZetaPoleBoxLowerBound

/-!
# The Möbius distance without a zero-free strip

`sum_cos_div_prime_ge` bounds the prime cosine sum below by `−7 log log|t| − C`, but only once
`log⁹|t|/A ≤ log z`: the lower bound for `|ζ|` it uses is the one supplied by the exponent-nine
zero-free strip, and the abscissa `1 + 1/log z` must lie inside that strip.

The three-four-one inequality supplies a lower bound for `|ζ(σ+it)|` at *every* `σ > 1` with no
zero-free input at all,

```text
|ζ(σ+it)| ≥ exp( (−22 − 3 log(1 + 1/(σ−1)) − log‖ζ(σ+2it)‖) / 4 ) ,
```

and right of the abscissa `‖ζ‖` is at most `3 + log(4 + |Im s|)` by the harmonic sum.  At
`σ = 1 + 1/log z` this gives

```text
∑_{p ≤ z} cos(t log p)/p  ≥  −(3/4) log(1 + log z) − (1/4) log(3 + log(4 + 2|t|)) − C ,
```

for **every** `z ≥ 3` and every `|t| ≥ 1`.  The price is a self-loss `(3/4) log log z` where the
strip version loses nothing in `z`; the gain is that the smoothness parameter is unconstrained, so
the Möbius distance

```text
D(μ, χ_t; p ≤ z)²  ≥  (1/4) log log z − (1/4) log log|t| − C
```

is positive and growing as soon as `log z` exceeds a fixed power of `log|t|` above the first, where
the strip version needs `log z ≥ (log|t|)⁹/A`.
-/

namespace RHTower.Sieve

open Finset RHTower

/-- **Right of the abscissa `ζ` is logarithmic.**  Only the harmonic sum is used. -/
theorem norm_riemannZeta_ge_one_log_le {w : ℂ} (hre : 1 ≤ w.re) (hre2 : w.re ≤ 2)
    (him : 1 ≤ |w.im|) :
    ‖riemannZeta w‖ ≤ 3 + Real.log (4 + |w.im|) := by
  set N : ℕ := ⌈3 + |w.im|⌉₊ with hNdef
  have hpos : (0 : ℝ) < 3 + |w.im| := by
    have := abs_nonneg w.im; linarith
  have hNle : (3 : ℝ) + |w.im| ≤ ((N : ℕ) : ℝ) := by rw [hNdef]; exact Nat.le_ceil _
  have hNlt : ((N : ℕ) : ℝ) < 4 + |w.im| := by
    have hc := Nat.ceil_lt_add_one (a := 3 + |w.im|) hpos.le
    rw [← hNdef] at hc
    linarith
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by linarith
  have hbase := norm_riemannZeta_ge_one_le hre him hN1
  have hwnorm : ‖w‖ ≤ 2 + |w.im| := by
    refine le_trans (Complex.norm_le_abs_re_add_abs_im w) ?_
    have hrew : |w.re| = w.re := abs_of_pos (by linarith)
    rw [hrew]
    linarith
  have hdiv : ‖w‖ / ((N : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hN0]
    linarith
  have hlog : Real.log ((N : ℕ) : ℝ) ≤ Real.log (4 + |w.im|) :=
    Real.log_le_log hN0 hNlt.le
  linarith

/-- **The prime series below the three-four-one lower bound.**  No zero-free input. -/
theorem le_tsum_re_prime_cpow_shift {σ t B₀ : ℝ} (hσ1 : 1 < σ)
    (hB : ‖riemannZeta ((σ : ℂ) + (2 * t : ℂ) * Complex.I)‖ ≤ B₀) :
    (-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4 - Real.pi ^ 2 / 6
      ≤ ∑' p : Nat.Primes, (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re := by
  have hlow := exp_le_norm_riemannZeta_shift (σ := σ) (t := t) (B₀ := B₀) hσ1 hB
  have hlog : (-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4
      ≤ Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    have h := Real.log_le_log (Real.exp_pos _) hlow
    rwa [Real.log_exp] at h
  exact le_tsum_re_prime_cpow_of_log_le hσ1 hlog

/-- **The prime cosine sum with no constraint on the truncation.** -/
theorem sum_cos_div_prime_ge_shift {z : ℕ} {t B₀ : ℝ} (hz : 3 ≤ z)
    (hB : ‖riemannZeta (((1 + 1 / Real.log (z : ℝ) : ℝ) : ℂ) + (2 * t : ℂ) * Complex.I)‖ ≤ B₀) :
    (-22 - 3 * Real.log (1 + Real.log (z : ℝ)) - Real.log B₀) / 4 - Real.pi ^ 2 / 6
        - 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
        - (1 + Real.log 4)
      ≤ ∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log p) / (p : ℝ) := by
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : (1 : ℝ) ≤ Real.log (z : ℝ) := by
    have hexp : Real.exp 1 ≤ (z : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    have h := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at h
  have hlogz0 : (0 : ℝ) < Real.log (z : ℝ) := by linarith
  have hσ1 : (1 : ℝ) < 1 + 1 / Real.log (z : ℝ) := by
    have : (0 : ℝ) < 1 / Real.log (z : ℝ) := by positivity
    linarith
  have hinv : 1 / ((1 + 1 / Real.log (z : ℝ)) - 1) = Real.log (z : ℝ) := by
    rw [show (1 + 1 / Real.log (z : ℝ)) - 1 = 1 / Real.log (z : ℝ) by ring, one_div_one_div]
  have hmain := le_tsum_re_prime_cpow_shift (σ := 1 + 1 / Real.log (z : ℝ)) (t := t)
    (B₀ := B₀) hσ1 hB
  rw [hinv] at hmain
  exact sum_cos_div_prime_ge_of_le hz hmain

/-- **The prime cosine sum, unconditional and truncation-free.** -/
theorem sum_cos_div_prime_ge_absolute {z : ℕ} {t : ℝ} (hz : 3 ≤ z) (ht : 1 ≤ |t|) :
    (-22 - 3 * Real.log (1 + Real.log (z : ℝ))
          - Real.log (3 + Real.log (4 + 2 * |t|))) / 4 - Real.pi ^ 2 / 6
        - 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
        - (1 + Real.log 4)
      ≤ ∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log p) / (p : ℝ) := by
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : (1 : ℝ) ≤ Real.log (z : ℝ) := by
    have hexp : Real.exp 1 ≤ (z : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    have h := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at h
  have hlogz0 : (0 : ℝ) < Real.log (z : ℝ) := by linarith
  set c : ℝ := 1 + 1 / Real.log (z : ℝ) with hcdef
  have hcinv : (0 : ℝ) < 1 / Real.log (z : ℝ) := by positivity
  have hcre : (((c : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I).re = c := by simp
  have hcim : (((c : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I).im = 2 * t := by simp
  have hc1 : (1 : ℝ) ≤ c := by rw [hcdef]; linarith
  have hc2 : c ≤ 2 := by
    rw [hcdef]
    have : 1 / Real.log (z : ℝ) ≤ 1 := by rw [div_le_one hlogz0]; linarith
    linarith
  have him2 : (1 : ℝ) ≤ |2 * t| := by
    rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    linarith
  have hB0 := norm_riemannZeta_ge_one_log_le
    (w := ((c : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
    (by rw [hcre]; exact hc1) (by rw [hcre]; exact hc2) (by rw [hcim]; exact him2)
  rw [hcim] at hB0
  have hcast : ((c : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I
      = ((c : ℝ) : ℂ) + (2 * t : ℂ) * Complex.I := by push_cast; ring
  rw [hcast, abs_mul, show |(2 : ℝ)| = 2 by norm_num] at hB0
  exact sum_cos_div_prime_ge_shift hz hB0

/-- **The Möbius distance, unconditional and truncation-free.**  A `μ`-like weight is far from the
character `χ_t` as soon as `log z` exceeds a fixed power of `log|t|` above the first. -/
theorem le_mulDistSqPair_moebius_absolute {f : ℕ → ℂ} {z : ℕ} {t : ℝ} (hz : 3 ≤ z)
    (ht : 1 ≤ |t|) (hf : ∀ p ∈ Nat.primesLE z, f p = -1) :
    logLog z - mertensSecondLowerConst
        + ((-22 - 3 * Real.log (1 + Real.log (z : ℝ))
            - Real.log (3 + Real.log (4 + 2 * |t|))) / 4 - Real.pi ^ 2 / 6
          - 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
          - (1 + Real.log 4))
      ≤ mulDistSqPair f (charFn t) (Nat.primesLE z) := by
  have hmertens : logLog z - mertensSecondLowerConst ≤ ∑ p ∈ Nat.primesLE z, 1 / (p : ℝ) :=
    le_mertensS (by omega)
  have hcos := sum_cos_div_prime_ge_absolute hz ht
  rw [mulDistSqPair_neg_one_split hf t]
  linarith

/-! ### The damped smooth sum -/

/-- The reciprocal squares of the primes below `z` are bounded by `ζ(2)`. -/
theorem sum_inv_sq_primesLE_le_pi (z : ℕ) :
    ∑ p ∈ Nat.primesLE z, 1 / (p : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 := by
  have hzeta : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) := hasSum_zeta_two
  exact sum_le_hasSum (Nat.primesLE z) (fun n _ => by positivity) hzeta

/-- **A power saving for the damped smooth Möbius sum, at every scale.**  The Dirichlet sum over
squarefree `z`-smooth integers is at most `C·(1 + log z)^{3/4}·(3 + log(4 + 2|t|))^{1/4}`, where the
trivial bound is `∏_{p ≤ z}(1 + 1/p) ≍ log z`.  Unlike the strip version this holds for every
smoothness parameter, with no relation between `z` and the frequency. -/
theorem exists_norm_sum_moebius_smooth_le_free :
    ∃ C : ℝ, ∀ (z : ℕ) (t : ℝ), 3 ≤ z → 1 ≤ |t| →
      ‖∑ n ∈ (Nat.primesLE z).powerset.image (fun S => ∏ p ∈ S, p),
          ((1 / (n : ℝ) : ℝ) : ℂ)
            * (moebiusC n * Complex.exp (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I))‖
        ≤ C * (1 + Real.log (z : ℝ)) ^ ((3 : ℝ) / 4)
            * (3 + Real.log (4 + 2 * |t|)) ^ ((1 : ℝ) / 4) := by
  refine ⟨Real.exp (Real.pi ^ 2 / 6 + 22 / 4 + Real.pi ^ 2 / 6
    + 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
    + (1 + Real.log 4)), ?_⟩
  intro z t hz ht
  have hP : ∀ p ∈ Nat.primesLE z, p.Prime := fun p hp => (Nat.mem_primesLE.1 hp).2
  have hbase := norm_sum_moebius_smooth_le_exp t hP
  have hcos := sum_cos_div_prime_ge_absolute hz ht
  have hsq := sum_inv_sq_primesLE_le_pi z
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hL1 : (0 : ℝ) < 1 + Real.log (z : ℝ) := by
    have : (0 : ℝ) ≤ Real.log (z : ℝ) := Real.log_nonneg (by linarith)
    linarith
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hL2 : (0 : ℝ) < 3 + Real.log (4 + 2 * |t|) := by
    have : (0 : ℝ) ≤ Real.log (4 + 2 * |t|) := Real.log_nonneg (by linarith)
    linarith
  have hpow1 : (1 + Real.log (z : ℝ)) ^ ((3 : ℝ) / 4)
      = Real.exp (3 / 4 * Real.log (1 + Real.log (z : ℝ))) := by
    rw [Real.rpow_def_of_pos hL1]
    ring_nf
  have hpow2 : (3 + Real.log (4 + 2 * |t|)) ^ ((1 : ℝ) / 4)
      = Real.exp (1 / 4 * Real.log (3 + Real.log (4 + 2 * |t|))) := by
    rw [Real.rpow_def_of_pos hL2]
    ring_nf
  refine le_trans hbase ?_
  rw [hpow1, hpow2, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  linarith

/-! ### The frequency range, with no constraint on the truncation -/

/-- **The prime cosine sum at every frequency and every truncation.**  The pole box covers
`|t| ≤ 9`, the three-four-one bound covers the rest, and neither imposes a relation between the
truncation and the frequency. -/
theorem exists_sum_cos_div_prime_ge_free :
    ∃ C : ℝ, ∀ (z : ℕ) (t : ℝ), 3 ≤ z →
      -(3 / 4 * Real.log (1 + Real.log (z : ℝ)))
          - 1 / 4 * Real.log (3 + Real.log (4 + 2 * |t|)) - C
        ≤ ∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log p) / (p : ℝ) := by
  obtain ⟨C₀, hC₀⟩ := exists_sum_cos_div_prime_ge_small
  refine ⟨max C₀ (22 / 4 + Real.pi ^ 2 / 6
    + 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
    + (1 + Real.log 4)), ?_⟩
  intro z t hz
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hL1 : (0 : ℝ) ≤ Real.log (1 + Real.log (z : ℝ)) := by
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ Real.log (z : ℝ) := Real.log_nonneg (by linarith)
    linarith
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hL2 : (0 : ℝ) ≤ Real.log (3 + Real.log (4 + 2 * |t|)) := by
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ Real.log (4 + 2 * |t|) := Real.log_nonneg (by linarith)
    linarith
  rcases le_or_gt (|t|) 9 with hsmall | hlarge
  · have hbase := hC₀ z hz t hsmall
    have hmax : C₀ ≤ max C₀ (22 / 4 + Real.pi ^ 2 / 6
      + 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
      + (1 + Real.log 4)) := le_max_left _ _
    linarith
  · have hbase := sum_cos_div_prime_ge_absolute hz (by linarith : (1 : ℝ) ≤ |t|)
    have hmax : 22 / 4 + Real.pi ^ 2 / 6
        + 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
        + (1 + Real.log 4)
        ≤ max C₀ (22 / 4 + Real.pi ^ 2 / 6
          + 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
          + (1 + Real.log 4)) := le_max_right _ _
    linarith

/-- **The distance to a character, at every frequency and every truncation.**  The `(log t)⁹`
smoothness gate of the strip version is gone; the price is the self-loss `(3/4) log log z`. -/
theorem exists_mulDistSqPair_ge_free :
    ∃ C : ℝ, ∀ (f : ℕ → ℂ) (z : ℕ) (t : ℝ), 3 ≤ z →
      (∀ p ∈ Nat.primesLE z, f p = -1) →
      logLog z - 3 / 4 * Real.log (1 + Real.log (z : ℝ))
          - 1 / 4 * Real.log (3 + Real.log (4 + 2 * |t|)) - C
        ≤ mulDistSqPair f (charFn t) (Nat.primesLE z) := by
  obtain ⟨C₁, hC₁⟩ := exists_sum_cos_div_prime_ge_free
  refine ⟨C₁ + mertensSecondLowerConst, ?_⟩
  intro f z t hz hf
  have hmertens : logLog z - mertensSecondLowerConst ≤ ∑ p ∈ Nat.primesLE z, 1 / (p : ℝ) :=
    le_mertensS (by omega)
  have hcos := hC₁ z t hz
  rw [mulDistSqPair_neg_one_split hf t]
  linarith

/-! ### The strip-quality constant, with `z ≤ T` in place of the gate -/

/-- Both logarithmic losses are bounded by `log log T` once the truncation stays below the
frequency range. -/
theorem wide_losses_le_logLog {z : ℕ} {T : ℝ} (hz : 3 ≤ z) (hT : 3 ≤ T) (hzT : (z : ℝ) ≤ T)
    {t : ℝ} (htT : |t| ≤ T) :
    3 / 4 * Real.log (1 + Real.log (z : ℝ))
        + 1 / 4 * Real.log (3 + Real.log (4 + 2 * |t|))
      ≤ Real.log (Real.log T) + 11 / 10 := by
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hT0 : (0 : ℝ) < T := by linarith
  have hT1 : (1 : ℝ) ≤ Real.log T := by
    have hexp : Real.exp 1 ≤ T := by
      have := Real.exp_one_lt_d9
      linarith
    have h := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at h
  have hT0' : (0 : ℝ) < Real.log T := by linarith
  have hlog2 : Real.log 2 ≤ 7 / 10 := by
    have := Real.log_two_lt_d9; linarith
  have hlog6 : Real.log 6 ≤ 21 / 10 := by
    have h8 : Real.log ((6 : ℝ)) ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
    have h8eq : Real.log ((8 : ℝ)) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num
    rw [h8eq] at h8
    linarith
  -- the truncation loss
  have hzlog : Real.log (z : ℝ) ≤ Real.log T := Real.log_le_log (by linarith) hzT
  have hA : Real.log (1 + Real.log (z : ℝ)) ≤ Real.log 2 + Real.log (Real.log T) := by
    have h1 : Real.log (1 + Real.log (z : ℝ)) ≤ Real.log (2 * Real.log T) := by
      refine Real.log_le_log (by nlinarith [Real.log_nonneg (show (1:ℝ) ≤ (z:ℝ) by linarith)]) ?_
      linarith
    rwa [Real.log_mul (by norm_num) (ne_of_gt hT0')] at h1
  -- the frequency loss
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hstep : 4 + 2 * |t| ≤ 6 * T := by linarith
  have hlogstep : Real.log (4 + 2 * |t|) ≤ Real.log 6 + Real.log T := by
    have h1 : Real.log (4 + 2 * |t|) ≤ Real.log (6 * T) :=
      Real.log_le_log (by linarith) hstep
    rwa [Real.log_mul (by norm_num) (ne_of_gt hT0)] at h1
  have hlog7 : Real.log 7 ≤ 21 / 10 := by
    have h8 : Real.log ((7 : ℝ)) ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
    have h8eq : Real.log ((8 : ℝ)) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num
    rw [h8eq] at h8
    linarith
  have hB : Real.log (3 + Real.log (4 + 2 * |t|)) ≤ Real.log 7 + Real.log (Real.log T) := by
    have hin : 3 + Real.log (4 + 2 * |t|) ≤ 7 * Real.log T := by linarith
    have hpos : (0 : ℝ) < 3 + Real.log (4 + 2 * |t|) := by
      have : (0 : ℝ) ≤ Real.log (4 + 2 * |t|) := Real.log_nonneg (by linarith)
      linarith
    have h1 : Real.log (3 + Real.log (4 + 2 * |t|)) ≤ Real.log (7 * Real.log T) :=
      Real.log_le_log hpos hin
    rwa [Real.log_mul (by norm_num) (ne_of_gt hT0')] at h1
  linarith

/-- **The distance with the strip-quality constant.**  The exponent-nine strip loses
`7 log log T` and demands `log⁹T/A ≤ log z`; this loses `log log T + 11/10` and demands only
`z ≤ T`. -/
theorem exists_mulDistSqPair_ge_height :
    ∃ C : ℝ, ∀ (f : ℕ → ℂ) (z : ℕ) (T t : ℝ), 3 ≤ z → 3 ≤ T → (z : ℝ) ≤ T → |t| ≤ T →
      (∀ p ∈ Nat.primesLE z, f p = -1) →
      logLog z - Real.log (Real.log T) - C
        ≤ mulDistSqPair f (charFn t) (Nat.primesLE z) := by
  obtain ⟨C₁, hC₁⟩ := exists_mulDistSqPair_ge_free
  refine ⟨C₁ + 11 / 10, ?_⟩
  intro f z T t hz hT hzT htT hf
  have hbase := hC₁ f z t hz hf
  have hloss := wide_losses_le_logLog hz hT hzT htT
  linarith

end RHTower.Sieve
