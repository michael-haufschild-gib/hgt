import GaloisForLFunctions.RHTower.Sieve.PrimeTailBound
import GaloisForLFunctions.RHTower.Sieve.PrimeSigmaShift
import GaloisForLFunctions.RHTower.Sieve.ZetaStripPrimeSum
import GaloisForLFunctions.RHTower.VonMangoldtThreeFourOneSeries

/-!
# The prime cosine sum on the one-line

The Euler comparison controls `∑'_p cos(t log p)·p^{−σ}` for `σ > 1`, while the multiplicative
distance is a finite sum of `cos(t log p)/p` over `p ≤ z`.  Three passages separate them, and each
has already been bounded:

* the truncation `∑_{p > z} p^{−σ}`, an absolute constant at `σ = 1 + 1/log z`;
* the abscissa shift `∑_{p ≤ z} (1/p − p^{−σ})`, at most `(σ − 1)(log z + log 4) ≤ 1 + log 4`;
* the zero-free strip, which bounds the full series below by `−log((20/A)·log⁷|t|) − π²/6`.

Together they give, whenever `log⁹|t|/A ≤ log z`,

    ∑_{p ≤ z} cos(t log p)/p  ≥  −7 log log|t| − C,

with `C` absolute.  Since Mertens' second theorem makes `∑_{p ≤ z} 1/p` at least
`log log z − c ≥ 9 log log|t| − c'`, the Möbius distance to `χ_t` is at least `2 log log|t|`: the
Möbius function is quantitatively far from *every* character in the range.
-/

namespace RHTower.Sieve

open Finset RHTower

/-- The primes up to `z`, as a finite set of the type of primes. -/
noncomputable def primeSubtypeLE (z : ℕ) : Finset Nat.Primes :=
  (Nat.primesLE z).subtype Nat.Prime

theorem mem_primeSubtypeLE {z : ℕ} {p : Nat.Primes} :
    p ∈ primeSubtypeLE z ↔ (p : ℕ) ≤ z :=
  ⟨fun h => (Nat.mem_primesLE.1 (Finset.mem_subtype.1 h)).1,
   fun h => Finset.mem_subtype.2 (Nat.mem_primesLE.2 ⟨h, p.2⟩)⟩

theorem sum_primeSubtypeLE (z : ℕ) (g : ℕ → ℝ) :
    ∑ p ∈ primeSubtypeLE z, g (p : ℕ) = ∑ n ∈ Nat.primesLE z, g n := by
  have h : ∑ p ∈ primeSubtypeLE z, g (p : ℕ)
      = ∑ n ∈ (Nat.primesLE z).filter Nat.Prime, g n :=
    Finset.sum_subtype_eq_sum_filter (s := Nat.primesLE z) (p := Nat.Prime) g
  rw [h]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  refine Finset.filter_true_of_mem ?_
  intro n hn
  exact (Nat.mem_primesLE.1 hn).2

/-- The truncated part of the prime series is dominated by the tail weight. -/
theorem norm_prime_tail_re_le {z : ℕ} {σ t : ℝ} (p : Nat.Primes) :
    ‖(if z < (p : ℕ) then
        (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re else 0)‖
      ≤ primeTailTerm z σ p := by
  have hp0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := by positivity
  rw [Real.norm_eq_abs, primeTailTerm]
  split_ifs with h
  · rw [RHTower.re_natCast_cpow_neg p.2.pos σ t, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hp0 _)]
    have hcos : |Real.cos (t * Real.log ((p : ℕ) : ℝ))| ≤ 1 := Real.abs_cos_le_one _
    nlinarith [Real.rpow_nonneg hp0 (-σ)]
  · simp

/-- **The head–tail split of the prime series.**  The head is the finite cosine sum. -/
theorem tsum_re_prime_cpow_split {z : ℕ} {σ t : ℝ} (hσ : 1 < σ) :
    ∑' p : Nat.Primes, (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re
      = (∑ n ∈ Nat.primesLE z, ((n : ℝ)) ^ (-σ) * Real.cos (t * Real.log n))
        + ∑' p : Nat.Primes,
            (if z < (p : ℕ) then
              (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re else 0) := by
  classical
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have hH : Summable (fun p : Nat.Primes =>
      if (p : ℕ) ≤ z then
        (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re else 0) := by
    refine summable_of_ne_finset_zero (s := primeSubtypeLE z) ?_
    intro p hp
    rw [if_neg]
    intro hcon
    exact hp (mem_primeSubtypeLE.2 hcon)
  have hT : Summable (fun p : Nat.Primes =>
      if z < (p : ℕ) then
        (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re else 0) :=
    Summable.of_norm_bounded (summable_primeTailTerm z hσ) (fun p => norm_prime_tail_re_le p)
  have hadd : ∀ p : Nat.Primes,
      (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re
        = (if (p : ℕ) ≤ z then
            (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re else 0)
          + (if z < (p : ℕ) then
            (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re else 0) := by
    intro p
    by_cases h : (p : ℕ) ≤ z
    · rw [if_pos h, if_neg (by omega)]
      ring
    · rw [if_neg h, if_pos (by omega)]
      ring
  rw [tsum_congr hadd, hH.tsum_add hT]
  congr 1
  rw [tsum_eq_sum (s := primeSubtypeLE z) (fun p hp => if_neg (fun hcon =>
    hp (mem_primeSubtypeLE.2 hcon)))]
  have hstep : ∑ p ∈ primeSubtypeLE z,
      (if (p : ℕ) ≤ z then
        (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re else 0)
      = ∑ p ∈ primeSubtypeLE z,
          (fun n : ℕ => ((n : ℝ)) ^ (-σ) * Real.cos (t * Real.log n)) (p : ℕ) := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [if_pos (mem_primeSubtypeLE.1 hp)]
    exact RHTower.re_natCast_cpow_neg p.2.pos σ t
  rw [hstep]
  exact sum_primeSubtypeLE z (fun n : ℕ => ((n : ℝ)) ^ (-σ) * Real.cos (t * Real.log n))

/-- **The truncation error.** -/
theorem abs_tsum_prime_tail_re_le {z : ℕ} {σ t : ℝ} (hσ : 1 < σ) :
    |∑' p : Nat.Primes,
        (if z < (p : ℕ) then
          (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re else 0)|
      ≤ ∑' p : Nat.Primes, primeTailTerm z σ p := by
  have hnorm : Summable (fun p : Nat.Primes =>
      ‖(if z < (p : ℕ) then
        (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re else 0)‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => norm_prime_tail_re_le p)
      (summable_primeTailTerm z hσ)
  have hstep := norm_tsum_le_tsum_norm hnorm
  rw [Real.norm_eq_abs] at hstep
  refine le_trans hstep ?_
  exact Summable.tsum_le_tsum (fun p => norm_prime_tail_re_le p) hnorm
    (summable_primeTailTerm z hσ)

/-- **The passage from the prime series to the finite cosine sum.**  Whatever lower bound the
Euler comparison supplies for the series at `σ = 1 + 1/log z`, the finite sum inherits it up to two
absolute constants: the truncation and the abscissa shift. -/
theorem sum_cos_div_prime_ge_of_le {z : ℕ} {t L : ℝ} (hz : 3 ≤ z)
    (hL : L ≤ ∑' p : Nat.Primes,
      (((p : ℕ) : ℂ) ^ (-(((1 + 1 / Real.log (z : ℝ) : ℝ) : ℂ) + (t : ℂ) * Complex.I))).re) :
    L - 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
        - (1 + Real.log 4)
      ≤ ∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log p) / (p : ℝ) := by
  classical
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : (1 : ℝ) ≤ Real.log (z : ℝ) := by
    have hexp : Real.exp 1 ≤ (z : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hlogz0 : (0 : ℝ) < Real.log (z : ℝ) := by linarith
  set σ : ℝ := 1 + 1 / Real.log (z : ℝ) with hσdef
  have hσ1 : (1 : ℝ) < σ := by
    rw [hσdef]
    have : (0 : ℝ) < 1 / Real.log (z : ℝ) := by positivity
    linarith
  have hsplit := tsum_re_prime_cpow_split (z := z) (t := t) hσ1
  have htail := abs_le.1 (abs_tsum_prime_tail_re_le (z := z) (t := t) hσ1)
  have htailC := tsum_primeTailTerm_le hz
  rw [← hσdef] at htailC
  have hshift := abs_le.1 (abs_sum_weight_shift_le (z := z) (by omega) hσ1.le
    (w := fun p : ℕ => Real.cos (t * Real.log (p : ℝ)))
    (fun p => Real.abs_cos_le_one _))
  have hident : ∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)
      = (∑ n ∈ Nat.primesLE z, ((n : ℝ)) ^ (-σ) * Real.cos (t * Real.log n))
        + ∑ p ∈ Nat.primesLE z,
            Real.cos (t * Real.log (p : ℝ)) * (1 / (p : ℝ) - ((p : ℝ)) ^ (-σ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring
  have hshiftC : (σ - 1) * (Real.log z + Real.log 4) ≤ 1 + Real.log 4 := by
    have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hval : (σ - 1) * (Real.log z + Real.log 4)
        = 1 + Real.log 4 / Real.log (z : ℝ) := by
      rw [hσdef]
      field_simp
      ring
    have hdiv : Real.log 4 / Real.log (z : ℝ) ≤ Real.log 4 := by
      rw [div_le_iff₀ hlogz0]
      nlinarith
    rw [hval]
    linarith
  rw [hident]
  linarith [hL, hsplit, htail.1, htail.2, htailC, hshift.1, hshift.2, hshiftC]

/-- The standard abscissa lies in the zero-free strip once `log⁹|t|/A ≤ log z`. -/
theorem standard_abscissa_mem_strip {z : ℕ} {t : ℝ} (hz : 3 ≤ z) (ht : 9 ≤ |t|)
    (hzt : 1 / Real.log z ≤ zetaLowerA / Real.log |t| ^ 9) :
    1 < 1 + 1 / Real.log (z : ℝ)
      ∧ 1 - zetaLowerA / Real.log |t| ^ 9 ≤ 1 + 1 / Real.log (z : ℝ)
      ∧ 1 + 1 / Real.log (z : ℝ) ≤ 1 + zetaLowerA / Real.log |t| ^ 9 := by
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : (1 : ℝ) ≤ Real.log (z : ℝ) := by
    have hexp : Real.exp 1 ≤ (z : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hlogz0 : (0 : ℝ) < Real.log (z : ℝ) := by linarith
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hlogt : (0 : ℝ) < Real.log |t| := Real.log_pos (by linarith)
  have hquot : (0 : ℝ) ≤ zetaLowerA / Real.log |t| ^ 9 := by positivity
  have hpos : (0 : ℝ) < 1 / Real.log (z : ℝ) := by positivity
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **The prime cosine sum on the one-line.**  Unconditional, uniform in the frequency: only
`7 log log|t|` is lost, and the truncation `z` is free as soon as `log⁹|t|/A ≤ log z`. -/
theorem sum_cos_div_prime_ge {z : ℕ} {t : ℝ} (hz : 3 ≤ z) (ht : 9 ≤ |t|)
    (hzt : 1 / Real.log z ≤ zetaLowerA / Real.log |t| ^ 9) :
    -Real.log (20 / zetaLowerA * Real.log |t| ^ 7) - Real.pi ^ 2 / 6
        - 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
        - (1 + Real.log 4)
      ≤ ∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log p) / (p : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := standard_abscissa_mem_strip hz ht hzt
  exact sum_cos_div_prime_ge_of_le hz (le_tsum_re_prime_cpow_strip ht h1 h2 h3)

end RHTower.Sieve
