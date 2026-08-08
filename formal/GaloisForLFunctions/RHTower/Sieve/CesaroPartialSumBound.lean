import GaloisForLFunctions.RHTower.Sieve.CesaroDampedChain

/-!
# The partial sum itself, by differencing the cutoff

The Cesàro kernel produces the weight `log(x/n)`, which vanishes at `n = x` — the usual reason a smoothed
sum has to be de-smoothed by a Tauberian argument.  Here no Tauberian argument is needed, because the
*coefficient support is fixed* and only the cutoff moves: for `x, x' ≥ N`,

`∑_{n ≤ N} f(n)log(x'/n) − ∑_{n ≤ N} f(n)log(x/n) = log(x'/x)·∑_{n ≤ N} f(n)`

**exactly**, since `log(x'/n) − log(x/n) = log(x'/x)` term by term.  So the partial sum is a difference of
two logarithmically weighted sums, and any bound on those is a bound on it:

`‖∑_{n ≤ N} f(n)‖·log(x'/x) ≤ (bound at x) + (bound at x')`.

Taking `x = N` and `x' = eN` makes `log(x'/x) = 1`.  The smoothing of the Cesàro kernel is therefore
harmless: it smooths in the *cutoff*, which is a free parameter, not in the support.
-/

noncomputable section
namespace RHTower.Sieve
open Complex Finset

/-- Truncating at the top of the range is invisible to the partial sum. -/
theorem sum_Icc_truncSeq_eq {f : ℕ → ℂ} (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, truncSeq f N n = ∑ n ∈ Finset.Icc 1 N, f n :=
  Finset.sum_congr rfl fun n hn => by rw [truncSeq, if_pos hn]

/-- **Differencing the cutoff recovers the partial sum exactly.**  The weight is `log x − log n`, so the
`n`-dependence cancels in the difference. -/
theorem sum_Icc_mul_log_sub_eq {f : ℕ → ℂ} {N : ℕ} {x x' : ℝ} (hx : 0 < x) (hx' : 0 < x') :
    (∑ n ∈ Finset.Icc 1 N, f n * ((Real.log (x' / n) : ℝ) : ℂ))
        - ∑ n ∈ Finset.Icc 1 N, f n * ((Real.log (x / n) : ℝ) : ℂ)
      = ((Real.log (x' / x) : ℝ) : ℂ) * ∑ n ∈ Finset.Icc 1 N, f n := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have h1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hcast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    linarith
  have hlog : Real.log (x' / n) - Real.log (x / n) = Real.log (x' / x) := by
    rw [Real.log_div hx'.ne' hn0.ne', Real.log_div hx.ne' hn0.ne', Real.log_div hx'.ne' hx.ne']
    ring
  rw [← hlog]
  push_cast
  ring

/-- **The partial sum from the Cesàro route, with no Tauberian step.**  The logarithmically weighted
bound is applied at two cutoffs and differenced. -/
theorem norm_sum_Icc_le_cesaro_difference {f : ℕ → ℂ} (hbdd : ∀ n, ‖f n‖ ≤ 1) {N : ℕ}
    (hN : 1 ≤ N) {V σ T x x' : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hT : 1 ≤ T) (hV : 0 ≤ V)
    (hxN : (N : ℝ) ≤ x) (hxx' : x ≤ x')
    (hgV : ∀ t : ℝ, |t| ≤ T → ‖LSeries (truncSeq f N) ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V) :
    ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (x' / x)
      ≤ ((∑ n ∈ Finset.Icc 1 N, cesaroError σ T (x / n))
            + (1 / (2 * Real.pi)) * (V * x ^ σ * (Real.pi / σ)))
        + ((∑ n ∈ Finset.Icc 1 N, cesaroError σ T (x' / n))
            + (1 / (2 * Real.pi)) * (V * x' ^ σ * (Real.pi / σ))) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx : (0 : ℝ) < x := by linarith
  have hx' : (0 : ℝ) < x' := by linarith
  have hratio : (1 : ℝ) ≤ x' / x := (one_le_div hx).2 hxx'
  have hlognn : (0 : ℝ) ≤ Real.log (x' / x) := Real.log_nonneg hratio
  have hid := sum_Icc_mul_log_sub_eq (f := truncSeq f N) (N := N) hx hx'
  rw [sum_Icc_truncSeq_eq] at hid
  have hnorm : ‖((Real.log (x' / x) : ℝ) : ℂ) * ∑ n ∈ Finset.Icc 1 N, f n‖
      = ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (x' / x) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlognn]
    ring
  have h1 := norm_sum_Icc_mul_log_div_le_cesaro (x := x) hbdd hN hσ1 hσ2 hT hV hxN hgV
  have h2 := norm_sum_Icc_mul_log_div_le_cesaro (x := x') hbdd hN hσ1 hσ2 hT hV
    (le_trans hxN hxx') hgV
  have htri : ‖((Real.log (x' / x) : ℝ) : ℂ) * ∑ n ∈ Finset.Icc 1 N, f n‖
      ≤ ‖∑ n ∈ Finset.Icc 1 N, truncSeq f N n * ((Real.log (x' / n) : ℝ) : ℂ)‖
        + ‖∑ n ∈ Finset.Icc 1 N, truncSeq f N n * ((Real.log (x / n) : ℝ) : ℂ)‖ := by
    rw [← hid]
    exact norm_sub_le _ _
  rw [hnorm] at htri
  linarith [htri, h1, h2]

/-- **The partial sum with the damped factor.**  The distance enters only through `dampedSize`. -/
theorem norm_sum_Icc_le_cesaro_damped {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n) (hbdd : ∀ n, ‖f n‖ ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) {σ T δ x x' : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hT : 1 ≤ T) (hδ : 0 ≤ δ)
    {z : ℕ} (hz : 1 ≤ z) (hxN : (N : ℝ) ≤ x) (hxx' : x ≤ x')
    (hunif : ∀ t : ℝ, |t| ≤ T →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z))) :
    ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (x' / x)
      ≤ ((∑ n ∈ Finset.Icc 1 N, cesaroError σ T (x / n))
            + (1 / (2 * Real.pi)) * (dampedSize σ δ z N * x ^ σ * (Real.pi / σ)))
        + ((∑ n ∈ Finset.Icc 1 N, cesaroError σ T (x' / n))
            + (1 / (2 * Real.pi)) * (dampedSize σ δ z N * x' ^ σ * (Real.pi / σ))) :=
  norm_sum_Icc_le_cesaro_difference hbdd hN hσ1.le hσ2 hT (dampedSize_nonneg hσ1 z N) hxN hxx'
    (fun _ ht => norm_LSeries_truncSeq_line_le_damped hf1 hmul hbdd hσ1 hz hδ hunif hN ht)

/-- **The Liouville partial sum through the Cesàro route.**  An unconditional bound on
`‖∑_{n ≤ N} λ(n)‖` itself: complete multiplicativity by `liouvilleC_mul`, the distance by the zero-free
strip, the analytic side by the integrable second-order decay of `x^s/s²`, and the passage from the
logarithmic weight to the partial sum by differencing the cutoff.  No sieve, no mean square, no dyadic
split, no recursion, and no Tauberian step. -/
theorem exists_norm_sum_Icc_liouvilleC_le_cesaro :
    ∃ C : ℝ, ∀ (N z : ℕ) (σ T x x' : ℝ), 1 ≤ N → 3 ≤ z → 1 < σ → σ ≤ 2 → 1 ≤ T → 9 ≤ T →
      (N : ℝ) ≤ x → x ≤ x' → 1 / Real.log z ≤ zetaLowerA / Real.log T ^ 9 →
      ‖∑ n ∈ Finset.Icc 1 N, liouvilleC n‖ * Real.log (x' / x)
        ≤ ((∑ n ∈ Finset.Icc 1 N, cesaroError σ T (x / n))
              + (1 / (2 * Real.pi))
                * (dampedSize σ (liouvilleDelta C z T) z N * x ^ σ * (Real.pi / σ)))
          + ((∑ n ∈ Finset.Icc 1 N, cesaroError σ T (x' / n))
              + (1 / (2 * Real.pi))
                * (dampedSize σ (liouvilleDelta C z T) z N * x' ^ σ * (Real.pi / σ))) := by
  obtain ⟨C, hC⟩ := exists_liouvilleC_mulDistSqPair_ge_uniform
  refine ⟨C, fun N z σ T x x' hN hz hσ1 hσ2 hT hT9 hxN hxx' hzt => ?_⟩
  have hz1 : 1 ≤ z := by omega
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → liouvilleC (m * n) = liouvilleC m * liouvilleC n :=
    fun {m n} _ => liouvilleC_mul m n
  have hunif : ∀ t : ℝ, |t| ≤ T →
      liouvilleDelta C z T ≤ Real.sqrt (mulDistSqPair liouvilleC (charFn t) (Nat.primesLE z)) := by
    intro t ht
    rw [liouvilleDelta]
    exact Real.sqrt_le_sqrt (hC z T t hz hT9 ht hzt)
  exact norm_sum_Icc_le_cesaro_damped liouvilleC_one hmul norm_liouvilleC_le hN hσ1 hσ2 hT
    (Real.sqrt_nonneg _) hz1 hxN hxx' hunif

end RHTower.Sieve
end
