import GaloisForLFunctions.RHTower.TwistedAntitwistPerron
import GaloisForLFunctions.RHTower.Sieve.ReciprocalDyadicAbel
import GaloisForLFunctions.RHTower.Sieve.HalaszGhsPunctured

/-!
# The reciprocal dyadic polynomial of a twisted multiplicative function

Dividing the twist `g(n)n^{-iτ}` by `n` is the reciprocal Dirichlet coefficient `g(n)n^{-1-iτ}`, so
Abel summation converts the sharp Halász partial-sum bound into the dyadic estimate

```text
‖∑_{Y ≤ n ≤ 2Y} g(n) n^{-1-iτ}‖ ≤ 2·max_{m ≤ 2Y}‖∑_{k ≤ m} g(k)k^{-iτ}‖ / Y.
```

Together with the punctured Halász bound — damped by a quarter of the Littlewood deficit off the
antitwist window, and by the kernel weight `1/(|τ|−1)` on it — and the entropy split of the Halász main
term, this is the whole reciprocal-polynomial estimate.
-/

noncomputable section

namespace RHTower

open RHTower.Sieve Complex

/-- The twist divided by `n` is the reciprocal Dirichlet coefficient at `1 + iτ`. -/
theorem twistSeq_div_eq_twistedSummand (f : ℕ → ℂ) (τ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    twistSeq f τ n / (n : ℂ) = twistedSummand f ((1 : ℂ) + (τ : ℝ) * Complex.I) n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℂ) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).2 (by omega : n ≠ 0)
  have hcpow : (n : ℂ) ^ (-((1 : ℂ) + (τ : ℝ) * Complex.I)) = charFn (-τ) n / (n : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
    have harg : ((Real.log n : ℝ) : ℂ) * (-((1 : ℂ) + (τ : ℝ) * Complex.I))
        = ((-(Real.log n) : ℝ) : ℂ) + ((-τ * Real.log n : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.exp_add]
    have hreal : Complex.exp ((-(Real.log n) : ℝ) : ℂ) = ((1 / (n : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hnpos]
      norm_num
    rw [hreal, charFn]
    push_cast
    field_simp
  rw [twistedSummand, hcpow, twistSeq_apply]
  ring

/-- **(Z13) The reciprocal dyadic polynomial from a uniform partial-sum bound.** -/
theorem norm_sum_Ico_twistedSummand_le {f : ℕ → ℂ} (τ : ℝ) {Y : ℕ} (hY : 1 ≤ Y) {E : ℝ}
    (hE : ∀ m : ℕ, m ≤ 2 * Y → ‖∑ n ∈ Finset.Icc 1 m, twistSeq f τ n‖ ≤ E) :
    ‖∑ n ∈ Finset.Ico Y (2 * Y + 1),
        twistedSummand f ((1 : ℂ) + (τ : ℝ) * Complex.I) n‖ ≤ 2 * E / (Y : ℝ) := by
  have hcongr : ∀ n ∈ Finset.Ico Y (2 * Y + 1),
      twistedSummand f ((1 : ℂ) + (τ : ℝ) * Complex.I) n = twistSeq f τ n / (n : ℂ) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    exact (twistSeq_div_eq_twistedSummand f τ (le_trans hY hn.1)).symm
  rw [Finset.sum_congr rfl hcongr]
  exact norm_sum_Ico_div_le_of_partialSum hY hE

end RHTower

end
