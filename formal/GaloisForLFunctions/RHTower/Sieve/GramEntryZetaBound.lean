import GaloisForLFunctions.RHTower.Sieve.CriticalTruncationZeta
import GaloisForLFunctions.RHTower.Sieve.AbelIncreasingWeight

/-!
# The Gram entry of a Dirichlet polynomial, against `ζ`

The Gram matrix of the exponential rows `n ↦ n^{it_r}` has entries `∑_{n < M} n^{iτ}`.  Writing
`n^{-iτ} = n^{1/2}·n^{-1/2-iτ}` and summing by parts against the increasing weight `n^{1/2}`
(`Sieve/AbelIncreasingWeight`) reduces the entry to the critical-line partial sums, which
`Sieve/CriticalTruncationZeta` compares with `ζ`.  The outcome

```text
|∑_{1 ≤ n < M} n^{-it}| ≤ 2 M^{1/2}‖ζ(1/2+it)‖ + 2M/|t| + M^{1/2} + 8|t| M^{1/2}
```

is the classical bound Jutila's estimate averages with the fourth moment of `ζ`.  Every term but
`‖ζ‖` is elementary.
-/

namespace RHTower.Sieve

open Finset Complex

noncomputable section

/-- A uniform bound for every prefix of the critical-line series. -/
def criticalPrefixBound (K : ℕ) (t : ℝ) : ℝ :=
  ‖riemannZeta (criticalPt t)‖ + (K : ℝ) ^ ((1 : ℝ) / 2) / |t| + 1 / 2 + 4 * |t|

theorem criticalPrefixBound_nonneg {K : ℕ} {t : ℝ} (ht : 2 ≤ |t|) :
    0 ≤ criticalPrefixBound K t := by
  have h1 : (0 : ℝ) < |t| := by linarith
  rw [criticalPrefixBound]
  have h2 : (0 : ℝ) ≤ ‖riemannZeta (criticalPt t)‖ := norm_nonneg _
  have h3 : (0 : ℝ) ≤ (K : ℝ) ^ ((1 : ℝ) / 2) / |t| := by positivity
  linarith

/-- **Every prefix of the critical-line series is bounded by `‖ζ‖` plus elementary terms.** -/
theorem norm_sum_range_criticalPt_prefix_le {K : ℕ} {t : ℝ} (ht : 2 ≤ |t|) (k : ℕ) (hk : k ≤ K) :
    ‖∑ n ∈ Finset.range k, (1 : ℂ) / (n : ℂ) ^ (criticalPt t)‖ ≤ criticalPrefixBound K t := by
  have habs : (0 : ℝ) < |t| := by linarith
  have hKk : ((k : ℝ)) ≤ (K : ℝ) := by exact_mod_cast hk
  rcases Nat.lt_or_ge k 2 with hsmall | hk2
  · have hzero : ∑ n ∈ Finset.range k, (1 : ℂ) / (n : ℂ) ^ (criticalPt t) = 0 := by
      interval_cases k
      · simp
      · simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero]
        rw [Complex.zero_cpow]
        · simp
        · intro h
          have := congrArg Complex.re h
          rw [criticalPt_re] at this
          norm_num at this
    rw [hzero, norm_zero]
    exact criticalPrefixBound_nonneg ht
  · have hk1 : 1 ≤ k - 1 := by omega
    have hrw : k = (k - 1) + 1 := by omega
    rw [hrw]
    refine le_trans (norm_sum_range_criticalPt_le hk1 ht) ?_
    have hkm : (((k - 1 : ℕ)) : ℝ) ≤ (K : ℝ) := by
      have : (k - 1 : ℕ) ≤ K := by omega
      exact_mod_cast this
    have hkm1 : (1 : ℝ) ≤ (((k - 1 : ℕ)) : ℝ) := by exact_mod_cast hk1
    have hmono : (((k - 1 : ℕ)) : ℝ) ^ ((1 : ℝ) / 2) ≤ (K : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) hkm (by norm_num)
    have hinv : (((k - 1 : ℕ)) : ℝ) ^ (-(1 : ℝ) / 2) ≤ 1 := by
      rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring]
      exact Real.rpow_le_one_of_one_le_of_nonpos hkm1 (by norm_num)
    have hdiv : (((k - 1 : ℕ)) : ℝ) ^ ((1 : ℝ) / 2) / |t| ≤ (K : ℝ) ^ ((1 : ℝ) / 2) / |t| :=
      div_le_div_of_nonneg_right hmono habs.le
    rw [criticalPrefixBound]
    have h4 : 4 * |t| * (((k - 1 : ℕ)) : ℝ) ^ (-(1 : ℝ) / 2) ≤ 4 * |t| := by
      nlinarith [hinv, habs.le]
    have h5 : (((k - 1 : ℕ)) : ℝ) ^ (-(1 : ℝ) / 2) / 2 ≤ 1 / 2 := by linarith [hinv]
    linarith [hdiv, h4, h5]

/-- The weighted summand is the pure exponential. -/
theorem weighted_criticalPt_eq (t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ((((n : ℝ)) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * ((1 : ℂ) / (n : ℂ) ^ (criticalPt t))
      = (n : ℂ) ^ (-(((t : ℝ)) : ℂ) * Complex.I) := by
  have hn0 : (n : ℂ) ≠ 0 := by
    have : (0 : ℕ) < n := hn
    exact_mod_cast Nat.cast_ne_zero.2 (by omega)
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hhalf : ((((n : ℝ)) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) = (n : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hnR]
    norm_num
  have hsplit : (n : ℂ) ^ (criticalPt t)
      = (n : ℂ) ^ ((1 / 2 : ℝ) : ℂ) * (n : ℂ) ^ ((((t : ℝ)) : ℂ) * Complex.I) := by
    rw [← Complex.cpow_add _ _ hn0]
    rfl
  rw [hhalf, hsplit]
  have hne : (n : ℂ) ^ ((1 / 2 : ℝ) : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hn0)
  field_simp
  rw [Complex.cpow_neg, one_div]

/-- **The Gram entry of the exponential rows, against `ζ`.**  Every term but `‖ζ‖` is elementary. -/
theorem norm_sum_expSum_le_zeta (M : ℕ) {t : ℝ} (ht : 2 ≤ |t|) :
    ‖∑ n ∈ Finset.range M, (n : ℂ) ^ (-(((t : ℝ)) : ℂ) * Complex.I)‖
      ≤ 2 * criticalPrefixBound M t * (((M - 1 : ℕ)) : ℝ) ^ ((1 : ℝ) / 2) := by
  have ht0 : t ≠ 0 := by
    intro h
    rw [h] at ht
    simp at ht
    linarith
  have hIne : -(((t : ℝ)) : ℂ) * Complex.I ≠ 0 := by
    intro h
    have : ((t : ℝ) : ℂ) = 0 := by
      rcases mul_eq_zero.1 h with h1 | h2
      · exact neg_eq_zero.1 h1
      · exact absurd h2 Complex.I_ne_zero
    exact ht0 (by exact_mod_cast this)
  have hterm : ∀ n : ℕ, (n : ℂ) ^ (-(((t : ℝ)) : ℂ) * Complex.I)
      = ((((n : ℝ)) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * ((1 : ℂ) / (n : ℂ) ^ (criticalPt t)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.cast_zero, Complex.zero_cpow hIne]
      norm_num [Real.zero_rpow]
    · exact (weighted_criticalPt_eq t hn).symm
  rw [Finset.sum_congr rfl (fun n _ => hterm n)]
  refine norm_sum_mul_le_of_bounded_partial_mono M (fun n => ((n : ℝ)) ^ ((1 : ℝ) / 2))
    (fun n => (1 : ℂ) / (n : ℂ) ^ (criticalPt t)) ?_ ?_ ?_
  · simp [Real.zero_rpow]
  · intro i
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    exact_mod_cast Nat.le_succ i
  · intro k hk
    exact norm_sum_range_criticalPt_prefix_le ht k hk

end

end RHTower.Sieve
