import GaloisForLFunctions.RHTower.Sieve.LorentzianLSeriesLine
/-!
# The block decomposition of a Dirichlet polynomial

A finitely supported Dirichlet series is a finite sum of terms, so for any index map `κ` whose image on the
support lies in a finite set `u`,

`L(a, t) = ∑_{j ∈ u} L(a·1_{κ = j}, t)`,

the fibres of `κ` splitting the sum.  Each fibre inherits the support, the coefficient bounds and the
primality of the original — restriction only kills coefficients.

The dyadic instance takes `κ = ⌊log₂ ·⌋` and `u = range(⌊log₂ M⌋ + 1)`, so the blocks are the ranges
`2^j ≤ n < 2^{j+1}`.  Combined with Minkowski for the weighted mean square this lets each block be estimated
with its own sieve level, which is what the Selberg count needs: it is sharp only when `log Y` is comparable
to `log p`, and on the block that is `log Y ≈ j log 2`.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Finset

/-- A finitely supported Dirichlet series is the finite sum of its terms. -/
theorem LSeries_eq_sum_term_of_support {a : ℕ → ℂ} {s : Finset ℕ}
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (t : ℂ) :
    LSeries a t = ∑ n ∈ s, LSeries.term a t n := by
  classical
  rw [LSeries]
  refine tsum_eq_sum fun n hn => ?_
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [LSeries.term_def, if_pos rfl]
  · have ha : a n = 0 := by
      by_contra hne
      exact hn (hsupp n hne)
    rw [LSeries.term_def, if_neg hn0, ha, zero_div]

/-- The coefficients of `a` carried by one fibre of an index map. -/
def coeffBlock {ι : Type*} [DecidableEq ι] (a : ℕ → ℂ) (κ : ℕ → ι) (j : ι) : ℕ → ℂ :=
  fun n => if κ n = j then a n else 0

theorem coeffBlock_support {ι : Type*} [DecidableEq ι] {a : ℕ → ℂ} {κ : ℕ → ι} {j : ι}
    {s : Finset ℕ} (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) :
    ∀ n : ℕ, coeffBlock a κ j n ≠ 0 → n ∈ s := by
  intro n hn
  rw [coeffBlock] at hn
  by_cases hk : κ n = j
  · rw [if_pos hk] at hn
    exact hsupp n hn
  · rw [if_neg hk] at hn
    exact absurd rfl hn

theorem norm_coeffBlock_le {ι : Type*} [DecidableEq ι] (a : ℕ → ℂ) (κ : ℕ → ι) (j : ι)
    (n : ℕ) : ‖coeffBlock a κ j n‖ ≤ ‖a n‖ := by
  rw [coeffBlock]
  by_cases hk : κ n = j
  · rw [if_pos hk]
  · rw [if_neg hk, norm_zero]
    exact norm_nonneg _

theorem coeffBlock_prime {ι : Type*} [DecidableEq ι] {a : ℕ → ℂ} {κ : ℕ → ι} {j : ι}
    {s : Finset ℕ} (hprime : ∀ n ∈ s, a n ≠ 0 → n.Prime) :
    ∀ n ∈ s, coeffBlock a κ j n ≠ 0 → n.Prime := by
  intro n hn hne
  refine hprime n hn ?_
  rw [coeffBlock] at hne
  by_cases hk : κ n = j
  · rw [if_pos hk] at hne
    exact hne
  · rw [if_neg hk] at hne
    exact absurd rfl hne

/-- **A Dirichlet polynomial is the sum of its blocks.**  For any index map into a finite set covering the
support, the series splits as the finite sum of the series of its fibres. -/
theorem LSeries_eq_sum_blocks {a : ℕ → ℂ} {s : Finset ℕ}
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) {ι : Type*} [DecidableEq ι] (κ : ℕ → ι) (u : Finset ι)
    (hmaps : ∀ n ∈ s, κ n ∈ u) (t : ℂ) :
    LSeries a t = ∑ j ∈ u, LSeries (coeffBlock a κ j) t := by
  classical
  rw [LSeries_eq_sum_term_of_support hsupp t]
  have hj : ∀ j ∈ u, LSeries (coeffBlock a κ j) t
      = ∑ n ∈ s with κ n = j, LSeries.term a t n := by
    intro j _
    rw [LSeries_eq_sum_term_of_support (coeffBlock_support (κ := κ) (j := j) hsupp) t]
    rw [← Finset.sum_filter_add_sum_filter_not s (fun n => κ n = j)]
    have hzero : (∑ n ∈ s with ¬(κ n = j), LSeries.term (coeffBlock a κ j) t n) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      rw [Finset.mem_filter] at hn
      rcases eq_or_ne n 0 with rfl | hn0
      · rw [LSeries.term_def, if_pos rfl]
      · rw [LSeries.term_def, if_neg hn0, coeffBlock, if_neg hn.2, zero_div]
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_filter] at hn
    rcases eq_or_ne n 0 with rfl | hn0
    · rw [LSeries.term_def, if_pos rfl, LSeries.term_def, if_pos rfl]
    · rw [LSeries.term_def, if_neg hn0, LSeries.term_def, if_neg hn0, coeffBlock,
        if_pos hn.2]
  rw [Finset.sum_congr rfl hj]
  exact (Finset.sum_fiberwise_of_maps_to hmaps (fun n => LSeries.term a t n)).symm

/-- **The dyadic block decomposition of a Dirichlet polynomial.**  The blocks are the dyadic ranges
`2^j ≤ n < 2^{j+1}`, indexed by `⌊log₂ n⌋`, and there are `⌊log₂ M⌋ + 1` of them. -/
theorem LSeries_eq_sum_dyadic_blocks {a : ℕ → ℂ} {M : ℕ}
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ Finset.Icc 1 M) (t : ℂ) :
    LSeries a t
      = ∑ j ∈ Finset.range (Nat.log 2 M + 1),
          LSeries (coeffBlock a (fun n => Nat.log 2 n) j) t := by
  refine LSeries_eq_sum_blocks hsupp _ _ (fun n hn => ?_) t
  rw [Finset.mem_Icc] at hn
  rw [Finset.mem_range, Nat.lt_succ_iff]
  exact Nat.log_mono_right hn.2

end RHTower.Sieve
end
