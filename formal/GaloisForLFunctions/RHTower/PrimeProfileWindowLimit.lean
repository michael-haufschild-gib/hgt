import GaloisForLFunctions.RHTower.CriticalPrimeProfileSum
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Prime-window limits of critical profiles

Two reusable devices for the all-prime critical limits of
`prime-valuation-dyadic-fermion-normal-cone-law`.

* `tendsto_sum_divProfile` — for any profile `F` whose quotient `t ↦ F t / t` extends continuously
  to `[0,1]` by zero, the critical prime sum `∑_{p ≤ N} F(log p / log N) / p` converges to
  `∫₀¹ F(t) dt / t`.  This is the Mertens prime window applied to `F t / t`, and it is the exact
  shape taken by every local Hellinger defect in the card.

* `tendsto_finsetSum_Icc_zero` — Tannery's theorem on the growing prime window: a doubly indexed
  family which is dominated by a fixed summable bound and vanishes termwise has vanishing window
  sums.  This is the "dominated convergence assembly" that turns a per-prime remainder estimate
  into a vanishing total remainder.

* `tendsto_prod_Icc_of_tendsto_sum_log` — a positive window product converges to the exponential of
  the limit of its window log-sum.
-/

open Filter Topology Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The profile quotient `t ↦ F t / t`, extended by zero at the origin. -/
def divProfile (F : ℝ → ℝ) (t : ℝ) : ℝ := if t = 0 then 0 else F t / t

theorem divProfile_critProfile (u : ℝ) :
    divProfile (fun t => (Real.exp (u * t) - 1) ^ 2) = critProfile u := by
  funext t
  rw [divProfile, critProfile]

/-- The prime window of `F t / t` is the critical prime sum of `F`. -/
theorem mertensPrimeWindow_divProfile_div (F : ℝ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    mertensPrimeWindow (divProfile F) N / Real.log N
      = ∑ n ∈ Finset.Icc 0 N,
          (if n.Prime then F (Real.log n / Real.log N) / (n : ℝ) else 0) := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  rw [mertensPrimeWindow, Finset.sum_div]
  refine Finset.sum_congr rfl fun n hn => ?_
  by_cases hp : n.Prime
  · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.two_le
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hne : Real.log (n : ℝ) / Real.log (N : ℝ) ≠ 0 := by positivity
    rw [if_pos hp, mertensPrimeWeight, if_pos hp, divProfile, if_neg hne]
    field_simp
  · rw [if_neg hp, mertensPrimeWeight, if_neg hp]
    simp

/-- **The critical prime sum of a profile.** -/
theorem tendsto_sum_divProfile (F : ℝ → ℝ)
    (hcont : ContinuousOn (divProfile F) (Set.Icc 0 1)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N,
        (if n.Prime then F (Real.log n / Real.log N) / (n : ℝ) else 0))
      atTop (nhds (∫ t in (0 : ℝ)..1, divProfile F t)) := by
  have hmain := tendsto_mertensPrimeWindow_div_log hcont
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact mertensPrimeWindow_divProfile_div F hN

/-- **Tannery's theorem on the growing prime window.** -/
theorem tendsto_finsetSum_Icc_zero {r : ℕ → ℕ → ℝ} {bound : ℕ → ℝ}
    (hsum : Summable bound) (hb0 : ∀ n, 0 ≤ bound n)
    (hbd : ∀ᶠ N in atTop, ∀ n, |r N n| ≤ bound n)
    (hzero : ∀ n, Tendsto (fun N => r N n) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N, r N n) atTop (nhds 0) := by
  classical
  set f : ℕ → ℕ → ℝ := fun N n => if n ≤ N then r N n else 0 with hf
  have hsupp : ∀ N : ℕ, ∑ n ∈ Finset.Icc 0 N, r N n = ∑' n : ℕ, f N n := by
    intro N
    have hzero' : ∀ n ∉ Finset.Icc 0 N, f N n = 0 := by
      intro n hn
      simp only [Finset.mem_Icc, not_and, not_le] at hn
      rw [hf]
      simp only
      rw [if_neg]
      omega
    rw [tsum_eq_sum hzero']
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_Icc] at hn
    rw [hf]
    simp only
    rw [if_pos hn.2]
  have hlim : ∀ n : ℕ, Tendsto (fun N => f N n) atTop (nhds 0) := by
    intro n
    refine (hzero n).congr' ?_
    filter_upwards [eventually_ge_atTop n] with N hN
    rw [hf]
    simp only
    rw [if_pos hN]
  have hbound : ∀ᶠ N in atTop, ∀ n, ‖f N n‖ ≤ bound n := by
    filter_upwards [hbd] with N hN
    intro n
    rw [hf]
    simp only
    split_ifs with h
    · simpa using hN n
    · simpa using hb0 n
  have := tendsto_tsum_of_dominated_convergence (f := f) (g := fun _ : ℕ => (0 : ℝ))
    hsum hlim hbound
  simpa [hsupp] using this

/-- A positive window product converges to the exponential of the limit of its window log-sum. -/
theorem tendsto_prod_Icc_of_tendsto_sum_log {A : ℕ → ℕ → ℝ} {L : ℝ}
    (hpos : ∀ᶠ N in atTop, ∀ n ∈ Finset.Icc 0 N, 0 < A N n)
    (hlog : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N, Real.log (A N n)) atTop (nhds L)) :
    Tendsto (fun N : ℕ => ∏ n ∈ Finset.Icc 0 N, A N n) atTop (nhds (Real.exp L)) := by
  have hexp := (Real.continuous_exp.tendsto L).comp hlog
  refine hexp.congr' ?_
  filter_upwards [hpos] with N hN
  rw [Function.comp_apply, Real.exp_sum]
  exact Finset.prod_congr rfl fun n hn => Real.exp_log (hN n hn)

end

end RHTower
