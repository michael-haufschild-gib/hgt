import GaloisForLFunctions.RHTower.Sieve.PrimeRangeSplit
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Dominated vanishing of prime sums over a growing range

An all-prime limit produces sums whose *range* and whose *summands* both move with the scale:

`Σ_{p ≤ N} a N p`,   `a N p → 0` for each fixed `p`,   `|a N p| ≤ b p` with `Σ b < ∞`.

Such a sum vanishes.  The proof is the usual two-step split — a fixed head where each term dies,
and a tail controlled by the summable majorant — but it is worth isolating, because every remainder
term of an all-prime profile limit has exactly this shape: bounded by `C/p²` uniformly, and
vanishing for each fixed prime because the exponent coordinate `log p / log N` tends to `0`.
-/

namespace RHTower.Sieve

open Filter Finset
open scoped Topology

noncomputable section

theorem sum_le_tsum_nat_add {b : ℕ → ℝ} (hb : Summable b) (hbnn : ∀ p, 0 ≤ b p)
    (K M : ℕ) :
    ∑ k ∈ Finset.range M, b (k + K) ≤ ∑' k, b (k + K) := by
  exact Summable.sum_le_tsum _ (fun k _ => hbnn _) ((summable_nat_add_iff K).2 hb)

/-- The part of a prime range above a cut is dominated by the tail of the majorant. -/
theorem sum_sdiff_primesLE_le_tail {b : ℕ → ℝ} (hb : Summable b) (hbnn : ∀ p, 0 ≤ b p)
    (K N : ℕ) :
    ∑ p ∈ Nat.primesLE N \ Nat.primesLE K, b p ≤ ∑' k, b (k + (K + 1)) := by
  classical
  have hsub : Nat.primesLE N \ Nat.primesLE K ⊆ Finset.Ico (K + 1) (N + 1) := by
    intro p hp
    rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hp
    obtain ⟨⟨hpN, hprime⟩, hnot⟩ := hp
    rw [Finset.mem_Ico]
    refine ⟨?_, by omega⟩
    by_contra hcon
    exact hnot ⟨by omega, hprime⟩
  have hstep : ∑ p ∈ Nat.primesLE N \ Nat.primesLE K, b p
      ≤ ∑ p ∈ Finset.Ico (K + 1) (N + 1), b p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hbnn p)
  refine le_trans hstep ?_
  rw [Finset.sum_Ico_eq_sum_range]
  have hcongr : ∑ k ∈ Finset.range (N + 1 - (K + 1)), b (K + 1 + k)
      = ∑ k ∈ Finset.range (N + 1 - (K + 1)), b (k + (K + 1)) := by
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Nat.add_comm]
  rw [hcongr]
  exact sum_le_tsum_nat_add hb hbnn (K + 1) _

/-- **Dominated vanishing of prime sums over a growing range.** -/
theorem tendsto_sum_primesLE_of_dominated
    {a : ℕ → ℕ → ℝ} {b : ℕ → ℝ} (hb : Summable b) (hbnn : ∀ p, 0 ≤ b p)
    (hdom : ∀ N p, |a N p| ≤ b p)
    (hzero : ∀ p, Tendsto (fun N => a N p) atTop (𝓝 0)) :
    Tendsto (fun N => ∑ p ∈ Nat.primesLE N, a N p) atTop (𝓝 0) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  -- choose a cut past which the majorant tail is small
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∑' k, b (k + (K + 1)) < ε / 2 := by
    have htail : Tendsto (fun i : ℕ => ∑' k, b (k + i)) atTop (𝓝 0) :=
      tendsto_sum_nat_add b
    obtain ⟨i, hi⟩ := eventually_atTop.1 (htail.eventually_lt_const hhalf)
    exact ⟨i, hi (i + 1) (by omega)⟩
  -- the fixed head vanishes
  have hhead : Tendsto (fun N => ∑ p ∈ Nat.primesLE K, |a N p|) atTop (𝓝 0) := by
    have h : Tendsto (fun N => ∑ p ∈ Nat.primesLE K, |a N p|) atTop
        (𝓝 (∑ p ∈ Nat.primesLE K, (0 : ℝ))) := by
      refine tendsto_finsetSum _ ?_
      intro p _
      simpa using (hzero p).abs
    simpa using h
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hhead.eventually_lt_const hhalf)
  refine ⟨max M K, fun N hN => ?_⟩
  have hNM : M ≤ N := le_trans (le_max_left _ _) hN
  have hNK : K ≤ N := le_trans (le_max_right _ _) hN
  have hsub : Nat.primesLE K ⊆ Nat.primesLE N := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hsplit : ∑ p ∈ Nat.primesLE N, |a N p|
      = ∑ p ∈ Nat.primesLE K, |a N p| + ∑ p ∈ Nat.primesLE N \ Nat.primesLE K, |a N p| := by
    rw [← Finset.sum_sdiff hsub]
    ring
  have htailbd : ∑ p ∈ Nat.primesLE N \ Nat.primesLE K, |a N p| ≤ ∑' k, b (k + (K + 1)) := by
    refine le_trans (Finset.sum_le_sum ?_) (sum_sdiff_primesLE_le_tail hb hbnn K N)
    intro p _
    exact hdom N p
  have hheadbd : ∑ p ∈ Nat.primesLE K, |a N p| < ε / 2 := hM N hNM
  rw [Real.dist_eq, sub_zero]
  calc |∑ p ∈ Nat.primesLE N, a N p| ≤ ∑ p ∈ Nat.primesLE N, |a N p| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p ∈ Nat.primesLE K, |a N p| + ∑ p ∈ Nat.primesLE N \ Nat.primesLE K, |a N p| := hsplit
    _ < ε / 2 + ε / 2 := by
        exact add_lt_add_of_lt_of_le hheadbd (le_trans htailbd hK.le)
    _ = ε := by ring

end

end RHTower.Sieve
