import GaloisForLFunctions.RHTower.Sieve.GhsScaleSequence
import GaloisForLFunctions.RHTower.Sieve.AveragedSquarefreeTail

/-!
# The two remaining sizes: the block's plain mass and the long factor's aggregate

Two quantities are still carried as parameters in the per-block bound.  Both are now closed.

The **plain `ℓ²` mass** of the outer weight on a block is bounded by the block's own shape divided
by its left endpoint:

```text
∑_{A < q ≤ B} ‖a_q q^{−σ}‖² ≤ (log B/log(N/B))²·(1/A) ,
```

because the near-diagonal estimate already gives `‖a_q q^{−σ}‖² ≤ (log q)²/(q² log²(N/q))` and the
tail `∑_{q > A} 1/q²` telescopes to `1/A`.  Since `A` is a power of `N` in the argument, this term
is negligible against anything polylogarithmic.

The **long factor's aggregate**, against a uniform bound `V`, collapses by the kernel sum:

```text
∑_{k<m} ‖f(σ+iv_k)‖²·x^{2σ}/‖σ+iv_k‖² ≤ V²·x^{2σ}·(7/σ² + 1) ,
```

uniformly in the number of cells.  This is the step where the height disappears.
-/

noncomputable section

namespace RHTower.Sieve

open Complex Finset

/-- **The plain mass of the outer weight on a block.** -/
theorem sum_plain_mass_ghsOuterBlock_le {f : ℕ → ℂ} (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) {σ : ℝ}
    (hσ : 1 ≤ σ) {A B N : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (hBN : 2 ≤ N / B) :
    ∑ q ∈ Nat.primesLE B \ Nat.primesLE A,
        ‖ghsOuterBlock f N A B q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
      ≤ (Real.log B / Real.log ((N / B : ℕ) : ℝ)) ^ 2 * (1 / (A : ℝ)) := by
  classical
  have hBN2 : (2 : ℝ) ≤ ((N / B : ℕ) : ℝ) := by exact_mod_cast hBN
  have hlogNB : (0 : ℝ) < Real.log ((N / B : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hB1 : 1 ≤ B := le_trans hA hAB
  have hBR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB1
  have hlogB : (0 : ℝ) ≤ Real.log B := Real.log_nonneg hBR
  -- termwise
  have hterm : ∀ q ∈ Nat.primesLE B \ Nat.primesLE A,
      ‖ghsOuterBlock f N A B q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
        ≤ (Real.log B / Real.log ((N / B : ℕ) : ℝ)) ^ 2 * (1 / (q : ℝ) ^ 2) := by
    intro q hq
    have hqp : q.Prime := prime_of_mem_block hq
    have hqB : q ≤ B := by
      rw [Finset.mem_sdiff, Nat.mem_primesLE] at hq
      exact hq.1.1
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqp.two_le
    have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
    have hlogq : (0 : ℝ) < Real.log q := Real.log_pos (by linarith)
    -- from the weighted term bound
    have hw := ghsOuter_weighted_term_le (f := f) (N := N) hbdd hσ hqp
    rw [ghsOuterBlock_eq hq]
    have hdivNq : N / B ≤ N / q := Nat.div_le_div_left hqB hqp.pos
    have hdivR : ((N / B : ℕ) : ℝ) ≤ ((N / q : ℕ) : ℝ) := by exact_mod_cast hdivNq
    have hlogNq : Real.log ((N / B : ℕ) : ℝ) ≤ Real.log ((N / q : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) hdivR
    have hlogqB : Real.log q ≤ Real.log B := Real.log_le_log hq0 (by exact_mod_cast hqB)
    have hsqNq : (Real.log ((N / B : ℕ) : ℝ)) ^ 2 ≤ (Real.log ((N / q : ℕ) : ℝ)) ^ 2 := by
      nlinarith [hlogNB.le, hlogNq]
    -- unwind the weighted bound
    have hfac : (0 : ℝ) < Real.log q / (q : ℝ) := by positivity
    have hstep := mul_le_mul_of_nonneg_left hw hfac.le
    have hL : (Real.log q / (q : ℝ)) * ((q : ℝ) / Real.log q
          * ‖ghsOuter f N q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2)
        = ‖ghsOuter f N q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 := by
      field_simp
    have hR : (Real.log q / (q : ℝ))
          * (Real.log q / ((q : ℝ) * (Real.log ((N / q : ℕ) : ℝ)) ^ 2))
        = (Real.log q) ^ 2 / ((q : ℝ) ^ 2 * (Real.log ((N / q : ℕ) : ℝ)) ^ 2) := by
      rw [div_mul_div_comm]
      congr 1 <;> ring
    have hmass : ‖ghsOuter f N q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
        ≤ (Real.log q) ^ 2 / ((q : ℝ) ^ 2 * (Real.log ((N / q : ℕ) : ℝ)) ^ 2) := by
      linarith [hstep, hL.le, hL.ge, hR.le, hR.ge]
    refine le_trans hmass ?_
    have hLq0 : (0 : ℝ) < Real.log ((N / q : ℕ) : ℝ) := by linarith
    have hb0 : (0 : ℝ) < (q : ℝ) ^ 2 * (Real.log ((N / q : ℕ) : ℝ)) ^ 2 := by positivity
    have hd0 : (0 : ℝ) < (q : ℝ) ^ 2 * (Real.log ((N / B : ℕ) : ℝ)) ^ 2 := by positivity
    have hdb : (q : ℝ) ^ 2 * (Real.log ((N / B : ℕ) : ℝ)) ^ 2
        ≤ (q : ℝ) ^ 2 * (Real.log ((N / q : ℕ) : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsqNq (by positivity)
    have hnum : (Real.log q) ^ 2 ≤ (Real.log B) ^ 2 := by nlinarith [hlogq.le, hlogqB]
    have hchain : (Real.log q) ^ 2 / ((q : ℝ) ^ 2 * (Real.log ((N / q : ℕ) : ℝ)) ^ 2)
        ≤ (Real.log B) ^ 2 / ((q : ℝ) ^ 2 * (Real.log ((N / B : ℕ) : ℝ)) ^ 2) := by
      calc (Real.log q) ^ 2 / ((q : ℝ) ^ 2 * (Real.log ((N / q : ℕ) : ℝ)) ^ 2)
          ≤ (Real.log B) ^ 2 / ((q : ℝ) ^ 2 * (Real.log ((N / q : ℕ) : ℝ)) ^ 2) := by
            gcongr
        _ ≤ (Real.log B) ^ 2 / ((q : ℝ) ^ 2 * (Real.log ((N / B : ℕ) : ℝ)) ^ 2) :=
            div_le_div_of_nonneg_left (by positivity) hd0 hdb
    refine le_trans hchain (le_of_eq ?_)
    field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsub : Nat.primesLE B \ Nat.primesLE A ⊆ Finset.Icc (A + 1) B := by
    intro q hq
    have hqp : q.Prime := prime_of_mem_block hq
    rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hq
    rw [Finset.mem_Icc]
    refine ⟨?_, hq.1.1⟩
    by_contra hc
    exact hq.2 ⟨by omega, hqp⟩
  have htail : ∑ q ∈ Nat.primesLE B \ Nat.primesLE A, (1 : ℝ) / (q : ℝ) ^ 2 ≤ 1 / (A : ℝ) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => by positivity) ?_
    exact sum_Icc_inv_sq_le hA B
  have hc0 : (0 : ℝ) ≤ (Real.log B / Real.log ((N / B : ℕ) : ℝ)) ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left htail hc0

/-- **The long factor's aggregate against a uniform bound.**  The height disappears. -/
theorem sum_cells_aggregate_le_of_bound {σ x V : ℝ} (hσ : 0 < σ) (hx : 0 < x) (hV : 0 ≤ V)
    {g : ℕ → ℂ}
    {n m : ℕ} (hm : m ≤ 2 * n)
    (hgb : ∀ y : ℝ, |y| ≤ (n : ℝ) → ‖LSeries g ((σ : ℂ) + (y : ℝ) * I)‖ ≤ V)
    {v : ℕ → ℝ}
    (hv : ∀ k, k < m →
      v k ∈ Set.Icc (-(n : ℝ) + (k : ℝ) * 1) (-(n : ℝ) + ((k : ℝ) + 1) * 1)) :
    ∑ k ∈ Finset.range m,
        (‖LSeries g ((σ : ℂ) + (v k : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (v k : ℝ) * I‖)) ^ 2
      ≤ V ^ 2 * (x ^ σ) ^ 2 * (7 / σ ^ 2 + 1) := by
  have hxσ : (0 : ℝ) ≤ x ^ σ := Real.rpow_nonneg hx.le σ
  have hterm : ∀ k ∈ Finset.range m,
      (‖LSeries g ((σ : ℂ) + (v k : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (v k : ℝ) * I‖)) ^ 2
        ≤ V ^ 2 * (x ^ σ) ^ 2 * (1 / ‖(σ : ℂ) + (v k : ℝ) * I‖ ^ 2) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hcell := hv k hk
    rw [Set.mem_Icc] at hcell
    have hkR : ((k : ℝ) + 1) ≤ 2 * (n : ℝ) := by
      have h1 : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hk
      have h2 : (m : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hm
      linarith
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have habs : |v k| ≤ (n : ℝ) := by
      rw [abs_le]
      constructor <;> [linarith [hcell.1]; linarith [hcell.2]]
    have hgk := hgb (v k) habs
    have hg0 : (0 : ℝ) ≤ ‖LSeries g ((σ : ℂ) + (v k : ℝ) * I)‖ := norm_nonneg _
    have hker : (0 : ℝ) ≤ ‖(σ : ℂ) + (v k : ℝ) * I‖ := norm_nonneg _
    have heq : (‖LSeries g ((σ : ℂ) + (v k : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (v k : ℝ) * I‖)) ^ 2
        = ‖LSeries g ((σ : ℂ) + (v k : ℝ) * I)‖ ^ 2 * (x ^ σ) ^ 2
            * (1 / ‖(σ : ℂ) + (v k : ℝ) * I‖ ^ 2) := by
      field_simp
    rw [heq]
    have hsq : ‖LSeries g ((σ : ℂ) + (v k : ℝ) * I)‖ ^ 2 ≤ V ^ 2 := by nlinarith [hgk, hg0, hV]
    have hnn : (0 : ℝ) ≤ (x ^ σ) ^ 2 * (1 / ‖(σ : ℂ) + (v k : ℝ) * I‖ ^ 2) := by positivity
    nlinarith [hsq, hnn]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hker := sum_cells_inv_normSq_le (σ := σ) hσ (v := v) (n := n) (m := m) hv
  have hc0 : (0 : ℝ) ≤ V ^ 2 * (x ^ σ) ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left hker hc0

end RHTower.Sieve

end
