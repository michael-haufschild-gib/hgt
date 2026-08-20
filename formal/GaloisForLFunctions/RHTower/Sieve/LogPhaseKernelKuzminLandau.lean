import GaloisForLFunctions.RHTower.Sieve.LogPhaseKernelBound
import GaloisForLFunctions.RHTower.Sieve.MaynardKuzminLandauFactor

/-!
# The logarithmic-phase kernel with Kuzmin–Landau decay

`Sieve/LogPhaseKernelBound.norm_sum_Icc_logPhase_le` assembles the dyadic blocks with the
second-derivative envelope alone, and the resulting kernel bound `3072·M/√t` is the wrong shape for
Halász–Montgomery: its supremum over `|t| ≥ 1` is `3072·M`, so the row mass `2N + C·|E|` only beats
the trivial bound when `|E|` is smaller than an absolute constant.

Kuzmin–Landau gives the reciprocal decay `6π·2^j/t` on a dyadic block, but only above the first
derivative resonance `3t ≤ 4π·2^j`.  Splitting the dyadic range there — second derivative below,
Kuzmin–Landau above — produces the classical shape

```text
   ‖∑_{n ≤ M} n^{−it}‖  ≤  J₀·214√t + 1536·2^{J₀+1}/√t + 12π·M/t + log₂M + 1 ,
```

whose supremum over `1 ≤ t ≤ 2T` is `O(√T log T)` once `2^{J₀} ≍ t`, and that is what makes the row
mass `N log T + |E|√T log T`.
-/

namespace RHTower.Sieve

open Finset

private theorem div_le_div_right_of_le {a b c : ℝ} (h : a ≤ b) (hc : 0 < c) : a / c ≤ b / c := by
  have hnn : (0 : ℝ) ≤ (b - a) / c := div_nonneg (by linarith) hc.le
  have hdiff : (b - a) / c = b / c - a / c := by ring
  rw [hdiff] at hnn
  linarith

/-- **Kuzmin–Landau on one dyadic block of `[1, M]`.** -/
theorem norm_dyadic_block_le_kuzminLandau (M j : ℕ) {t : ℝ} (ht : 0 < t)
    (hKL : 3 * t ≤ 4 * Real.pi * (2 : ℝ) ^ j) :
    ‖∑ n ∈ (Finset.Icc 1 M).filter (fun n => Nat.log 2 n = j),
        ((n : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ 6 * Real.pi * (2 : ℝ) ^ j / t + 1 := by
  classical
  have hrhs : (0 : ℝ) ≤ 6 * Real.pi * (2 : ℝ) ^ j / t + 1 := by
    have := Real.pi_pos
    positivity
  set N : ℕ := 2 ^ j with hNdef
  set B : ℕ := min (2 ^ (j + 1)) (M + 1) with hBdef
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hNR : ((N : ℕ) : ℝ) = (2 : ℝ) ^ j := by rw [hNdef]; push_cast; ring
  rw [dyadic_block_eq M j, ← hNdef, ← hBdef]
  rcases le_or_gt B N with hemp | hne
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, norm_zero]
    exact hrhs
  · set L : ℕ := B - N with hLdef
    have hL1 : 1 ≤ L := by omega
    have hLN : L ≤ N := by
      have h2 : B ≤ 2 ^ (j + 1) := min_le_left _ _
      have h3 : (2 : ℕ) ^ (j + 1) = 2 * N := by rw [hNdef, pow_succ]; ring
      omega
    have hreindex : ∑ n ∈ Finset.Ico N B, ((n : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))
        = ∑ k ∈ Finset.range L, ((N + k : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ))) := by
      rw [Finset.sum_Ico_eq_sum_range]
    rw [hreindex]
    have hconv : ∑ k ∈ Finset.range L, ((N + k : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))
        = ∑ k ∈ Finset.range L,
            Complex.exp (((2 * Real.pi * logPhase t ((N : ℝ) + k) : ℝ) : ℂ) * Complex.I) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [natCast_cpow_neg_I_mul t (N + k) (by omega)]
      congr 3
      push_cast
      ring
    rw [hconv]
    have hKL' : 3 * t ≤ 4 * Real.pi * ((N : ℕ) : ℝ) := by rw [hNR]; exact hKL
    have hbase := norm_logPhase_dyadic_prefix_le_kuzminLandau t ht N L hN1 hL1 hLN hKL'
    refine hbase.trans (le_of_eq ?_)
    rw [hNR]

/-- **The kernel bound with the dyadic range split at the Kuzmin–Landau threshold.** -/
theorem norm_sum_Icc_logPhase_le_split {M : ℕ} (hM : 1 ≤ M) {t : ℝ} (ht : 0 < t) (J₀ : ℕ)
    (hJ₀ : 3 * t ≤ 4 * Real.pi * (2 : ℝ) ^ J₀) :
    ‖∑ n ∈ Finset.Icc 1 M, ((n : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ (J₀ : ℝ) * (214 * Real.sqrt t) + 1536 * (2 * (2 : ℝ) ^ J₀) / Real.sqrt t
        + (12 * Real.pi * (M : ℝ) / t + ((Nat.log 2 M : ℝ) + 1)) := by
  classical
  have hsq : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  refine le_trans (norm_sum_Icc_le_sum_dyadic_blocks
    (fun n => ((n : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ))))) ?_
  set S : Finset ℕ := Finset.range (Nat.log 2 M + 1) with hS
  set g : ℕ → ℝ := fun j =>
    ‖∑ n ∈ (Finset.Icc 1 M).filter (fun n => Nat.log 2 n = j),
        ((n : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ with hg
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun j => j < J₀) g
  rw [← hsplit]
  have hlow : ∑ j ∈ S.filter (fun j => j < J₀), g j
      ≤ (J₀ : ℝ) * (214 * Real.sqrt t) + 1536 * (2 * (2 : ℝ) ^ J₀) / Real.sqrt t := by
    have hterm : ∀ j ∈ S.filter (fun j => j < J₀),
        g j ≤ 214 * Real.sqrt t + 1536 * ((2 : ℝ) ^ j / Real.sqrt t) := fun j _ =>
      norm_dyadic_block_le_affine M j ht
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hcard : ((S.filter (fun j => j < J₀)).card : ℝ) ≤ (J₀ : ℝ) := by
      have hsub : S.filter (fun j => j < J₀) ⊆ Finset.range J₀ := by
        intro j hj
        rw [Finset.mem_filter] at hj
        exact Finset.mem_range.2 hj.2
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      exact_mod_cast this
    have hpow : ∑ j ∈ S.filter (fun j => j < J₀), ((2 : ℝ) ^ j / Real.sqrt t)
        ≤ (2 * (2 : ℝ) ^ J₀) / Real.sqrt t := by
      rw [← Finset.sum_div]
      refine div_le_div_right_of_le ?_ hsq
      have hsub : S.filter (fun j => j < J₀) ⊆ Finset.range J₀ := by
        intro j hj
        rw [Finset.mem_filter] at hj
        exact Finset.mem_range.2 hj.2
      have hmono : ∑ j ∈ S.filter (fun j => j < J₀), (2 : ℝ) ^ j
          ≤ ∑ j ∈ Finset.range J₀, (2 : ℝ) ^ j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
      have hgeom : ∑ j ∈ Finset.range J₀, (2 : ℝ) ^ j = 2 ^ J₀ - 1 := by
        rw [geom_sum_eq (by norm_num)]
        ring
      rw [hgeom] at hmono
      have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ J₀ := by positivity
      linarith
    have hid : ∑ j ∈ S.filter (fun j => j < J₀),
          (214 * Real.sqrt t + 1536 * ((2 : ℝ) ^ j / Real.sqrt t))
        = ((S.filter (fun j => j < J₀)).card : ℝ) * (214 * Real.sqrt t)
          + 1536 * ∑ j ∈ S.filter (fun j => j < J₀), ((2 : ℝ) ^ j / Real.sqrt t) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [hid]
    have hsq0 : (0 : ℝ) ≤ 214 * Real.sqrt t := by positivity
    have hA : ((S.filter (fun j => j < J₀)).card : ℝ) * (214 * Real.sqrt t)
        ≤ (J₀ : ℝ) * (214 * Real.sqrt t) := mul_le_mul_of_nonneg_right hcard hsq0
    have hC : 1536 * ((2 * (2 : ℝ) ^ J₀) / Real.sqrt t)
        = 1536 * (2 * (2 : ℝ) ^ J₀) / Real.sqrt t := by ring
    linarith [hA, hpow, hC]
  have hhigh : ∑ j ∈ S.filter (fun j => ¬ j < J₀), g j
      ≤ 12 * Real.pi * (M : ℝ) / t + ((Nat.log 2 M : ℝ) + 1) := by
    have hterm : ∀ j ∈ S.filter (fun j => ¬ j < J₀),
        g j ≤ 1 + (6 * Real.pi / t) * (2 : ℝ) ^ j := by
      intro j hj
      rw [Finset.mem_filter] at hj
      have hJj : J₀ ≤ j := by omega
      have hmono : (2 : ℝ) ^ J₀ ≤ (2 : ℝ) ^ j :=
        pow_le_pow_right₀ (by norm_num) hJj
      have hKL : 3 * t ≤ 4 * Real.pi * (2 : ℝ) ^ j := by nlinarith [hJ₀, hmono, hpi]
      refine le_trans (norm_dyadic_block_le_kuzminLandau M j ht hKL) (le_of_eq ?_)
      field_simp
      ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hb : (0 : ℝ) ≤ 6 * Real.pi / t := by positivity
    have hsub : S.filter (fun j => ¬ j < J₀) ⊆ S := Finset.filter_subset _ _
    have hstep : ∑ j ∈ S.filter (fun j => ¬ j < J₀), (1 + (6 * Real.pi / t) * (2 : ℝ) ^ j)
        ≤ ∑ j ∈ S, (1 + (6 * Real.pi / t) * (2 : ℝ) ^ j) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    refine hstep.trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hS,
      Finset.card_range]
    have hgeom : ∑ j ∈ Finset.range (Nat.log 2 M + 1), (2 : ℝ) ^ j
        = 2 ^ (Nat.log 2 M + 1) - 1 := by
      rw [geom_sum_eq (by norm_num)]
      ring
    rw [hgeom]
    have hMpow : (2 : ℝ) ^ (Nat.log 2 M) ≤ (M : ℝ) := by
      have := Nat.pow_log_le_self 2 (by omega : M ≠ 0)
      exact_mod_cast this
    have hpow2 : (2 : ℝ) ^ (Nat.log 2 M + 1) = 2 * (2 : ℝ) ^ (Nat.log 2 M) := by
      rw [pow_succ]; ring
    rw [hpow2]
    have hMR : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
    have : (6 * Real.pi / t) * (2 * (2 : ℝ) ^ (Nat.log 2 M) - 1)
        ≤ 12 * Real.pi * (M : ℝ) / t := by
      have hle : 6 * Real.pi * (2 * (2 : ℝ) ^ (Nat.log 2 M) - 1) ≤ 12 * Real.pi * (M : ℝ) := by
        nlinarith [hMpow, hpi]
      have hid2 : (6 * Real.pi / t) * (2 * (2 : ℝ) ^ (Nat.log 2 M) - 1)
          = 6 * Real.pi * (2 * (2 : ℝ) ^ (Nat.log 2 M) - 1) / t := by ring
      rw [hid2]
      exact div_le_div_right_of_le hle ht
    push_cast
    linarith
  linarith

end RHTower.Sieve
