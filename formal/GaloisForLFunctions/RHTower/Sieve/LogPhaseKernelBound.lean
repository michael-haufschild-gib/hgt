import GaloisForLFunctions.RHTower.Sieve.DyadicAffineEnvelope
import GaloisForLFunctions.RHTower.Sieve.AdicBlocks

/-!
# The pointwise bound for the logarithmic-phase kernel

Summing the two regimes of the logarithmic phase over the dyadic blocks of `[1, M]` gives

```text
   ‖∑_{n ≤ M} n^{-it}‖  ≤  (⌊log₂ M⌋ + 1)·214·√t  +  3072·M/√t ,
```

with explicit constants and no asymptotic notation.  This is the kernel estimate the integral
Halász–Montgomery bound needs: the first term carries its `log T·T^{1/2}`, the second its `N/T^{1/2}`.
-/

namespace RHTower.Sieve

open Finset

/-- A purely imaginary power of a positive integer has norm one. -/
theorem norm_cpow_imag_eq_one {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    ‖((n : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ = 1 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcast : ((n : ℕ) : ℂ) = ((n : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
  have hre : (-(Complex.I * (t : ℂ))).re = 0 := by simp
  rw [hre, Real.rpow_zero]

/-- **The second-derivative bound on a partial dyadic block.** -/
theorem norm_logPhase_partial_block_le {t : ℝ} (ht : 0 < t) {N L : ℕ} (hN : 1 ≤ N)
    (hL : 1 ≤ L) (hLN : L ≤ N) (hlam : logDyadicLambda N t ≤ 1) :
    ‖∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ logDyadicSecondBound N t := by
  have hspan : N + L ≤ 2 * N + 1 := by omega
  have h := dirichlet_block_bound t ht 2 N L (by omega) hN hL hspan
    (by simpa [logDyadicLambda] using hlam)
  norm_num at h
  have hgoalL : ∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))
      = ∑ x ∈ Finset.range L, ((N : ℂ) + (x : ℂ)) ^ (-(Complex.I * (t : ℂ))) :=
    Finset.sum_congr rfl fun x _ => by push_cast; ring_nf
  rw [hgoalL]
  refine h.trans ?_
  rw [logDyadicSecondBound, logDyadicLambda]
  have hfac : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num
  rw [hfac, mul_one]
  have hLNR : (L : ℝ) ≤ (N : ℝ) := by exact_mod_cast hLN
  have hnn : (0 : ℝ) ≤ (16 * (t / (2 * Real.pi) / (2 * (N : ℝ)) ^ 2)) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  nlinarith [hLNR, hnn]

/-- The `j`-th dyadic block of `[1, M]`, explicitly. -/
theorem dyadic_block_eq (M j : ℕ) :
    (Finset.Icc 1 M).filter (fun n => Nat.log 2 n = j)
      = Finset.Ico (2 ^ j) (min (2 ^ (j + 1)) (M + 1)) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico, lt_min_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, hlog⟩
    refine ⟨?_, ?_, by omega⟩
    · rw [← hlog]; exact Nat.pow_log_le_self 2 (by omega)
    · rw [← hlog]; exact Nat.lt_pow_succ_log_self (by norm_num) n
  · rintro ⟨hlo, hhi, hM⟩
    have hn1 : 1 ≤ n := le_trans Nat.one_le_two_pow hlo
    exact ⟨⟨hn1, by omega⟩, Nat.log_eq_of_pow_le_of_lt_pow hlo hhi⟩

/-- **The affine bound on one dyadic block, unconditionally.** -/
theorem norm_dyadic_block_le_affine (M j : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖∑ n ∈ (Finset.Icc 1 M).filter (fun n => Nat.log 2 n = j),
        ((n : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ 214 * Real.sqrt t + 1536 * ((2 : ℝ) ^ j / Real.sqrt t) := by
  classical
  have hsq : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  have hrhs : (0 : ℝ) ≤ 214 * Real.sqrt t + 1536 * ((2 : ℝ) ^ j / Real.sqrt t) := by positivity
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
    by_cases hlam : logDyadicLambda N t ≤ 1
    · refine le_trans (norm_logPhase_partial_block_le ht hN1 hL1 hLN hlam) ?_
      have := logDyadicSecondBound_le_affine hN1 ht
      rw [hNR] at this
      exact this
    · -- the trivial bound is already affine
      have htriv : ‖∑ k ∈ Finset.range L, ((N + k : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
          ≤ (L : ℝ) := by
        refine le_trans (norm_sum_le _ _) ?_
        have hterm : ∀ k ∈ Finset.range L,
            ‖((N + k : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ = 1 :=
          fun k _ => norm_cpow_imag_eq_one (by omega) t
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          mul_one]
      have hLR : (L : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hLN
      refine le_trans htriv (le_trans hLR ?_)
      have hkey := trivial_le_affine hN1 ht (not_le.1 hlam)
      rw [hNR] at hkey
      rw [hNR]
      exact hkey

/-- **The pointwise kernel bound.**  Summing the affine per-block bound over the `⌊log₂ M⌋ + 1`
dyadic blocks of `[1, M]`. -/
theorem norm_sum_Icc_logPhase_le {M : ℕ} (hM : 1 ≤ M) {t : ℝ} (ht : 0 < t) :
    ‖∑ n ∈ Finset.Icc 1 M, ((n : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ ((Nat.log 2 M : ℝ) + 1) * (214 * Real.sqrt t) + 3072 * (M : ℝ) / Real.sqrt t := by
  have hsq : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  have hb : (0 : ℝ) ≤ 1536 / Real.sqrt t := by positivity
  have hblk : ∀ j ∈ Finset.range (Nat.log 2 M + 1),
      ‖∑ n ∈ (Finset.Icc 1 M).filter (fun n => Nat.log 2 n = j),
          ((n : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
        ≤ 214 * Real.sqrt t + (1536 / Real.sqrt t) * 2 ^ j := by
    intro j _
    refine le_trans (norm_dyadic_block_le_affine M j ht) (le_of_eq ?_)
    field_simp
  have hbase := norm_sum_Icc_le_of_dyadic_bounds hM
    (fun n => ((n : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))) hb hblk
  refine hbase.trans (le_of_eq ?_)
  field_simp
  ring

end RHTower.Sieve
