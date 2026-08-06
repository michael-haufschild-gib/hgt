import GaloisForLFunctions.RHTower.Sieve.DirichletSigmaHead

/-!
# Depth off the line, and the uniform tail

Off the line the per-block saving carries the factor `N^(1-σ)`, so the depth criterion acquires the
width term: the block contributes at most `ε` once

```text
(1/(3·2^k) - (1-σ)) · log N  ≥  log (2560/ε).
```

The bracket is positive exactly when `1 - σ < 1/(3·2^k)`, so the estimate survives off the line only
within that distance of `Re s = 1`.  That distance is what a zero-free region's width will be: the
saving exponent `1/(3·2^k)` of the derivative test is the same quantity that limits how far left the
rectangle may reach.
-/

namespace RHTower.Sieve

open Finset

/-- **Depth criterion off the line.**  The width `1 - σ` is subtracted from the saving exponent. -/
theorem block_sigma_saving_le_of_log_ge {σ : ℝ} {N k : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε)
    (hdeep : Real.log (2560 / ε)
      ≤ (1 / (3 * (2 : ℝ) ^ k) - (1 - σ)) * Real.log (N : ℝ)) :
    2560 * (N : ℝ) ^ (1 - σ) * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k))) ≤ ε := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hratio : (0 : ℝ) < 2560 / ε := by positivity
  have hmerge : (N : ℝ) ^ (1 - σ) * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k)))
      = Real.exp (((1 - σ) - 1 / (3 * (2 : ℝ) ^ k)) * Real.log (N : ℝ)) := by
    rw [← Real.rpow_add hN0, Real.rpow_def_of_pos hN0]
    ring_nf
  have hexp : Real.exp (((1 - σ) - 1 / (3 * (2 : ℝ) ^ k)) * Real.log (N : ℝ))
      ≤ Real.exp (-Real.log (2560 / ε)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hdeep]
  have hval : Real.exp (-Real.log (2560 / ε)) = ε / 2560 := by
    rw [Real.exp_neg, Real.exp_log hratio]
    field_simp
  calc 2560 * (N : ℝ) ^ (1 - σ) * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k)))
      = 2560 * ((N : ℝ) ^ (1 - σ) * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k)))) := by ring
    _ = 2560 * Real.exp (((1 - σ) - 1 / (3 * (2 : ℝ) ^ k)) * Real.log (N : ℝ)) := by rw [hmerge]
    _ ≤ 2560 * Real.exp (-Real.log (2560 / ε)) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = 2560 * (ε / 2560) := by rw [hval]
    _ = ε := by ring

/-- **Uniform tail off the line.**  A single head term plus the number of blocks times the uniform
saving. -/
theorem norm_dirichlet_sigma_partial_uniform {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {C R : ℕ} (hC : 3 ≤ C) {ε : ℝ}
    (hb : ∀ r < R,
      ‖∑ n ∈ Finset.Ico (C * 2 ^ r) (C * 2 ^ (r + 1)),
          (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖ ≤ ε) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (C * 2 ^ R), (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ (1 + (((C - 1 : ℕ) : ℝ) ^ (1 - σ) - 1) / (1 - σ) + ((C - 1 : ℕ) : ℝ) ^ (-σ))
        + (R : ℝ) * ε := by
  have hmain := norm_dirichlet_sigma_partial_of_blockBound hσ0 hσ1 hC (fun _ => ε) hb
  have hconst : ∑ _r ∈ Finset.range R, (ε : ℝ) = (R : ℝ) * ε := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hconst] at hmain
  exact hmain

end RHTower.Sieve
