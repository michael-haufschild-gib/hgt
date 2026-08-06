import GaloisForLFunctions.RHTower.Sieve.DirichletTwoRegimeBound

/-!
# Depth turns the block saving into a uniform bound

The per-block saving `2560 · N ^ (-1/(3·2^k))` drops below a target `ε` exactly when the block is
deep enough for its order, namely when

```text
3 · 2^k · log (2560/ε)  ≤  log N.
```

Once every block above the split point meets that condition with a common `ε`, the tail contributes
at most `(R - S) · ε` and the whole partial sum takes the final Littlewood shape: a harmonic term
for the low range plus a count of blocks times the uniform saving.
-/

namespace RHTower.Sieve

open Finset

/-- **Depth criterion.**  A block deep enough for its order contributes at most `ε`. -/
theorem block_saving_le_of_log_ge {N k : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε)
    (hdeep : 3 * (2 : ℝ) ^ k * Real.log (2560 / ε) ≤ Real.log (N : ℝ)) :
    2560 * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k))) ≤ ε := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hq : (0 : ℝ) < 3 * (2 : ℝ) ^ k := by positivity
  have hratio : (0 : ℝ) < 2560 / ε := by positivity
  have hkey : Real.log (2560 / ε) ≤ 1 / (3 * (2 : ℝ) ^ k) * Real.log (N : ℝ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hq]
    nlinarith [hdeep]
  have hrpow : (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k)))
      = Real.exp (-(1 / (3 * (2 : ℝ) ^ k)) * Real.log (N : ℝ)) := by
    rw [Real.rpow_def_of_pos hN0]
    ring_nf
  have hexp : Real.exp (-(1 / (3 * (2 : ℝ) ^ k)) * Real.log (N : ℝ))
      ≤ Real.exp (-Real.log (2560 / ε)) := by
    refine Real.exp_le_exp.mpr ?_
    linarith
  have hval : Real.exp (-Real.log (2560 / ε)) = ε / 2560 := by
    rw [Real.exp_neg, Real.exp_log hratio]
    field_simp
  calc 2560 * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k)))
      = 2560 * Real.exp (-(1 / (3 * (2 : ℝ) ^ k)) * Real.log (N : ℝ)) := by rw [hrpow]
    _ ≤ 2560 * Real.exp (-Real.log (2560 / ε)) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = 2560 * (ε / 2560) := by rw [hval]
    _ = ε := by ring

/-- **Final shape.**  A harmonic term for everything below the split point, plus the number of
blocks above it times the uniform per-block saving. -/
theorem norm_dirichlet_partial_two_regime_uniform {t : ℝ} {A S R : ℕ} (hA : 1 ≤ A) (hSR : S ≤ R)
    {ε : ℝ}
    (hb : ∀ r, S ≤ r → r < R →
      ‖∑ n ∈ Finset.Ico (A * 2 ^ r) (A * 2 ^ (r + 1)),
          (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖ ≤ ε) :
    ‖∑ n ∈ Finset.Ico 1 (A * 2 ^ R), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ (1 + Real.log ((A * 2 ^ S - 1 : ℕ) : ℝ)) + ((R - S : ℕ) : ℝ) * ε := by
  have hmain := norm_dirichlet_partial_two_regime (t := t) hA hSR (fun _ => ε) hb
  have hconst : ∑ _r ∈ Finset.Ico S R, (ε : ℝ) = ((R - S : ℕ) : ℝ) * ε := by
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  rw [hconst] at hmain
  exact hmain

end RHTower.Sieve
