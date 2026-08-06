import GaloisForLFunctions.RHTower.Sieve.DirichletAssembledBound

/-!
# The canonical target

The depth criterion `3·2^K·log (2560/ε) ≤ σ·log 2` is a lower bound on `ε`, so the best admissible
target is the one making it an equality:

```text
ε₀ = 2560 · exp (- σ log 2 / (3 · 2^K)).
```

Substituting it leaves the estimate a function of `t` and the order `K` alone.
-/

namespace RHTower.Sieve

open Finset

/-- The smallest target the depth criterion permits at split exponent `σ` and order `K`. -/
noncomputable def targetEps (σ K : ℕ) : ℝ :=
  2560 * Real.exp (-((σ : ℝ) * Real.log 2 / (3 * (2 : ℝ) ^ K)))

theorem targetEps_pos (σ K : ℕ) : 0 < targetEps σ K := by
  rw [targetEps]
  positivity

theorem targetEps_le (σ K : ℕ) : targetEps σ K ≤ 2560 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx : 0 ≤ (σ : ℝ) * Real.log 2 / (3 * (2 : ℝ) ^ K) := by positivity
  have hexp : Real.exp (-((σ : ℝ) * Real.log 2 / (3 * (2 : ℝ) ^ K))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  rw [targetEps]
  nlinarith [hexp]

/-- The canonical target meets the depth criterion, with equality. -/
theorem targetEps_deep (σ K : ℕ) :
    3 * (2 : ℝ) ^ K * Real.log (2560 / targetEps σ K) = (σ : ℝ) * Real.log 2 := by
  have hden : (0 : ℝ) < 3 * (2 : ℝ) ^ K := by positivity
  have hratio : 2560 / targetEps σ K
      = Real.exp ((σ : ℝ) * Real.log 2 / (3 * (2 : ℝ) ^ K)) := by
    rw [targetEps, Real.exp_neg]
    field_simp
  rw [hratio, Real.log_exp]
  field_simp

/-- **Assembled bound at the canonical target.**  Only the order `K` remains free. -/
theorem norm_dirichlet_partial_littlewood_canonical {t : ℝ} (ht8 : 8 * Real.pi ≤ t) {K : ℕ}
    (hK : 2 ≤ K) (hbig : 2 * Real.pi * (2 : ℝ) ^ (K : ℕ) ≤ t)
    (hσ1 : 1 ≤ splitExponent t K)
    (hSR : splitExponent t K - 1 < topExponent t)
    (hfac : Nat.factorial (K - 1) ≤ 2 ^ (splitExponent t K)) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (topExponent t + 1)),
        (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 1 + ((Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
            / (((K : ℝ) - 4 / 3) * Real.log 2) + 1) * Real.log 2
        + 3 * Real.log (t / (8 * Real.pi)) / Real.log 2
            * targetEps (splitExponent t K) K :=
  norm_dirichlet_partial_littlewood_assembled ht8 hK hbig
    (targetEps_pos _ _) (targetEps_le _ _) hσ1 hSR hfac
    (le_of_eq (targetEps_deep (splitExponent t K) K))

end RHTower.Sieve
