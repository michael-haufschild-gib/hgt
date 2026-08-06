import GaloisForLFunctions.RHTower.Sieve.DirichletSigmaStrip

/-!
# The canonical target on the strip

The uniform depth check `log (2560/ε) ≤ (1/(6·2^K))·log C` is a lower bound on `ε`, so the best
admissible target makes it an equality:

```text
ε₀ = 2560 · exp (- log C / (6·2^K)).
```

Substituting it removes the last free parameter of the rectangle estimate apart from the split point
and the number of blocks.
-/

namespace RHTower.Sieve

open Finset

/-- The smallest target the uniform depth check permits at split point `C` and order `K`. -/
noncomputable def stripTargetEps (C K : ℕ) : ℝ :=
  2560 * Real.exp (-(Real.log (C : ℝ) / (6 * (2 : ℝ) ^ K)))

theorem stripTargetEps_pos (C K : ℕ) : 0 < stripTargetEps C K := by
  rw [stripTargetEps]
  positivity

theorem stripTargetEps_le {C : ℕ} (hC : 1 ≤ C) (K : ℕ) : stripTargetEps C K ≤ 2560 := by
  have hlogC : 0 ≤ Real.log (C : ℝ) := by
    refine Real.log_nonneg ?_
    exact_mod_cast hC
  have hx : 0 ≤ Real.log (C : ℝ) / (6 * (2 : ℝ) ^ K) := by positivity
  have hexp : Real.exp (-(Real.log (C : ℝ) / (6 * (2 : ℝ) ^ K))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  rw [stripTargetEps]
  nlinarith [hexp]

/-- The canonical target meets the uniform depth check, with equality. -/
theorem stripTargetEps_deep (C K : ℕ) :
    Real.log (2560 / stripTargetEps C K) = 1 / (6 * (2 : ℝ) ^ K) * Real.log (C : ℝ) := by
  have hden : (0 : ℝ) < 6 * (2 : ℝ) ^ K := by positivity
  have hratio : 2560 / stripTargetEps C K
      = Real.exp (Real.log (C : ℝ) / (6 * (2 : ℝ) ^ K)) := by
    rw [stripTargetEps, Real.exp_neg]
    field_simp
  rw [hratio, Real.log_exp]
  field_simp

/-- **Rectangle bound at the canonical target.**  Only the split point, the number of blocks and the
order remain. -/
theorem norm_dirichlet_sigma_littlewood_canonical {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (ht : 0 < t) {C R : ℕ} (hC : 3 ≤ C) (hR : 1 ≤ R) (K : ℕ) (hK : 2 ≤ K)
    (hstrip : 1 - σ ≤ 1 / (6 * (2 : ℝ) ^ K))
    (hfac0 : Nat.factorial (K - 1) ≤ C)
    (hlowTop : 8 * Real.pi * ((C * 2 ^ (R - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh0 : t ≤ 2 * Real.pi * 2 ^ K * ((C : ℕ) : ℝ) ^ (K - 1) * ((C : ℕ) : ℝ) ^ (-(1 / 3) : ℝ)) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (C * 2 ^ R), (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ (1 + (((C - 1 : ℕ) : ℝ) ^ (1 - σ) - 1) / (1 - σ) + ((C - 1 : ℕ) : ℝ) ^ (-σ))
        + (R : ℝ) * stripTargetEps C K :=
  norm_dirichlet_sigma_littlewood_strip hσ0 hσ1 ht hC hR K (stripTargetEps_pos C K) hK hstrip
    hfac0 hlowTop hhigh0 (le_of_eq (stripTargetEps_deep C K))

end RHTower.Sieve
