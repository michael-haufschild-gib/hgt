import GaloisForLFunctions.RHTower.Sieve.DirichletSigmaEndpoints

/-!
# A strip of uniform validity

The depth criterion off the line asks for `log (2560/ε) ≤ (1/(3·2^K) - (1-σ))·log N`, whose bracket
degenerates as `σ` approaches `1 - 1/(3·2^K)`.  Halving the allowance decouples the two: on the
strip

```text
1 - 1/(6·2^K)  ≤  σ  <  1,
```

the bracket is at least `1/(6·2^K)`, so a single depth check — free of `σ` — serves every `σ` in the
strip.

That is the form a zero-free region argument consumes: a growth bound valid uniformly on a rectangle
left of `Re s = 1`, whose width is a fixed function of the order.
-/

namespace RHTower.Sieve

open Finset

/-- **Uniform rectangle bound on a strip.**  One depth check, free of `σ`, serves the whole strip
`1 - 1/(6·2^K) ≤ σ < 1`. -/
theorem norm_dirichlet_sigma_littlewood_strip {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (ht : 0 < t)
    {C R : ℕ} (hC : 3 ≤ C) (hR : 1 ≤ R) (K : ℕ) {ε : ℝ} (hε : 0 < ε) (hK : 2 ≤ K)
    (hstrip : 1 - σ ≤ 1 / (6 * (2 : ℝ) ^ K))
    (hfac0 : Nat.factorial (K - 1) ≤ C)
    (hlowTop : 8 * Real.pi * ((C * 2 ^ (R - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh0 : t ≤ 2 * Real.pi * 2 ^ K * ((C : ℕ) : ℝ) ^ (K - 1) * ((C : ℕ) : ℝ) ^ (-(1 / 3) : ℝ))
    (hdeepUnif : Real.log (2560 / ε) ≤ 1 / (6 * (2 : ℝ) ^ K) * Real.log ((C : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (C * 2 ^ R), (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ (1 + (((C - 1 : ℕ) : ℝ) ^ (1 - σ) - 1) / (1 - σ) + ((C - 1 : ℕ) : ℝ) ^ (-σ))
        + (R : ℝ) * ε := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  have hhalf : 1 / (6 * (2 : ℝ) ^ K) ≤ 1 / (3 * (2 : ℝ) ^ K) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    linarith
  have hwidth : 1 - σ ≤ 1 / (3 * (2 : ℝ) ^ K) := le_trans hstrip hhalf
  have hlogC : 0 ≤ Real.log ((C : ℕ) : ℝ) := by
    refine Real.log_nonneg ?_
    have : (3 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
    linarith
  have hbracket : 1 / (6 * (2 : ℝ) ^ K) ≤ 1 / (3 * (2 : ℝ) ^ K) - (1 - σ) := by
    have hsum : 1 / (3 * (2 : ℝ) ^ K) = 1 / (6 * (2 : ℝ) ^ K) + 1 / (6 * (2 : ℝ) ^ K) := by
      field_simp
      ring
    linarith [hstrip, hsum]
  refine norm_dirichlet_sigma_littlewood_endpoints hσ0 hσ1 ht hC hR K hε hK hwidth hfac0
    hlowTop hhigh0 ?_
  calc Real.log (2560 / ε) ≤ 1 / (6 * (2 : ℝ) ^ K) * Real.log ((C : ℕ) : ℝ) := hdeepUnif
    _ ≤ (1 / (3 * (2 : ℝ) ^ K) - (1 - σ)) * Real.log ((C : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hbracket hlogC

end RHTower.Sieve
