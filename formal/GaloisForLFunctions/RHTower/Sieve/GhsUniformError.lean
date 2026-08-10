import GaloisForLFunctions.RHTower.Sieve.GhsBlockExplicit

/-!
# One truncation error for every block

`ghsPerronError N B M n σ` depends on the block through `B` and `M`, but only through
`log(B·M·N)`, and every block has `B ≤ N` and `M ≤ N`.  So `log(B·M·N) ≤ 3·log N` and a single

```text
ghsUniformError N n σ := ((3 log N)⁴/(log 2)³)·(N+½)^σ·(5(1 + 3 log N) + 4(1 + log N))/(π·n)
```

dominates all of them.  This is what lets the capstone — which asks for one bound valid for every
block — be applied without generalising it to a per-block sum: the cost of using the maximum rather
than the individual errors is a single factor `K ≍ log log N`, which the final division by `log N`
absorbs.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- The truncation error at the crudest admissible length. -/
def ghsUniformError (N n : ℕ) (σ : ℝ) : ℝ :=
  ((3 * Real.log N) ^ 4 / (Real.log 2) ^ 3)
    * ((N : ℝ) + 1 / 2) ^ σ
    * (5 * (1 + 3 * Real.log N) + 4 * (1 + Real.log N))
    / (Real.pi * ((n : ℝ) * 2 ^ (0 : ℕ)))

/-- **Every block's truncation error is at most the uniform one.** -/
theorem ghsPerronError_le_uniform {N B M n : ℕ} {σ : ℝ} (hN : 1 ≤ N)
    (hB : B ≤ N) (hM : M ≤ N) :
    ghsPerronError N B M n σ ≤ ghsUniformError N n σ := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1
  have hcube : ((B * (M * N) : ℕ) : ℝ) ≤ (N : ℝ) ^ 3 := by
    have hle : B * (M * N) ≤ N * (N * N) := Nat.mul_le_mul hB (Nat.mul_le_mul hM le_rfl)
    have : ((B * (M * N) : ℕ) : ℝ) ≤ ((N * (N * N) : ℕ) : ℝ) := by exact_mod_cast hle
    calc ((B * (M * N) : ℕ) : ℝ) ≤ ((N * (N * N) : ℕ) : ℝ) := this
      _ = (N : ℝ) ^ 3 := by push_cast; ring
  have hlog3 : Real.log ((B * (M * N) : ℕ) : ℝ) ≤ 3 * Real.log N := by
    rcases eq_or_lt_of_le (Nat.zero_le (B * (M * N))) with h | h
    · rw [← h]
      simp only [Nat.cast_zero, Real.log_zero]
      linarith
    · have hpos : (1 : ℝ) ≤ ((B * (M * N) : ℕ) : ℝ) := by exact_mod_cast h
      have hstep : Real.log ((B * (M * N) : ℕ) : ℝ) ≤ Real.log ((N : ℝ) ^ 3) :=
        Real.log_le_log (by linarith) hcube
      rwa [Real.log_pow, Nat.cast_ofNat] at hstep
  have hlog0 : (0 : ℝ) ≤ Real.log ((B * (M * N) : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hxσ : (0 : ℝ) ≤ ((N : ℝ) + 1 / 2) ^ σ := Real.rpow_nonneg (by linarith) σ
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hden : (0 : ℝ) < Real.pi * ((n : ℝ) * 2 ^ (0 : ℕ)) ∨
      Real.pi * ((n : ℝ) * 2 ^ (0 : ℕ)) = 0 := by
    rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) n) with h | h
    · right; rw [← h]; ring
    · left; have hpi := Real.pi_pos; positivity
  rw [ghsPerronError, ghsUniformError]
  have hnum : ((Real.log ((B * (M * N) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
        * ((N : ℝ) + 1 / 2) ^ σ
        * (5 * (1 + Real.log ((B * (M * N) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
      ≤ ((3 * Real.log N) ^ 4 / (Real.log 2) ^ 3)
        * ((N : ℝ) + 1 / 2) ^ σ
        * (5 * (1 + 3 * Real.log N) + 4 * (1 + Real.log N)) := by
    have hp4 : (Real.log ((B * (M * N) : ℕ) : ℝ)) ^ 4 ≤ (3 * Real.log N) ^ 4 :=
      pow_le_pow_left₀ hlog0 hlog3 4
    have hfac1 : ((Real.log ((B * (M * N) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
          * ((N : ℝ) + 1 / 2) ^ σ
        ≤ ((3 * Real.log N) ^ 4 / (Real.log 2) ^ 3) * ((N : ℝ) + 1 / 2) ^ σ := by
      refine mul_le_mul_of_nonneg_right ?_ hxσ
      exact div_le_div_of_nonneg_right hp4 (by positivity)
    have hfac2 : 5 * (1 + Real.log ((B * (M * N) : ℕ) : ℝ)) + 4 * (1 + Real.log N)
        ≤ 5 * (1 + 3 * Real.log N) + 4 * (1 + Real.log N) := by linarith
    have h20 : (0 : ℝ) ≤ 5 * (1 + Real.log ((B * (M * N) : ℕ) : ℝ)) + 4 * (1 + Real.log N) := by
      linarith
    have h10 : (0 : ℝ) ≤ ((3 * Real.log N) ^ 4 / (Real.log 2) ^ 3)
        * ((N : ℝ) + 1 / 2) ^ σ := by positivity
    calc ((Real.log ((B * (M * N) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
          * ((N : ℝ) + 1 / 2) ^ σ
          * (5 * (1 + Real.log ((B * (M * N) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
        ≤ (((3 * Real.log N) ^ 4 / (Real.log 2) ^ 3) * ((N : ℝ) + 1 / 2) ^ σ)
            * (5 * (1 + Real.log ((B * (M * N) : ℕ) : ℝ)) + 4 * (1 + Real.log N)) :=
          mul_le_mul_of_nonneg_right hfac1 h20
      _ ≤ (((3 * Real.log N) ^ 4 / (Real.log 2) ^ 3) * ((N : ℝ) + 1 / 2) ^ σ)
            * (5 * (1 + 3 * Real.log N) + 4 * (1 + Real.log N)) :=
          mul_le_mul_of_nonneg_left hfac2 h10
  rcases hden with h | h
  · exact div_le_div_of_nonneg_right hnum h.le
  · rw [h, div_zero, div_zero]

end RHTower.Sieve

end
