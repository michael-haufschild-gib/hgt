import GaloisForLFunctions.RHTower.Sieve.DyadicMeanSquareGallagher
import GaloisForLFunctions.RHTower.Sieve.MaximalWindowReduction

/-!
# The maximal-window mean square from one uniform dyadic bound

`sum_maxWindowSq_succ_le_dyadic` expresses the maximal-window mean square through `2^J` translates of
`dyadicMeanSquare f 1` and, at each level `j < J`, `2^{J−j}` translates of `dyadicMeanSquare f 2^j`.
A single bound `C` valid for every level and every translate therefore suffices:

```text
∑_{y ∈ [A+1, B+1]} maxWindowSq f H y  ≤  (J+1)²·2^J·C ,      H + 1 ≤ 2^J .
```

The two factors `J + 1` are the Rademacher–Menshov losses — one from Cauchy–Schwarz, one from the
sum over levels — and `2^J ≍ H` counts the translates.  Against the target `o(H²√x)` this leaves
`C = o(H√x/(log H)²)` to be supplied by `dyadicMeanSquare_le_gallagher`, i.e. by a bound on
`‖logPoly f (Icc 1 M) w‖²`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The maximal-window mean square, from one uniform bound on the dyadic mean squares.** -/
theorem sum_maxWindowSq_succ_le_uniform (f : ℕ → ℝ) {H J A B : ℕ} (hJ : H + 1 ≤ 2 ^ J)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ j, j ≤ J → ∀ i : ℕ,
      dyadicMeanSquare f (2 ^ j) (A + i * 2 ^ j) (B + i * 2 ^ j) ≤ C) :
    ∑ y ∈ Finset.Icc (A + 1) (B + 1), maxWindowSq f H y
      ≤ ((J : ℝ) + 1) * ((J : ℝ) + 1) * (2 ^ J : ℝ) * C := by
  classical
  refine le_trans (sum_maxWindowSq_succ_le_dyadic f hJ) ?_
  -- the level-zero translates
  have hzero : ∑ i ∈ Finset.range (2 ^ J), dyadicMeanSquare f 1 (A + i) (B + i)
      ≤ (2 ^ J : ℝ) * C := by
    have hterm : ∀ i ∈ Finset.range (2 ^ J), dyadicMeanSquare f 1 (A + i) (B + i) ≤ C := by
      intro i _
      have h := hC 0 (Nat.zero_le J) i
      simpa using h
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : ((2 ^ J : ℕ) : ℝ) = (2 : ℝ) ^ J := by push_cast; ring
    rw [this]
  -- the higher levels
  have hlevel : ∀ j ∈ Finset.range J,
      ∑ i ∈ Finset.range (2 ^ (J - j)),
          dyadicMeanSquare f (2 ^ j) (A + i * 2 ^ j) (B + i * 2 ^ j)
        ≤ (2 ^ J : ℝ) * C := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hterm : ∀ i ∈ Finset.range (2 ^ (J - j)),
        dyadicMeanSquare f (2 ^ j) (A + i * 2 ^ j) (B + i * 2 ^ j) ≤ C :=
      fun i _ => hC j (by omega) i
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hcast : ((2 ^ (J - j) : ℕ) : ℝ) = (2 : ℝ) ^ (J - j) := by push_cast; ring
    rw [hcast]
    have hpow : (2 : ℝ) ^ (J - j) ≤ (2 : ℝ) ^ J :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact mul_le_mul_of_nonneg_right hpow hC0
  have hsum : ∑ j ∈ Finset.range J, ∑ i ∈ Finset.range (2 ^ (J - j)),
        dyadicMeanSquare f (2 ^ j) (A + i * 2 ^ j) (B + i * 2 ^ j)
      ≤ (J : ℝ) * ((2 ^ J : ℝ) * C) := by
    refine le_trans (Finset.sum_le_sum hlevel) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
  have hpow0 : (0 : ℝ) ≤ (2 ^ J : ℝ) := by positivity
  nlinarith [hzero, hsum, hJ0, hpow0, hC0]

end RHTower.Sieve

end
