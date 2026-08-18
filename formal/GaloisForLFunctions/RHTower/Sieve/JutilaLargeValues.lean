import GaloisForLFunctions.RHTower.Sieve.PowerFibreDivisorBound
import GaloisForLFunctions.RHTower.Sieve.DirichletLargeValuesL1

/-!
# The two endpoints of Jutila's large-values estimate

Matomäki–Teräväinen's Lemma 4.1 rests on Jutila's estimate, which interpolates between two
large-value counts for a Dirichlet polynomial of length `N` with divisor-bounded coefficients:

* the **Montgomery endpoint** `k = 1`, already in the corpus as
  `Sieve/DirichletLargeValuesL1.card_largeValues_div_le`;
* the **moment endpoint** at an arbitrary power `k`, obtained by applying the same count to the
  `k`-fold convolution `convPow N k a`, whose length is `N^k` and whose coefficient energy is
  controlled by `Sieve/PowerFibreDivisorBound` — the fibre being the ordered `k`-factorisation set,
  paid by the divisor bound.

Both endpoints are recorded here in a single statement with `k` free, so that the interpolation can
choose `k`.  Neither endpoint alone reaches `σ > 1/5` in the range `N ≥ T^{2/3}` (Montgomery needs
`σ ≥ 1/2`, the pure moment needs `k = 1`); the interpolation is what the fourth moment of `ζ`
supplies through `Sieve/CriticalTruncationZeta`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The moment endpoint.**  The large-value count at the `k`-th power, for divisor-bounded
coefficients on an unrestricted support. -/
theorem card_largeValues_pow_div_le_divisorBounded {ε : ℝ} (hε : 0 < ε) (N k : ℕ)
    (hNk : 2 ≤ N ^ k) (a : Fin N → ℂ) {lam : ℕ → ℝ} {δ T V : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T) (hV : 0 < V)
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hlow : δ / 2 ≤ lam 0) (R : ℕ)
    (hhigh : lam R + δ / 2 ≤ T)
    (hbig : ∀ r ∈ Finset.range (R + 1), V ≤ ‖dirPoly N a (lam r)‖) :
    (R : ℝ) + 1
      ≤ (T + 4 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log ((N ^ k : ℕ) : ℝ)))
            * (1 / δ + 2 * Real.log ((N ^ k : ℕ) : ℝ))
            * ((divisorBoundConst ε * (((N ^ k : ℕ) : ℝ)) ^ ε) ^ k
                * (∑ m : Fin N, ‖a m‖ ^ 2) ^ k)
          / V ^ (2 * k) := by
  classical
  have hVk : (0 : ℝ) < V ^ k := by positivity
  have hbigk : ∀ r ∈ Finset.range (R + 1),
      V ^ k ≤ ‖dirPoly (N ^ k) (convPow N k a) (lam r)‖ := by
    intro r hr
    rw [dirPoly_convPow, norm_pow]
    exact pow_le_pow_left₀ hV.le (hbig r hr) k
  have hcount := card_largeValues_div_le (N ^ k) hNk (convPow N k a) hδ hT hVk hgap hlow R
    hhigh hbigk
  have hVpow : (V ^ k) ^ 2 = V ^ (2 * k) := by
    rw [← pow_mul, mul_comm]
  rw [hVpow] at hcount
  have hV2 : (0 : ℝ) < V ^ (2 * k) := by positivity
  have hlogNk : (0 : ℝ) ≤ Real.log ((N ^ k : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (N ^ k) with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hcast : (0 : ℝ) ≤ ((N ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfac : (0 : ℝ) ≤ (T + 4 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log ((N ^ k : ℕ) : ℝ)))
      * (1 / δ + 2 * Real.log ((N ^ k : ℕ) : ℝ)) := by
    have h1 : (0 : ℝ) ≤ T + 4 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log ((N ^ k : ℕ) : ℝ)) := by
      nlinarith
    have h2 : (0 : ℝ) ≤ 1 / δ + 2 * Real.log ((N ^ k : ℕ) : ℝ) := by positivity
    exact mul_nonneg h1 h2
  have hstep := mul_le_mul_of_nonneg_left
    (sum_normSq_convPow_le_divisorBounded hε N k a) hfac
  refine le_trans hcount ?_
  exact div_le_div_of_nonneg_right hstep hV2.le

end

end RHTower.Sieve
