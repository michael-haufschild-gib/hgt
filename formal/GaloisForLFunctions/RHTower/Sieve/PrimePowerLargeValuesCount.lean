import GaloisForLFunctions.RHTower.Sieve.PrimePowerSupport
import GaloisForLFunctions.RHTower.Sieve.DirichletLargeValuesCount

/-!
# Counting the large values of a prime polynomial by an adapted moment

Applying the discrete large-values cap to the `ℓ`-th power of a prime-supported Dirichlet
polynomial counts its well-spaced large values with the `2ℓ`-th moment:

    (R + 1)·V^{2ℓ} ≤ (T + 4N^ℓ(1+log N^ℓ))·(δ⁻¹ + 2 log N^ℓ)·ℓ^ℓ·(∑_p ‖b_p‖²)^ℓ.

For a short prime range this is the adapted count: choosing `ℓ` so that `N^ℓ` matches `T` makes
the range factor proportional to `T`, and the entire length dependence collapses into
`ℓ^ℓ·(∑‖b_p‖²)^ℓ` — exponentially small in `ℓ` whenever the threshold `V` exceeds the mass
`∑‖b_p‖²`-scale, which is what bounds the well-spaced exceptional set of the bilinear method.
-/

namespace RHTower.Sieve

open Finset

/-- **The adapted-moment cap on well-spaced large values of a prime-supported polynomial.** -/
theorem card_largeValues_pow_le (N ℓ : ℕ) (hℓ : ℓ ≠ 0) (hN : 2 ≤ N) (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 → Nat.Prime ((n : ℕ) + 1))
    {lam : ℕ → ℝ} {δ T V : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T) (hV : 0 < V)
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hlow : δ / 2 ≤ lam 0) (R : ℕ)
    (hhigh : lam R + δ / 2 ≤ T)
    (hbig : ∀ r ∈ Finset.range (R + 1), V ≤ ‖dirPoly N a (lam r)‖) :
    ((R : ℝ) + 1) * V ^ (2 * ℓ)
      ≤ (T + 4 * ((N ^ ℓ : ℕ) : ℝ) * (1 + Real.log ((N ^ ℓ : ℕ) : ℝ)))
          * (1 / δ + 2 * Real.log ((N ^ ℓ : ℕ) : ℝ))
          * ((ℓ : ℝ) ^ ℓ * (∑ n : Fin N, ‖a n‖ ^ 2) ^ ℓ) := by
  have hNl : 2 ≤ N ^ ℓ := le_trans hN (Nat.le_self_pow hℓ N)
  have hVl : (0 : ℝ) < V ^ ℓ := by positivity
  have hbigl : ∀ r ∈ Finset.range (R + 1),
      V ^ ℓ ≤ ‖dirPoly (N ^ ℓ) (convPow N ℓ a) (lam r)‖ := by
    intro r hr
    rw [dirPoly_convPow, norm_pow]
    exact pow_le_pow_left₀ hV.le (hbig r hr) ℓ
  have hbase := card_largeValues_le (N ^ ℓ) hNl (convPow N ℓ a) hδ hT hVl
    hgap hlow R hhigh hbigl
  have hpow : (V ^ ℓ) ^ 2 = V ^ (2 * ℓ) := by
    rw [← pow_mul, mul_comm]
  rw [hpow] at hbase
  have hlogNl : (0 : ℝ) ≤ Real.log ((N ^ ℓ : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) ≤ ((N ^ ℓ : ℕ) : ℝ) := by
      exact_mod_cast le_trans (by norm_num) hNl
    exact Real.log_nonneg h1
  have hcast : (0 : ℝ) ≤ ((N ^ ℓ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA : (0 : ℝ)
      ≤ T + 4 * ((N ^ ℓ : ℕ) : ℝ) * (1 + Real.log ((N ^ ℓ : ℕ) : ℝ)) := by nlinarith
  have hB : (0 : ℝ) ≤ 1 / δ + 2 * Real.log ((N ^ ℓ : ℕ) : ℝ) := by positivity
  have hmass := sum_normSq_convPow_le_of_prime_support N ℓ a hsupp
  have hstep := mul_le_mul_of_nonneg_left hmass (mul_nonneg hA hB)
  calc ((R : ℝ) + 1) * V ^ (2 * ℓ)
      ≤ (T + 4 * ((N ^ ℓ : ℕ) : ℝ) * (1 + Real.log ((N ^ ℓ : ℕ) : ℝ)))
          * (1 / δ + 2 * Real.log ((N ^ ℓ : ℕ) : ℝ))
          * ∑ j : Fin (N ^ ℓ), ‖convPow N ℓ a j‖ ^ 2 := hbase
    _ ≤ (T + 4 * ((N ^ ℓ : ℕ) : ℝ) * (1 + Real.log ((N ^ ℓ : ℕ) : ℝ)))
          * (1 / δ + 2 * Real.log ((N ^ ℓ : ℕ) : ℝ))
          * ((ℓ : ℝ) ^ ℓ * (∑ n : Fin N, ‖a n‖ ^ 2) ^ ℓ) := by
        rw [mul_assoc, mul_assoc] at hstep ⊢
        exact hstep

end RHTower.Sieve
