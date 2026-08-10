import GaloisForLFunctions.RHTower.Sieve.PerronVerticalTripleBound
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowBrunTitchmarsh

/-!
# The vertical triple bound with the Brun–Titchmarsh mean squares

`integral_symm_norm_perron_triple_affine_le` consumes the two prime factors' mean squares as affine
data `Q + κ·U`, so any improvement of the mean square substitutes with no further work.  Feeding it
the Brun–Titchmarsh mean square instead of the Selberg one replaces the height-independent constant

```text
10πe·(∑_q q‖a_q q^{-σ}‖²)/log Y      (Selberg, level capped at log Y = O(1))
```

by

```text
10πe·(∑_q q‖a_q q^{-σ}‖²)/log z      (Brun–Titchmarsh, level free)
```

at the cost of a height-linear term `6z(1 + log z)³` in place of `selbergFibreError z Y + z`.  Since
the Brun–Titchmarsh error carries no fibre factor, the level may be taken as a power of the window
length; the Selberg one cannot.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- **The vertical triple bound at prime-supported outer factors, with the Brun–Titchmarsh mean
squares.** -/
theorem integral_symm_norm_perron_triple_bt_le {A B f : ℕ → ℂ} {sA sB : Finset ℕ}
    (hsA : ∀ m ∈ sA, m.Prime) (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ sA)
    (hsB : ∀ m ∈ sB, m.Prime) (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ sB)
    {σ x t₀ V zA zB : ℝ} (hσ : 0 < σ) (hx : 0 < x) (ht₀ : 1 ≤ t₀) (hV : 0 ≤ V)
    (hzA : 1 < zA) (hzB : 1 < zB)
    (hFc : Continuous fun t : ℝ => LSeries f ((σ : ℂ) + (t : ℝ) * I))
    (M : ℕ)
    (hFbound : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ M → ‖LSeries f ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V) :
    (∫ t in (-(t₀ * 2 ^ M))..(t₀ * 2 ^ M),
        ‖LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries f ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖)
      ≤ 2 * perronVerticalAffineProductBound σ x t₀ V
            (btMeanSquareConst A sA σ zA) (btMeanSquareRate A sA σ zA)
            (btMeanSquareConst B sB σ zB) (btMeanSquareRate B sB σ zB) M
        + (V * x ^ σ / σ)
            * (Real.sqrt (btMeanSquareConst A sA σ zA + btMeanSquareRate A sA σ zA * t₀)
              * Real.sqrt (btMeanSquareConst B sB σ zB + btMeanSquareRate B sB σ zB * t₀)) := by
  have hA0 : (0 : ℕ) ∉ sA := fun h => Nat.not_prime_zero (hsA 0 h)
  have hB0 : (0 : ℕ) ∉ sB := fun h => Nat.not_prime_zero (hsB 0 h)
  exact integral_symm_norm_perron_triple_affine_le hA0 hAsupp hB0 hBsupp hσ hx ht₀ hV
    (btMeanSquareConst_nonneg A sA σ hzA) (btMeanSquareRate_nonneg A sA σ hzA)
    (btMeanSquareConst_nonneg B sB σ hzB) (btMeanSquareRate_nonneg B sB σ hzB)
    hFc
    (fun U hU => integral_Icc_normSq_LSeries_le_prime_bt_affine hsA hA0 hAsupp σ hU hzA)
    (fun U hU => integral_Icc_normSq_LSeries_le_prime_bt_affine hsB hB0 hBsupp σ hU hzB)
    M hFbound

end RHTower.Sieve

end
