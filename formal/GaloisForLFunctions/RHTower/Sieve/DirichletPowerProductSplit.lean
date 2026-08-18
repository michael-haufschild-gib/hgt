import GaloisForLFunctions.RHTower.Sieve.DirichletProductSplit
import GaloisForLFunctions.RHTower.Sieve.DirichletSymmSplit
import GaloisForLFunctions.RHTower.Sieve.DirichletPowerMeasure

/-!
# The product split at a free exponent, with a prime-supported second factor

Cutting the frequency range at a threshold for the second factor and measuring the exceptional set
by the free-exponent large-values estimate gives, for every `k`,

`V^{2k}∫|F|²|G|² ≤ V^{2k+2}∫|F|² + (sup|F|)²(sup|G|)²·(T + 4M^k(1+log M^k))·k^k·(∑|b|²)^k .`

For a prime-supported second factor no power of its length enters the exceptional term, so the
exponent may be chosen against `log T / log M` — which is the mechanism the Matomäki--Radziwiłł
argument uses to make the exceptional frequencies cost nothing.
-/

namespace RHTower.Sieve

open MeasureTheory

/-- **The product split, with a free-exponent bound on the exceptional set.** -/
theorem integral_normSq_mul_le_of_pow (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ) (k : ℕ)
    {T V Bf Bg A : ℝ}
    (hBf : ∀ t : ℝ, ‖dirPoly N a t‖ ≤ Bf) (hBg : ∀ t : ℝ, ‖dirPoly M b t‖ ≤ Bg)
    (hA : V ^ (2 * k) * volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly M b t‖} ≤ A) :
    V ^ (2 * k) * (∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖ ^ 2 * ‖dirPoly M b t‖ ^ 2)
      ≤ V ^ (2 * k + 2) * (∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖ ^ 2)
        + Bf ^ 2 * Bg ^ 2 * A := by
  have hsplit := integral_normSq_mul_split N M a b hBf hBg (V := V) (T := T)
  have hVk : (0 : ℝ) ≤ V ^ (2 * k) := by
    rw [pow_mul]
    positivity
  have hK : (0 : ℝ) ≤ Bf ^ 2 * Bg ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsplit hVk
  have hexc := mul_le_mul_of_nonneg_left hA hK
  calc V ^ (2 * k)
        * (∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖ ^ 2 * ‖dirPoly M b t‖ ^ 2)
      ≤ V ^ (2 * k)
          * (V ^ 2 * (∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖ ^ 2)
            + Bf ^ 2 * Bg ^ 2
              * volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly M b t‖}) := hmul
    _ = V ^ (2 * k + 2) * (∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖ ^ 2)
          + Bf ^ 2 * Bg ^ 2
            * (V ^ (2 * k) * volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly M b t‖}) := by
        rw [pow_add]
        ring
    _ ≤ V ^ (2 * k + 2) * (∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖ ^ 2)
          + Bf ^ 2 * Bg ^ 2 * A := by linarith [hexc]

/-- **The product split, fully instantiated at a prime-supported second factor.**  The exceptional
term carries `k^k` and no power of the length. -/
theorem integral_normSq_mul_le_pow_prime_support (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ)
    (k : ℕ) (hk : 1 ≤ k)
    (hsupp : ∀ n : Fin M, b n ≠ 0 → Nat.Prime ((n : ℕ) + 1))
    {T V Bf Bg : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hBf : ∀ t : ℝ, ‖dirPoly N a t‖ ≤ Bf) (hBg : ∀ t : ℝ, ‖dirPoly M b t‖ ≤ Bg) :
    V ^ (2 * k) * (∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖ ^ 2 * ‖dirPoly M b t‖ ^ 2)
      ≤ V ^ (2 * k + 2) * (∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖ ^ 2)
        + Bf ^ 2 * Bg ^ 2
            * ((T + 4 * ((M ^ k : ℕ) : ℝ) * (1 + Real.log ((M ^ k : ℕ) : ℝ)))
                * ((k : ℝ) ^ k * (∑ n : Fin M, ‖b n‖ ^ 2) ^ k)) :=
  integral_normSq_mul_le_of_pow N M a b k hBf hBg
    (volume_largeValues_pow_le_of_prime_support k M hk b hsupp hT hV)

/-! ## The symmetric range -/

/-- **The symmetric product split at a free exponent, prime-supported second factor.** -/
theorem integral_normSq_mul_symm_le_pow_prime_support (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ)
    (k : ℕ) (hk : 1 ≤ k)
    (hsupp : ∀ n : Fin M, b n ≠ 0 → Nat.Prime ((n : ℕ) + 1))
    {T V Bf Bg : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hBf : ∀ t : ℝ, ‖dirPoly N a t‖ ≤ Bf) (hBg : ∀ t : ℝ, ‖dirPoly M b t‖ ≤ Bg) :
    V ^ (2 * k) * (∫ t in Set.Icc (-T) T, ‖dirPoly N a t‖ ^ 2 * ‖dirPoly M b t‖ ^ 2)
      ≤ V ^ (2 * k + 2) * (∫ t in Set.Icc (-T) T, ‖dirPoly N a t‖ ^ 2)
        + Bf ^ 2 * Bg ^ 2
            * (2 * ((T + 4 * ((M ^ k : ℕ) : ℝ) * (1 + Real.log ((M ^ k : ℕ) : ℝ)))
                * ((k : ℝ) ^ k * (∑ n : Fin M, ‖b n‖ ^ 2) ^ k))) := by
  have hsplit := integral_normSq_mul_split_symm N M a b hBf hBg (V := V) (T := T)
  have hVk : (0 : ℝ) ≤ V ^ (2 * k) := by
    rw [pow_mul]
    positivity
  have hK : (0 : ℝ) ≤ Bf ^ 2 * Bg ^ 2 := by positivity
  have hA := volume_largeValues_pow_symm_le_of_prime_support k M hk b hsupp hT hV
  have hmul := mul_le_mul_of_nonneg_left hsplit hVk
  have hexc := mul_le_mul_of_nonneg_left hA hK
  calc V ^ (2 * k)
        * (∫ t in Set.Icc (-T) T, ‖dirPoly N a t‖ ^ 2 * ‖dirPoly M b t‖ ^ 2)
      ≤ V ^ (2 * k)
          * (V ^ 2 * (∫ t in Set.Icc (-T) T, ‖dirPoly N a t‖ ^ 2)
            + Bf ^ 2 * Bg ^ 2
              * volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly M b t‖}) := hmul
    _ = V ^ (2 * k + 2) * (∫ t in Set.Icc (-T) T, ‖dirPoly N a t‖ ^ 2)
          + Bf ^ 2 * Bg ^ 2
            * (V ^ (2 * k) * volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly M b t‖}) := by
        rw [pow_add]
        ring
    _ ≤ V ^ (2 * k + 2) * (∫ t in Set.Icc (-T) T, ‖dirPoly N a t‖ ^ 2)
          + Bf ^ 2 * Bg ^ 2
            * (2 * ((T + 4 * ((M ^ k : ℕ) : ℝ) * (1 + Real.log ((M ^ k : ℕ) : ℝ)))
                * ((k : ℝ) ^ k * (∑ n : Fin M, ‖b n‖ ^ 2) ^ k))) := by linarith [hexc]

end RHTower.Sieve
