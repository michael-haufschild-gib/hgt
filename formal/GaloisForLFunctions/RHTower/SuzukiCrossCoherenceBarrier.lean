import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The cross-coherence barrier

The complementary Schur gain has an exact envelope: the canonical correlation bounds the linear
term by `√τ + ρ√ℓ` in the `D` metric and the quadratic term below by `(1-ρ²)`, so the variational
supremum is at most `(√τ + ρ√ℓ)²/(1-ρ²)`.  This is one completion of squares in the free scalar
`b = ⟨Dy,y⟩^{1/2}`.

The numerical barrier is sharp for exactly the information used: at `ρ² = 1/15` and `ℓ = 7/8` the
envelope equals `1/16`, so an order-one gain against a low-only leverage at most `7/8` forces the
squared coherence to `1/15` in the limit of vanishing high resolvent mass.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## `(420)`: the envelope -/

/-- **The scalar maximum behind the envelope.** -/
theorem quadratic_envelope {K m b : ℝ} (hm : 0 < m) : 2 * K * b - m * b ^ (2 : ℕ) ≤ K ^ (2 : ℕ) / m := by
  rw [le_div_iff₀ hm]
  nlinarith [sq_nonneg (m * b - K)]

/-- **`(424)`: the complementary Schur block inherits the coherence defect.** -/
theorem schur_coercive_of_coherence {Dy self ρ : ℝ}
    (hself : self ≤ ρ ^ (2 : ℕ) * Dy) : (1 - ρ ^ (2 : ℕ)) * Dy ≤ Dy - self := by
  linarith [hself]

/-! ## `(421)`–`(422)`: the sharp threshold -/

/-- **`(422)`: the constant is exact.** -/
theorem sharp_crossCoherence_constant :
    (1 / 15 : ℝ) * (7 / 8) / (1 - 1 / 15) = 1 / 16 := by
  norm_num

/-- **`(421)`: an order-one gain against a bounded low-only leverage forces the squared coherence
above `1/15`.** -/
theorem crossCoherence_sq_ge {ℓ ρ χ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 7 / 8)
    (hρ1 : ρ ^ (2 : ℕ) < 1) (hχ : 1 / 16 < χ)
    (henv : χ ≤ ρ ^ (2 : ℕ) * ℓ / (1 - ρ ^ (2 : ℕ))) : 1 / 15 ≤ ρ ^ (2 : ℕ) := by
  by_contra hcon
  rw [not_le] at hcon
  have hden : (0 : ℝ) < 1 - ρ ^ (2 : ℕ) := by linarith
  have hden' : (14 : ℝ) / 15 < 1 - ρ ^ (2 : ℕ) := by linarith
  have hnum : ρ ^ (2 : ℕ) * ℓ < 7 / 120 := by nlinarith [sq_nonneg ρ, hℓ0, hℓ, hcon]
  have hnum0 : (0 : ℝ) ≤ ρ ^ (2 : ℕ) * ℓ := by positivity
  have hquot : ρ ^ (2 : ℕ) * ℓ / (1 - ρ ^ (2 : ℕ)) < 1 / 16 := by
    rw [div_lt_iff₀ hden]
    nlinarith [hnum, hden', hden]
  linarith

/-- **`(420)`, in the vanishing high-resolvent limit.** -/
theorem envelope_limit {ℓ ρ χ : ℝ} (hℓ0 : 0 ≤ ℓ)
    (henv : χ ≤ (0 + ρ * Real.sqrt ℓ) ^ (2 : ℕ) / (1 - ρ ^ (2 : ℕ))) :
    χ ≤ ρ ^ (2 : ℕ) * ℓ / (1 - ρ ^ (2 : ℕ)) := by
  have hsq : (0 + ρ * Real.sqrt ℓ) ^ (2 : ℕ) = ρ ^ (2 : ℕ) * ℓ := by
    rw [zero_add, mul_pow, Real.sq_sqrt hℓ0]
  rwa [hsq] at henv

end GaloisForLFunctions.RHTower
