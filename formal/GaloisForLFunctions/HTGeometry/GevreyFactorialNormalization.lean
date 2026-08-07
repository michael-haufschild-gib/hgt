import GaloisForLFunctions.HTGeometry.GevreyZetaTailBounds
import GaloisForLFunctions.HTGeometry.GammaFactorialNormalization

/-!
# The exact Gevrey order of the zeta tail, in the factorial normalization

The two-sided bounds for the tail coefficients

`|b k| = 2 |sin (π s k / 2)| Γ(1 + s k) Z k / (2π)^(1 + s k)`

were established against `Γ(1 + s k)`.  Since `Γ(1 + s k)` and `(k!)^s` differ by a factor of the
geometric form `C A^k`, the same bounds hold against `(k!)^s`:

`c a^k (k!)^s ≤ |b k|` for infinitely many `k`,  and  `|b k| ≤ C A^k (k!)^s` for all `k`.

So the exact Gevrey order is `s` in either normalization.
-/

namespace GaloisForLFunctions.HTGeometry

open Real

/-- **The exact Gevrey order of an irrational-power zeta tail, in the factorial normalization.** -/
theorem gevrey_exact_order_factorial {s M : ℝ} (hs0 : 0 < s) (hirr : Irrational s)
    {b Z : ℕ → ℝ} (hZ : ∀ k, 1 ≤ Z k) (hM : ∀ k, Z k ≤ M)
    (hb : ∀ k : ℕ, |b k| = 2 * |Real.sin (Real.pi * s * k / 2)| * Real.Gamma (1 + s * k) * Z k
      / (2 * Real.pi) ^ (1 + s * (k : ℝ)))
    (hGamma : ∀ k : ℕ, 0 < Real.Gamma (1 + s * k)) :
    (∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ k : ℕ, |b k| ≤ C * A ^ k * (k.factorial : ℝ) ^ s) ∧
      (∃ c a : ℝ, 0 < c ∧ 0 < a ∧
        {k : ℕ | c * a ^ k * (k.factorial : ℝ) ^ s ≤ |b k|}.Infinite) := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hB : (0 : ℝ) < (((2 * Real.pi) ^ s)⁻¹) := by
    have : (0 : ℝ) < (2 * Real.pi) ^ s := Real.rpow_pos_of_pos h2pi s
    positivity
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one ((hZ 0).trans (hM 0))
  constructor
  · obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℕ, s < M₀ := ⟨⌈s⌉₊ + 1, by push_cast; linarith [Nat.le_ceil s]⟩
    set A₀ : ℝ := ((1 : ℝ) + M₀ + s) ^ s with hA₀
    have hA₀pos : 0 < A₀ := Real.rpow_pos_of_pos (by positivity) s
    refine ⟨M / Real.pi, (((2 * Real.pi) ^ s)⁻¹) * A₀,
      div_pos hMpos Real.pi_pos, mul_pos hB hA₀pos, fun k => ?_⟩
    have hup := gevrey_upper_bound hZ hM hb hGamma k
    have hgam : Real.Gamma (1 + s * k) ≤ A₀ ^ k * (k.factorial : ℝ) ^ s :=
      Gamma_le_pow_mul_factorial_rpow hs0 M₀ hM₀ k
    calc |b k| ≤ (M / Real.pi) * ((((2 * Real.pi) ^ s)⁻¹) ^ k) * Real.Gamma (1 + s * k) := hup
      _ ≤ (M / Real.pi) * ((((2 * Real.pi) ^ s)⁻¹) ^ k) * (A₀ ^ k * (k.factorial : ℝ) ^ s) := by
          refine mul_le_mul_of_nonneg_left hgam ?_
          positivity
      _ = (M / Real.pi) * (((((2 * Real.pi) ^ s)⁻¹) * A₀) ^ k) * (k.factorial : ℝ) ^ s := by
          rw [mul_pow]; ring
  · obtain ⟨c₀, a₀, hc₀, ha₀, hlow⟩ := exists_pow_mul_factorial_rpow_le_Gamma hs0
    refine ⟨c₀ / (2 * Real.pi), (((2 * Real.pi) ^ s)⁻¹) * a₀,
      div_pos hc₀ h2pi, mul_pos hB ha₀, ?_⟩
    refine (infinite_setOf_half_le_abs_sin_half hirr).mono ?_
    intro k hk
    have hgl := gevrey_lower_bound hZ hb hGamma hk
    have hgam : c₀ * (a₀ ^ k * (k.factorial : ℝ) ^ s) ≤ Real.Gamma (1 + s * k) := hlow k
    have hstep : (1 / (2 * Real.pi)) * ((((2 * Real.pi) ^ s)⁻¹) ^ k)
          * (c₀ * (a₀ ^ k * (k.factorial : ℝ) ^ s))
        ≤ (1 / (2 * Real.pi)) * ((((2 * Real.pi) ^ s)⁻¹) ^ k) * Real.Gamma (1 + s * k) := by
      refine mul_le_mul_of_nonneg_left hgam ?_
      positivity
    have heq : (c₀ / (2 * Real.pi)) * (((((2 * Real.pi) ^ s)⁻¹) * a₀) ^ k)
          * (k.factorial : ℝ) ^ s
        = (1 / (2 * Real.pi)) * ((((2 * Real.pi) ^ s)⁻¹) ^ k)
          * (c₀ * (a₀ ^ k * (k.factorial : ℝ) ^ s)) := by
      rw [mul_pow]; ring
    show (c₀ / (2 * Real.pi)) * (((((2 * Real.pi) ^ s)⁻¹) * a₀) ^ k) * (k.factorial : ℝ) ^ s ≤ |b k|
    rw [heq]
    exact hstep.trans hgl

end GaloisForLFunctions.HTGeometry
