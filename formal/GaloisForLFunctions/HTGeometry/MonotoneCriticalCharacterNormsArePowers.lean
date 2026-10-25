import GaloisForLFunctions.HTGeometry.MonotoneMultiplicativeProfilesArePowers
import Mathlib.Analysis.Complex.Basic

/-!
# Monotone critical character norms are powers

An antitone critical squared-modulus profile forces a multiplicative
complex character to have augmentation modulus or one real power law.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry

/-- The critical squared-modulus profile of a multiplicative complex character. -/
def criticalNormProfile (χ : ℕ+ →* ℂ) : ℕ+ →* ℝ where
  toFun p := (p : ℝ) * ‖χ p‖ ^ 2
  map_one' := by norm_num
  map_mul' p q := by
    simp only [map_mul, norm_mul, mul_pow, PNat.mul_coe, Nat.cast_mul]
    ring

/-- Numeric monotonicity fixes the magnitudes of a complex multiplicative character. -/
theorem character_norm_eq_augmentation_or_rpow (χ : ℕ+ →* ℂ)
    (hanti : Antitone (criticalNormProfile χ)) :
    (∀ p : ℕ+, p ≠ 1 → χ p = 0) ∨
      ∃ s : ℝ, 1 / 2 ≤ s ∧ ∀ p : ℕ+, ‖χ p‖ = (p : ℝ) ^ (-s) := by
  have hr0 (p : ℕ+) : 0 ≤ criticalNormProfile χ p := by
    change 0 ≤ (p : ℝ) * ‖χ p‖ ^ 2
    positivity
  rcases antitone_nonnegative_monoidHom_eq_augmentation_or_rpow
    (criticalNormProfile χ) hr0 hanti with hzero | ⟨α, hα, hpower⟩
  · refine Or.inl fun p hp => norm_eq_zero.mp ?_
    have h := hzero p hp
    change (p : ℝ) * ‖χ p‖ ^ 2 = 0 at h
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp h).resolve_left (by positivity))
  · refine Or.inr ⟨(α + 1) / 2, by linarith only [hα], fun p => ?_⟩
    have hp : (0 : ℝ) < p := by exact_mod_cast p.property
    have hsq : ‖χ p‖ ^ 2 = (p : ℝ) ^ (-(α + 1)) := by
      have h := hpower p
      change (p : ℝ) * ‖χ p‖ ^ 2 = (p : ℝ) ^ (-α) at h
      apply mul_left_cancel₀ hp.ne'
      rw [h]
      calc
        (p : ℝ) ^ (-α) = (p : ℝ) ^ ((1 : ℝ) + (-(α + 1))) := by congr 1; ring
        _ = (p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ (-(α + 1)) := Real.rpow_add hp _ _
        _ = _ := by rw [Real.rpow_one]
    apply (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hp.le _) two_ne_zero).mp
    rw [hsq, ← Real.rpow_natCast, ← Real.rpow_mul hp.le]
    congr 1
    ring

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.character_norm_eq_augmentation_or_rpow
end
