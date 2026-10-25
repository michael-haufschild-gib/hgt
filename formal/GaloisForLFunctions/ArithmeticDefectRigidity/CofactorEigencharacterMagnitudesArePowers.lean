import GaloisForLFunctions.HTGeometry.MonotoneCriticalCharacterNormsArePowers
import GaloisForLFunctions.ArithmeticDefectRigidity.NumericHorizonOrderControlsTheCofactorAction

/-!
# Actual cofactor eigencharacter magnitudes are powers

Numeric horizon order restricts every common eigenvector's character to
augmentation or a power modulus with exponent at least one half.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit
open GaloisForLFunctions.HTGeometry

/-- Every actual common eigencharacter has augmentation or one Archimedean modulus. -/
theorem eigencharacter_norm_eq_augmentation_or_rpow {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (χ : ℕ+ →* ℂ) {x : Hilbert L} (hx : x ≠ 0)
    (heig : ∀ p : ℕ+, dilation L p x = χ p • x) :
    (∀ p : ℕ+, p ≠ 1 → χ p = 0) ∨
      ∃ s : ℝ, 1 / 2 ≤ s ∧ ∀ p : ℕ+, ‖χ p‖ = (p : ℝ) ^ (-s) := by
  apply character_norm_eq_augmentation_or_rpow χ
  intro p q hpq
  have h := scaled_dilation_norm_sq_antitone L x hpq
  change (q : ℝ) * ‖dilation L q x‖ ^ 2 ≤ (p : ℝ) * ‖dilation L p x‖ ^ 2 at h
  simp only [heig, norm_smul, mul_pow, ← mul_assoc] at h
  change (q : ℝ) * ‖χ q‖ ^ 2 ≤ (p : ℝ) * ‖χ p‖ ^ 2
  exact le_of_mul_le_mul_right h (sq_pos_of_pos (norm_pos_iff.mpr hx))

end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.eigencharacter_norm_eq_augmentation_or_rpow
end
