import GaloisForLFunctions.HTGeometry.InverseFamilyThirdDerivative
import GaloisForLFunctions.HTGeometry.PolynomialTransportRemainder

/-!
# The third amplitude on a frequency ray decays cubically

On the frequency ray the generator's derivatives fall by one power of the frequency each time, so the
natural scale of the amplitude tower is `w = 1/t`.  The corpus's general `O(w³)` bound for the
amplitude surviving three integrations by parts then reads exactly as the cubic decay `t^{-3}` that
the transported remainder integral consumes.
-/

open Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

omit [NormedAlgebra ℝ R] in
/-- **The third amplitude decays like `t^{-3}` on a frequency ray.** -/
theorem norm_invFamilyProduct2Deriv_le_rpow_neg_three {C C₁ C₂ C₃ : ℝ → R} {Λ c₁ c₂ c₃ : ℝ}
    {t : ℝ} (ht : 0 < t) (hΛ : ‖invFamily C t‖ ≤ Λ)
    (h₁ : ‖C₁ t‖ ≤ c₁ / t) (h₂ : ‖C₂ t‖ ≤ c₂ / t ^ 2) (h₃ : ‖C₃ t‖ ≤ c₃ / t ^ 3) :
    ‖invFamilyProduct2Deriv C C₁ C₂ C₃ t‖
      ≤ ((Λ ^ 2 * c₁) * (3 * Λ ^ 4 * c₁ ^ 2 + Λ ^ 3 * c₂)
          + Λ * (3 * (2 * Λ ^ 3 * c₁ ^ 2 + Λ ^ 2 * c₂) * (Λ ^ 2 * c₁)
            + Λ * (6 * Λ ^ 4 * c₁ ^ 3 + 6 * Λ ^ 3 * c₁ * c₂ + Λ ^ 2 * c₃)))
        * t ^ (-(3 : ℝ)) := by
  have hw : (0 : ℝ) < 1 / t := by positivity
  have e1 : c₁ / t = c₁ * (1 / t) := by ring
  have e2 : c₂ / t ^ 2 = c₂ * (1 / t) ^ 2 := by
    rw [div_pow, one_pow]
    ring
  have e3 : c₃ / t ^ 3 = c₃ * (1 / t) ^ 3 := by
    rw [div_pow, one_pow]
    ring
  have hbase := norm_invFamilyProduct2Deriv_le (C := C) (C₁ := C₁) (C₂ := C₂) (C₃ := C₃)
    (Λ := Λ) (c₁ := c₁) (c₂ := c₂) (c₃ := c₃) (w := 1 / t) (t := t) hw hΛ
    (by rw [← e1]; exact h₁) (by rw [← e2]; exact h₂) (by rw [← e3]; exact h₃)
  have hcube : (1 / t) ^ 3 = t ^ (-(3 : ℝ)) := by
    rw [Real.rpow_neg ht.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      div_pow, one_pow, one_div]
  rwa [hcube] at hbase

end GaloisForLFunctions.HTGeometry
