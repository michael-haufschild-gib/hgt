import GaloisForLFunctions.RHTower.SelbergClass.FiniteOrder

/-!
# Algebra of entire finite-order functions

The product of two entire functions satisfying the project's global finite-order condition again
satisfies that condition.  Outside the unit disk, witnesses multiply/add as
`(A₁ * A₂, B₁ + B₂, max ρ₁ ρ₂)`.
-/

open Metric Set

namespace RHTower

noncomputable section

/-- Products of entire finite-order functions satisfy an exponential-power bound outside the unit
disk, with the product/sum/max witnesses from the input bounds. -/
theorem EntireFiniteOrder.hasExponentialPowerGrowthOutside_mul
    (F G : EntireFiniteOrder) :
    HasExponentialPowerGrowthOutside (fun z : ℂ ↦ F z * G z) := by
  rcases F.growth with ⟨AF, BF, ρF, hAF, hBF, hρF, hF⟩
  rcases G.growth with ⟨AG, BG, ρG, hAG, hBG, hρG, hG⟩
  refine ⟨AF * AG, BF + BG, max ρF ρG, 1, mul_pos hAF hAG, add_pos hBF hBG,
    hρF.trans (le_max_left _ _), zero_le_one, ?_⟩
  intro z hz
  have hpowF : ‖z‖ ^ ρF ≤ ‖z‖ ^ max ρF ρG :=
    Real.rpow_le_rpow_of_exponent_le hz (le_max_left _ _)
  have hpowG : ‖z‖ ^ ρG ≤ ‖z‖ ^ max ρF ρG :=
    Real.rpow_le_rpow_of_exponent_le hz (le_max_right _ _)
  have htermF : BF * ‖z‖ ^ ρF ≤ BF * ‖z‖ ^ max ρF ρG :=
    mul_le_mul_of_nonneg_left hpowF hBF.le
  have htermG : BG * ‖z‖ ^ ρG ≤ BG * ‖z‖ ^ max ρF ρG :=
    mul_le_mul_of_nonneg_left hpowG hBG.le
  have hsum : BF * ‖z‖ ^ ρF + BG * ‖z‖ ^ ρG ≤
      (BF + BG) * ‖z‖ ^ max ρF ρG := by
    rw [add_mul]
    exact add_le_add htermF htermG
  have hexp : Real.exp (BF * ‖z‖ ^ ρF + BG * ‖z‖ ^ ρG) ≤
      Real.exp ((BF + BG) * ‖z‖ ^ max ρF ρG) :=
    (Real.exp_le_exp).mpr hsum
  calc
    ‖F z * G z‖ = ‖F z‖ * ‖G z‖ := norm_mul _ _
    _ ≤ (AF * Real.exp (BF * ‖z‖ ^ ρF)) * (AG * Real.exp (BG * ‖z‖ ^ ρG)) :=
      mul_le_mul (hF z) (hG z) (norm_nonneg _) (mul_nonneg hAF.le (Real.exp_pos _).le)
    _ = AF * AG * Real.exp (BF * ‖z‖ ^ ρF + BG * ‖z‖ ^ ρG) := by
      rw [Real.exp_add]
      ring
    _ ≤ AF * AG * Real.exp ((BF + BG) * ‖z‖ ^ max ρF ρG) :=
      mul_le_mul_of_nonneg_left hexp (mul_pos hAF hAG).le

/-- Pointwise multiplication preserves the project's entire finite-order carrier. -/
def EntireFiniteOrder.mul (F G : EntireFiniteOrder) : EntireFiniteOrder :=
  EntireFiniteOrder.ofOutside (fun z : ℂ ↦ F z * G z) (F.analytic.mul G.analytic)
    (F.hasExponentialPowerGrowthOutside_mul G)

@[simp]
theorem EntireFiniteOrder.mul_apply (F G : EntireFiniteOrder) (z : ℂ) :
    F.mul G z = F z * G z :=
  rfl

end

end RHTower
