import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalSquareRoot

/-!
# A closed-data coordinate across the physical coexistence interval

The sine coordinate ranges between the two actual phase radii, with zero
at their arithmetic mean. Its critical displacement is linear and its
squared-radius displacement has an explicit limit. This lets one compare
stable phases and the intervening region using one exact construction.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAInteriorRadius (w φ τ ψ : ℝ) : ℝ :=
  egbFixedChargeAMeanRadius w φ τ * (1 + egbCoexistenceASymmetricRatio τ * sin ψ)

theorem egbFixedChargeAInteriorRadius_bounds (w φ τ ψ : ℝ) :
    egbFixedChargeASmallRadius w φ τ ≤ egbFixedChargeAInteriorRadius w φ τ ψ ∧
      egbFixedChargeAInteriorRadius w φ τ ψ ≤ egbFixedChargeALargeRadius w φ τ := by
  have hm := egbFixedChargeAMeanRadius_pos w φ τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hprod : 0 < egbFixedChargeAMeanRadius w φ τ * egbCoexistenceASymmetricRatio τ := mul_pos hm hd
  have hlo := mul_le_mul_of_nonneg_left (neg_one_le_sin ψ) hprod.le
  have hhi := mul_le_mul_of_nonneg_left (sin_le_one ψ) hprod.le
  rw [egbFixedChargeA_small_radius_mean, egbFixedChargeA_large_radius_mean]
  unfold egbFixedChargeAInteriorRadius
  constructor <;> nlinarith only [hlo, hhi]

theorem egbFixedChargeAInteriorRadius_pos (w φ τ ψ : ℝ) : 0 < egbFixedChargeAInteriorRadius w φ τ ψ :=
  lt_of_lt_of_le (egbFixedChargeA_radii_order w φ τ).1 (egbFixedChargeAInteriorRadius_bounds w φ τ ψ).1

theorem egbFixedChargeAInteriorRadius_large (w φ τ : ℝ) :
    egbFixedChargeAInteriorRadius w φ τ (Real.pi / 2) = egbFixedChargeALargeRadius w φ τ := by
  unfold egbFixedChargeAInteriorRadius
  rw [sin_pi_div_two, mul_one, egbFixedChargeA_large_radius_mean]
  ring

theorem egbFixedChargeAInteriorRadius_small (w φ τ : ℝ) :
    egbFixedChargeAInteriorRadius w φ τ (-Real.pi / 2) = egbFixedChargeASmallRadius w φ τ := by
  unfold egbFixedChargeAInteriorRadius
  have hs : sin (-Real.pi / 2) = -1 := by rw [neg_div, sin_neg, sin_pi_div_two]
  rw [hs, egbFixedChargeA_small_radius_mean]
  ring

theorem egbFixedChargeAInteriorRadius_mean (w φ τ : ℝ) :
    egbFixedChargeAInteriorRadius w φ τ 0 = egbFixedChargeAMeanRadius w φ τ := by
  simp only [egbFixedChargeAInteriorRadius, sin_zero, mul_zero, add_zero, mul_one]

theorem egbFixedChargeAInteriorRadius_critical_limit (w φ ψ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAInteriorRadius w φ τ ψ) atBot (𝓝 (egbFixedChargeACriticalRadius w φ)) := by
  have h := (egbFixedChargeAMeanRadius_critical_limit w φ).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).add (egbCoexistenceASymmetricRatio_critical_limit.mul (tendsto_const_nhds (x := sin ψ))))
  simpa only [egbFixedChargeAInteriorRadius, zero_mul, add_zero, mul_one] using h

theorem egbFixedChargeAInteriorRadius_normalized_difference (w φ τ ψ : ℝ) :
    (egbFixedChargeAInteriorRadius w φ τ ψ - egbFixedChargeACriticalRadius w φ) / egbCoexistenceASymmetricRatio τ =
      (egbFixedChargeAMeanRadius w φ τ - egbFixedChargeACriticalRadius w φ) / egbCoexistenceASymmetricRatio τ +
        egbFixedChargeAMeanRadius w φ τ * sin ψ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAInteriorRadius
  field_simp <;> ring

theorem egbFixedChargeAInteriorRadius_linear_critical_limit (w φ ψ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAInteriorRadius w φ τ ψ - egbFixedChargeACriticalRadius w φ) / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (egbFixedChargeACriticalRadius w φ * sin ψ)) := by
  simp only [egbFixedChargeAInteriorRadius_normalized_difference]
  simpa only [zero_add] using (egbFixedChargeAMeanRadius_linear_critical_limit w φ).add
    ((egbFixedChargeAMeanRadius_critical_limit w φ).mul (tendsto_const_nhds (x := sin ψ)))

theorem egbFixedChargeAInteriorRadius_square_gap_critical_limit (w φ ψ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAInteriorRadius w φ τ ψ ^ (2 : ℕ) - egbFixedChargeACriticalRadius w φ ^ (2 : ℕ)) / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (2 * egbFixedChargeACriticalRadius w φ ^ (2 : ℕ) * sin ψ)) := by
  have h := (egbFixedChargeAInteriorRadius_linear_critical_limit w φ ψ).mul
    ((egbFixedChargeAInteriorRadius_critical_limit w φ ψ).add (tendsto_const_nhds (x := egbFixedChargeACriticalRadius w φ)))
  convert h using 1
  · funext τ
    ring
  · ring

end GaloisForLFunctions.HTGeometry
