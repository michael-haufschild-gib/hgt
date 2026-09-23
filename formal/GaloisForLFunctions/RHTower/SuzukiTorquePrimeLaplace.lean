import GaloisForLFunctions.RHTower.SuzukiTorquePrimeSeries

/-!
# The prime layer's Laplace transform

The visible prime layer is a series of nonnegative tents, each with an explicit transform, and the
series of transforms converges to the right of `3/2`.  So the transform of the sum is the sum of the
transforms — no principal-value or Abel summation is needed, only absolute convergence.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- **The prime layer's Laplace transform is the tent series.** -/
theorem integral_suzukiFreePrimePositionTorque_mul_exp {σ : ℝ} (hσ : 3 / 2 < σ) :
    (∫ L in Ioi (0 : ℝ), suzukiFreePrimePositionTorque L * Real.exp (-σ * L))
      = (∑' n : ℕ, suzukiTentCoeff n * Real.exp (-σ * Real.log n)) / σ ^ (2 : ℕ) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hint : ∀ n : ℕ, Integrable (fun L : ℝ => suzukiTentTerm n L * Real.exp (-σ * L))
      (volume.restrict (Ioi (0 : ℝ))) := fun n => integrableOn_suzukiTentTerm_mul_exp n hσ0
  have hnorm : ∀ n : ℕ,
      (∫ L in Ioi (0 : ℝ), ‖suzukiTentTerm n L * Real.exp (-σ * L)‖)
        = suzukiTentCoeff n * (Real.exp (-σ * Real.log n) / σ ^ (2 : ℕ)) := by
    intro n
    have hcongr : (∫ L in Ioi (0 : ℝ), ‖suzukiTentTerm n L * Real.exp (-σ * L)‖)
        = ∫ L in Ioi (0 : ℝ), suzukiTentTerm n L * Real.exp (-σ * L) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (suzukiTentTerm_nonneg n L) (Real.exp_pos _).le)]
    rw [hcongr, integral_suzukiTentTerm_mul_exp n hσ0]
  have hsummable : Summable fun n : ℕ =>
      ∫ L in Ioi (0 : ℝ), ‖suzukiTentTerm n L * Real.exp (-σ * L)‖ := by
    refine ((summable_suzukiTentCoeff_mul_exp hσ).div_const (σ ^ (2 : ℕ))).congr fun n => ?_
    rw [hnorm n]
    ring
  have hswap := integral_tsum_of_summable_integral_norm hint hsummable
  have hleft : (∑' n : ℕ, ∫ L in Ioi (0 : ℝ), suzukiTentTerm n L * Real.exp (-σ * L))
      = (∑' n : ℕ, suzukiTentCoeff n * Real.exp (-σ * Real.log n)) / σ ^ (2 : ℕ) := by
    rw [← tsum_div_const]
    refine tsum_congr fun n => ?_
    rw [integral_suzukiTentTerm_mul_exp n hσ0]
    ring
  have hright : (∫ L in Ioi (0 : ℝ), ∑' n : ℕ, suzukiTentTerm n L * Real.exp (-σ * L))
      = ∫ L in Ioi (0 : ℝ), suzukiFreePrimePositionTorque L * Real.exp (-σ * L) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
    rw [tsum_mul_right, ← suzukiFreePrimePositionTorque_eq_tsum]
  rw [← hright, ← hswap, hleft]

end RHTower
