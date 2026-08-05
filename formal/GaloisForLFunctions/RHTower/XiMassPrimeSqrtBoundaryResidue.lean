import GaloisForLFunctions.RHTower.XiMassPrimeSqrtDilation

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

theorem exists_norm_xiMassPrimeSqrtMaskLayer_vertical_bound
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) :
    ∃ B : ℝ, ∀ u : ℝ,
      ‖xiMassPrimeSqrtMaskLayer a ((σ : ℂ) + u * I)‖ ≤ B := by
  have ha2 : 0 < a / 2 := by linarith
  have hσ2 : 0 < 2 * σ := by linarith
  obtain ⟨B, hB⟩ :=
    exists_norm_xiMassPrimeSquareLayer_vertical_bound
      (a := a / 2) (σ := 2 * σ) ha2 hσ2
  refine ⟨2 * B, fun u => ?_⟩
  have harg : 2 * ((σ : ℂ) + u * I) =
      ((2 * σ : ℝ) : ℂ) + ((2 * u : ℝ) : ℂ) * I := by
    push_cast
    ring
  calc
    ‖xiMassPrimeSqrtMaskLayer a ((σ : ℂ) + u * I)‖ =
        2 * ‖xiMassPrimeSquareLayer (a / 2)
          (2 * ((σ : ℂ) + u * I))‖ :=
      norm_xiMassPrimeSqrtMaskLayer_eq_two_mul_primeSquareLayer
        ha ((σ : ℂ) + u * I)
    _ = 2 * ‖xiMassPrimeSquareLayer (a / 2)
          (((2 * σ : ℝ) : ℂ) + ((2 * u : ℝ) : ℂ) * I)‖ := by rw [harg]
    _ ≤ 2 * B := mul_le_mul_of_nonneg_left (hB (2 * u)) (by norm_num)

end

end RHTower
