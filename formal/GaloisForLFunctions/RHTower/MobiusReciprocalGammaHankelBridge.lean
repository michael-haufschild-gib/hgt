import GaloisForLFunctions.RHTower.MobiusReciprocalOrderTransfer
import GaloisForLFunctions.RHTower.MobiusLaplaceGammaHankelWall

/-!
# Direct reciprocal-to-Laplace finite energy bridge

At reciprocal order `1 + δ`, the stationary finite moment is exactly the
original Möbius Gamma--Hankel quadratic form, apart from its positive Gamma
factor. The two-step order comparison therefore sends a source estimate at
order `3 + δ` directly to the already formalized Fatou/RH endpoint.
-/

open Finset Filter
namespace RHTower
noncomputable section

private theorem sum_Icc_one_eq_shifted_range (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, f n) = ∑ n ∈ Finset.range N, f (n + 1) := by
  symm
  apply Finset.sum_bij (fun n _ => n + 1)
  · intro n hn
    simp only [Finset.mem_range] at hn
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro a ha b hb he
    omega
  · intro b hb
    have hb := Finset.mem_Icc.mp hb
    exact ⟨b - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro n hn
    rfl

private theorem generalReciprocalMomentKernel_base (δ : ℝ) (m n : ℕ) :
    generalReciprocalMomentKernel (1 + δ) δ m n =
      1 / (((m + n : ℕ) : ℝ) ^ (1 + δ)) := by
  unfold generalReciprocalMomentKernel
  have hzero : 1 + δ - 1 - δ = 0 := by ring
  have hshape : 2 * (1 + δ) - 1 - δ = 1 + δ := by ring
  rw [hzero, hshape, Real.rpow_zero, one_div]
  push_cast
  ring

/-- Exact finite identification, including the Gamma normalization and natural-section indexing. -/
theorem finiteMobiusGammaHankelEnergy_eq_gamma_mul_generalReciprocalEnergy
    (δ : ℝ) (N : ℕ) :
    finiteMobiusGammaHankelEnergy N (1 + δ) =
      Real.Gamma (1 + δ) * finiteGeneralReciprocalEnergy (1 + δ) δ N := by
  unfold finiteMobiusGammaHankelEnergy finiteGammaHankelEnergy
  congr 1
  unfold finiteGeneralReciprocalEnergy
  rw [sum_Icc_one_eq_shifted_range]
  apply Finset.sum_congr rfl
  intro m hm
  rw [sum_Icc_one_eq_shifted_range]
  apply Finset.sum_congr rfl
  intro n hn
  rw [generalReciprocalMomentKernel_base]
  unfold shiftedMobiusRealCoefficient mobiusRealCoefficient
  push_cast
  have hsum : (m : ℝ) + 1 + ((n : ℝ) + 1) = (m : ℝ) + n + 2 := by ring
  rw [hsum]
  ring

/-- Two positive Gamma-shape rises preserve every signed Möbius coefficient and
control the original finite energy by a source two orders higher. -/
theorem finiteGeneralReciprocalEnergy_le_two_orders
    (R δ : ℝ) (hp : 0 < 2 * R - 1 - δ) (N : ℕ) :
    finiteGeneralReciprocalEnergy R δ N ≤
      (4 * ((2 * R - δ) / (2 * R - 1 - δ))) *
        (4 * ((2 * (R + 1) - δ) / (2 * (R + 1) - 1 - δ))) *
          finiteGeneralReciprocalEnergy (R + 2) δ N := by
  have hp1 : 0 < 2 * (R + 1) - 1 - δ := by linarith
  have hc : 0 ≤ 4 * ((2 * R - δ) / (2 * R - 1 - δ)) := by
    have hnum : 0 < 2 * R - δ := by linarith
    positivity
  have h0 := finiteGeneralReciprocalEnergy_le_succ R δ hp N
  have h1 := finiteGeneralReciprocalEnergy_le_succ (R + 1) δ hp1 N
  calc
    finiteGeneralReciprocalEnergy R δ N ≤
        (4 * ((2 * R - δ) / (2 * R - 1 - δ))) *
          finiteGeneralReciprocalEnergy (R + 1) δ N := h0
    _ ≤ (4 * ((2 * R - δ) / (2 * R - 1 - δ))) *
          ((4 * ((2 * (R + 1) - δ) / (2 * (R + 1) - 1 - δ))) *
            finiteGeneralReciprocalEnergy ((R + 1) + 1) δ N) :=
        mul_le_mul_of_nonneg_left h1 hc
    _ = _ := by rw [show (R + 1) + 1 = R + 2 by ring]; ring

/-- The parameter-coupled source order has an integral polynomial numerator.
Its denominator is the only fractional part of the signed additive kernel. -/
theorem generalReciprocalMomentKernel_three_add_delta (δ : ℝ) (m n : ℕ) :
    generalReciprocalMomentKernel (3 + δ) δ m n =
      (((m : ℝ) * (n : ℝ)) ^ (2 : ℕ)) /
        (((m : ℝ) + (n : ℝ)) ^ (5 + δ)) := by
  unfold generalReciprocalMomentKernel
  have hnum : 3 + δ - 1 - δ = (2 : ℝ) := by ring
  have hden : 2 * (3 + δ) - 1 - δ = 5 + δ := by ring
  rw [hnum, hden]
  simp only [Real.rpow_two]

end
end RHTower
