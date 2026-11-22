import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ChebyshevPacketAssembly
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.NearRangeScales
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.NearRangeErrors
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.NearRangeZeroSum

/-! The relative Chebyshev estimate for moduli of logarithmic size `O(√log y)`. -/

open Complex Classical
open WindowedLandauTheory.ZeroFreeDirichlet

noncomputable section

namespace QH.PrimeProgressions

/-- Summing the sharp Chebyshev estimates in the near range preserves a relative error
after the exceptional zero is removed. -/
theorem psi_relative_near_range (hE : ExplicitS) (hS : SharpenS) : PsiRelA := by
  obtain ⟨C, hC, hEx⟩ := hE (1 / 20) (by norm_num) le_rfl
  obtain ⟨a, D, ha, hD, hscale⟩ := near_range_scales (1 / 20) C (by norm_num) hC
  obtain ⟨c, hc, heta⟩ := etaOf_lower 1 one_pos
  let B := 4 * C * (1 + D) + 8 * D + 22 + 132 * C * D
  refine ⟨a, a, B / c, ha, ha, ?_⟩
  intro M _ h8 y hy hlog
  have hMₙ : 8 ≤ M := Nat.le_of_dvd (NeZero.pos M) h8
  have hM : (8 : ℝ) ≤ M := by exact_mod_cast hMₙ
  have hM₀ : (0 : ℝ) < M := by linarith
  have hM₃ : 3 ≤ M := by omega
  have hy₀ : 0 < y := by linarith
  let U := Real.exp (a * Real.sqrt (Real.log y))
  let δ := (U ^ 4)⁻¹
  let κ : ℝ := 1 / 20
  let t := y ^ (-(κ / 2))
  obtain ⟨hU, hyU, hp, ht, hl, hl₂, hL, hgap⟩ := hscale M y hM hy hlog
  change (8 : ℝ) ≤ U at hU
  have hU₁ : 1 ≤ U := by linarith
  have hU₀ : 0 < U := by linarith
  have hMU : (M : ℝ) ≤ U := (Real.log_le_iff_le_exp hM₀).mp hlog
  have hT : 2 ≤ U ^ (8 : ℕ) := (by linarith : 2 ≤ U).trans (le_self_pow₀ hU₁ (by norm_num))
  have hδ₀ : 0 < δ := by positivity
  have hδ : δ ≤ 1 / 2 := by
    change (U ^ 4)⁻¹ ≤ 1 / 2
    rw [one_div]
    exact inv_anti₀ (by norm_num) ((show (2 : ℝ) ≤ U by linarith).trans (le_self_pow₀ hU₁ (by norm_num)))
  let E := C * ((((M : ℝ) * U ^ 8) ^ C) * t + Real.log (2 * y) * Real.log ((M : ℝ) * U ^ 8) ^ 2 / U ^ 8)
  have hE₀ : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg hC.le (add_nonneg (by positivity)
      (div_nonneg (mul_nonneg (Real.log_nonneg (by linarith)) (sq_nonneg _)) (by positivity)))
  have hU₇₈ : U ^ (7 : ℕ) ≤ U ^ (8 : ℕ) := pow_le_pow_right₀ hU₁ (by norm_num)
  have hE' : E ≤ C * (1 + D) * (U ^ 7)⁻¹ := by
    calc E ≤ C * ((U ^ 8)⁻¹ + (D * U) / U ^ 8) := mul_le_mul_of_nonneg_left
          (add_le_add hp (div_le_div_of_nonneg_right hl₂ (by positivity))) hC.le
      _ ≤ C * ((U ^ 7)⁻¹ + (D * U) / U ^ 8) := mul_le_mul_of_nonneg_left
          (add_le_add (inv_anti₀ (by positivity) hU₇₈) le_rfl) hC.le
      _ = _ := by field_simp [hU₀.ne'] <;> ring
  choose Z m K hZ hcover hm hsimple hcount herror using fun χ => hEx M χ (U ^ 8) hM₃ hT
  have hre : ∀ χ, ∀ ρ ∈ Z χ, 1 / 2 ≤ ρ.re ∧ ρ.re < 1 := by
    intro χ ρ hρ
    obtain ⟨hz, hlo, -⟩ := hZ χ ρ hρ
    refine ⟨by linarith, lt_of_not_ge fun h => DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hz.1 h hz.2⟩
  have hmain := psi_total_from_zero_packets hM₃ hS Z m K y κ (U ^ 8) δ E hy (by positivity) hδ₀ hδ hE₀
    hcover hre hm (fun χ u hu => by
      have hu₁ : y ≤ u := by rcases hu with rfl | rfl <;> nlinarith only [mul_nonneg hδ₀.le hy₀.le]
      have hu₂ : u ≤ 2 * y := by
        rcases hu with rfl | rfl
        · linarith
        · nlinarith only [mul_le_mul_of_nonneg_right hδ hy₀.le, hy₀]
      refine (herror χ u (hy.trans hu₁)).trans ?_
      have hpow := Real.rpow_le_rpow_of_nonpos hy₀ hu₁ (by norm_num : -(1 / 20 / 2 : ℝ) ≤ 0)
      have hlogu := Real.log_le_log (hy₀.trans_le hu₁) hu₂
      dsimp only [E, t, κ]
      gcongr)
  have hnear := near_range_zero_sum hM₃ Z m hC.le (by positivity : 0 ≤ U ^ (8 : ℕ)) (by linarith : 1 ≤ y)
    (fun χ ρ hρ => ⟨(hZ χ ρ hρ).1, (hZ χ ρ hρ).2.2⟩) hsimple hcount
  have hW := near_range_zero_error hM₀.le hMU hU₁ hC.le hD.le hL hgap (by positivity) hnear
  have he := near_range_ramp_error hM₀.le hMU hU₁ hyU hC.le hD.le hE' hl ht
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have htot : ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤ B * y * (U ^ 2)⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hW (show 0 ≤ 22 * y by positivity)
    dsimp only [B]
    linarith only [hmain, he, h]
  have hη := heta M hM₃
  rw [Real.rpow_neg_one] at hη
  have hUη : U⁻¹ ≤ etaOf M / c := (inv_anti₀ hM₀ hMU).trans ((le_div_iff₀ hc).mpr (by linarith))
  have hUη' : (U ^ 2)⁻¹ ≤ etaOf M / c * U⁻¹ := by
    rw [pow_two, mul_inv_rev]
    exact mul_le_mul_of_nonneg_right hUη (by positivity)
  refine htot.trans ((mul_le_mul_of_nonneg_left hUη' (by positivity)).trans_eq ?_)
  rw [show U⁻¹ = Real.exp (-(a * Real.sqrt (Real.log y))) from (Real.exp_neg _).symm]
  ring

end QH.PrimeProgressions
