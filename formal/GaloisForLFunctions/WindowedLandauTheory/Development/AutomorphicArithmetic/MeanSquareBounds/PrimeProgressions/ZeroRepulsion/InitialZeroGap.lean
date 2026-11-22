import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExceptionSelection
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroRepulsion.SignedMomentAlgebra

/-! The ordinary logarithmic zero-free region gives the starting gap for repulsion. -/

open Finset Complex Classical

noncomputable section

namespace QH.PrimeProgressions

open WindowedLandauTheory.ZeroFreeDirichlet

namespace DHF

theorem region_gap : ∃ cR : ℝ, 0 < cR ∧ ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (β₁ T c₁ : ℝ)
    (ρ : ℂ), 3 ≤ M → 2 ≤ T → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 → 0 < c₁ → c₁ ≤ cR →
    1 - c₁ / Real.log ((M : ℝ) * T) < β₁ → IsLZero χ ρ → |ρ.im| ≤ T → (χ, ρ) ≠ (χ₁, (β₁ : ℂ)) →
    cR / 2 ≤ (1 - ρ.re) * Real.log ((M : ℝ) * T) := by
  obtain ⟨cR, hcR, hZ⟩ := zFRDirichlet
  refine ⟨cR, hcR, ?_⟩
  intro M _ χ₁ χ β₁ T c₁ ρ hM hT2 hχ1ne hLz hc₁0 hc₁ hβ₁ hρ hρim hne
  have hLg1 := dhLogOne M T hM hT2
  have hLg0 : 0 < Real.log ((M : ℝ) * T) := by linarith
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog2M : Real.log ((M : ℝ) * (|((β₁ : ℂ)).im| + 2)) ≤ Real.log ((M : ℝ) * T) := by
    simp only [Complex.ofReal_im, abs_zero, zero_add]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hlog2M0 : 0 < Real.log ((M : ℝ) * (|((β₁ : ℂ)).im| + 2)) := by
    apply Real.log_pos; simp only [Complex.ofReal_im, abs_zero, zero_add]; nlinarith
  have hreg : InRegion cR M (β₁ : ℂ) := by
    unfold InRegion
    have h1 : c₁ / Real.log ((M : ℝ) * T) ≤ cR / Real.log ((M : ℝ) * (|((β₁ : ℂ)).im| + 2)) := by
      rw [div_le_div_iff₀ hLg0 hlog2M0]
      have h2 := mul_le_mul_of_nonneg_left hlog2M hc₁0.le
      have h3 := mul_le_mul_of_nonneg_right hc₁ hLg0.le
      linarith only [h2, h3]
    rw [Complex.ofReal_re]; linarith only [h1, hβ₁]
  have hLz' : IsLZero χ₁ (β₁ : ℂ) := ⟨Or.inl hχ1ne, hLz⟩
  have hZ1 := (hZ M χ₁ (β₁ : ℂ) hreg hLz').2.2.2.2
  have hnreg : ¬ InRegion cR M ρ := by
    intro h
    obtain ⟨h1, h2⟩ := hZ1 χ ρ h hρ
    exact hne (Prod.ext h1 h2)
  unfold InRegion at hnreg
  push Not at hnreg
  have hlogρ0 : 0 < Real.log ((M : ℝ) * (|ρ.im| + 2)) := by
    apply Real.log_pos; have := abs_nonneg ρ.im; nlinarith
  have hlogρ : Real.log ((M : ℝ) * (|ρ.im| + 2)) ≤ 2 * Real.log ((M : ℝ) * T) := by
    rw [show (2 : ℝ) * Real.log ((M : ℝ) * T) = Real.log (((M : ℝ) * T) ^ 2) by
      rw [Real.log_pow]; push_cast; ring]
    apply Real.log_le_log (by have := abs_nonneg ρ.im; positivity)
    have : |ρ.im| + 2 ≤ 2 * T := by linarith
    have hM0 : (0 : ℝ) ≤ M := by positivity
    have hMT : (2 : ℝ) ≤ M * T := by nlinarith
    have hMT2 := mul_le_mul_of_nonneg_left hMT (by positivity : (0 : ℝ) ≤ M * T)
    calc (M : ℝ) * (|ρ.im| + 2) ≤ M * (2 * T) := mul_le_mul_of_nonneg_left this hM0
      _ ≤ _ := by rw [sq]; linarith
  have h1 : cR / Real.log ((M : ℝ) * (|ρ.im| + 2)) < 1 - ρ.re := by linarith
  rw [div_lt_iff₀ hlogρ0] at h1
  have hδ0 : 0 < 1 - ρ.re := by
    by_contra h; push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h hlogρ0.le
    linarith
  have := mul_le_mul_of_nonneg_left hlogρ hδ0.le
  linarith

end DHF

end QH.PrimeProgressions
