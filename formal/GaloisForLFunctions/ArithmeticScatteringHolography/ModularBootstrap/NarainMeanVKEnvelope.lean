import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainVKParameters
import GaloisForLFunctions.RHTower.SmoothDyadicZetaReflection

/-!
# Uniform arithmetic rectangles for the averaged Narain Mellin transform

Compact analyticity fills the low ordinates of the exponential strip envelope.
The resulting bound holds throughout every admissible shrinking rectangle.
-/

open Complex RHTower Set
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Compact control at the removable center completes the uniform exponential envelope
on every shrinking arithmetic rectangle. -/
theorem exists_narainMellinMean_vk_envelope (Y Z : Height) :
    ∃ δ T₀ C : ℝ, ∃ N : ℕ, 0 < δ ∧ 3 ≤ T₀ ∧
      Real.exp (Real.exp 1) ≤ T₀ ∧ 0 ≤ C ∧
      ∀ T : ℝ, T₀ ≤ T →
        0 < narainVKWidth δ T ∧ narainVKWidth δ T ≤ 1 / 8 ∧
        ∀ u : ℂ, -narainVKWidth δ T ≤ u.re → u.re ≤ 0 → |u.im| ≤ T →
          AnalyticAt ℂ (narainMellinMean Y Z) u ∧
          ‖narainMellinMean Y Z u‖ ≤
            C * (1 + |u.im|) ^ N * Real.exp (-(Real.pi * |u.im| / 2)) * narainVKCost T := by
  obtain ⟨δ, T₁, C₁, N, hδ, hT₁, hC₁, h⟩ := exists_narainMellinMean_vk_strip Y Z
  let S : ℝ := max T₁ (Real.exp (Real.exp 1))
  have hS₁ : T₁ ≤ S := le_max_left _ _
  have hSexp : Real.exp (Real.exp 1) ≤ S := le_max_right _ _
  have hS3 : 3 ≤ S := hT₁.trans hS₁
  have hSwidth : Real.exp (Real.exp 1) ≤ 2 * S + 1 := by linarith only [hSexp, hS3]
  obtain ⟨B, hB, hcore⟩ := exists_norm_le_on_rect
    (f := narainMellinMean Y Z) (a := -narainVKWidth δ S) (b := 0) (c := 1)
    (fun σ t hlo hhi ht =>
      ((h S hS₁).2.2 ((σ : ℂ) + (t : ℂ) * I)
        (by simpa using hlo) (by simpa using hhi)
        (by simp; linarith only [ht, hS3])).1.continuousAt)
  let C : ℝ := C₁ + B * Real.exp (Real.pi / 2)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hC₁C : C₁ ≤ C := le_add_of_nonneg_right (by positivity)
  have hBC : B * Real.exp (Real.pi / 2) ≤ C := by dsimp only [C]; linarith only [hC₁]
  refine ⟨δ, S, C, N, hδ, hS3, hSexp, hC, ?_⟩
  intro T hT
  obtain ⟨hd, hd8, hrect⟩ := h T (hS₁.trans hT)
  refine ⟨hd, hd8, ?_⟩
  intro u hlo hhi ht
  have ha := hrect u hlo hhi ht
  refine ⟨ha.1, ?_⟩
  have hTwidth : Real.exp (Real.exp 1) ≤ 2 * T + 1 := by
    linarith only [hSexp, hS3, hT]
  have hQ := one_le_narainVKCost hTwidth
  by_cases hlarge : 1 ≤ |u.im|
  · exact (ha.2 hlarge).trans (by gcongr)
  · have hsmall : |u.im| ≤ 1 := (lt_of_not_ge hlarge).le
    have hwidth := narainVKWidth_anti δ hSwidth hT
    have hlow : -narainVKWidth δ S ≤ u.re := by linarith only [hlo, hwidth]
    have hb : ‖narainMellinMean Y Z u‖ ≤ B := by
      simpa only [Complex.re_add_im] using hcore u.re u.im hlow hhi hsmall
    have hpoly : 1 ≤ (1 + |u.im|) ^ N :=
      one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg _))
    have hexp : Real.exp (-(Real.pi / 2)) ≤ Real.exp (-(Real.pi * |u.im| / 2)) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hsmall, Real.pi_pos]
    have hcancel : Real.exp (Real.pi / 2) * Real.exp (-(Real.pi / 2)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc
      _ ≤ B := hb
      _ = (B * Real.exp (Real.pi / 2)) * 1 * Real.exp (-(Real.pi / 2)) * 1 := by
        rw [mul_one, mul_one, mul_assoc, hcancel, mul_one]
      _ ≤ C * (1 + |u.im|) ^ N * Real.exp (-(Real.pi * |u.im| / 2)) * narainVKCost T := by
        gcongr

#print axioms exists_narainMellinMean_vk_envelope
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
