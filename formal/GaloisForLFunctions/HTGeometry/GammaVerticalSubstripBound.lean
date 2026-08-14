import GaloisForLFunctions.HTGeometry.GammaVerticalRatioBetaBound
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Topology.Order.Compact

/-!
# The vertical Gamma ratio is bounded on a closed substrip

The Beta bound gives `‖Γ(1-y+ix)‖ / ‖Γ(1+y+ix)‖ ≤ Γ(1-y)/Γ(1+y)` for every real `x`, with a right
side that no longer sees the height.  On a compact interval of heights inside `(0,1)` the real
quotient is a continuous function of `y`, so it has a maximum: the ratio is bounded on the whole
closed substrip.
-/

open Complex MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The real Gamma quotient of the substrip is continuous in the height. -/
theorem continuousOn_realGammaRatio {σ₀ σ₁ : ℝ} (h0 : 0 < σ₀) (h1 : σ₁ < 1) :
    ContinuousOn (fun y : ℝ => Real.Gamma (1 - y) / Real.Gamma (1 + y)) (Icc σ₀ σ₁) := by
  intro y hy
  have hy0 : 0 < y := lt_of_lt_of_le h0 hy.1
  have hy1 : y < 1 := lt_of_le_of_lt hy.2 h1
  have hnum : ContinuousAt (fun y : ℝ => Real.Gamma (1 - y)) y := by
    have hd : DifferentiableAt ℝ Real.Gamma (1 - y) := by
      refine Real.differentiableAt_Gamma (fun m => ?_)
      have hpos : (0 : ℝ) < 1 - y := by linarith
      have hnonpos : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      intro hcon
      rw [hcon] at hpos
      linarith
    exact hd.continuousAt.comp (by fun_prop)
  have hden : ContinuousAt (fun y : ℝ => Real.Gamma (1 + y)) y := by
    have hd : DifferentiableAt ℝ Real.Gamma (1 + y) := by
      refine Real.differentiableAt_Gamma (fun m => ?_)
      have hpos : (0 : ℝ) < 1 + y := by linarith
      have hnonpos : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      intro hcon
      rw [hcon] at hpos
      linarith
    exact hd.continuousAt.comp (by fun_prop)
  have hne : Real.Gamma (1 + y) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
  exact ((hnum.div hden hne)).continuousWithinAt

/-- **The vertical Gamma ratio is bounded on a closed substrip.** -/
theorem exists_bound_gammaRatio_substrip {σ₀ σ₁ : ℝ} (h0 : 0 < σ₀) (h01 : σ₀ ≤ σ₁) (h1 : σ₁ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y ∈ Icc σ₀ σ₁, ∀ x : ℝ,
      ‖Complex.Gamma (((1 - y : ℝ) : ℂ) + (x : ℂ) * I)‖
        / ‖Complex.Gamma (((1 + y : ℝ) : ℂ) + (x : ℂ) * I)‖
      ≤ K := by
  obtain ⟨y₀, hy₀mem, hy₀max⟩ := (isCompact_Icc (a := σ₀) (b := σ₁)).exists_isMaxOn
    (Set.nonempty_Icc.mpr h01) (continuousOn_realGammaRatio h0 h1)
  set K : ℝ := Real.Gamma (1 - y₀) / Real.Gamma (1 + y₀) with hK
  have hy₀0 : 0 < y₀ := lt_of_lt_of_le h0 hy₀mem.1
  have hy₀1 : y₀ < 1 := lt_of_le_of_lt hy₀mem.2 h1
  have hK0 : 0 ≤ K := by
    have h1' : 0 < Real.Gamma (1 - y₀) := Real.Gamma_pos_of_pos (by linarith)
    have h2' : 0 < Real.Gamma (1 + y₀) := Real.Gamma_pos_of_pos (by linarith)
    positivity
  refine ⟨K, hK0, fun y hy x => ?_⟩
  have hy0 : 0 < y := lt_of_lt_of_le h0 hy.1
  have hy1 : y < 1 := lt_of_le_of_lt hy.2 h1
  have hsum : (1 - y) + 2 * y = 1 + y := by ring
  have hbound := norm_Gamma_vertical_le (a := 1 - y) (d := 2 * y) (by linarith) (by linarith) x
  rw [hsum] at hbound
  have hden : (0 : ℝ) < ‖Complex.Gamma (((1 + y : ℝ) : ℂ) + (x : ℂ) * I)‖ := by
    refine norm_pos_iff.mpr (Complex.Gamma_ne_zero (fun m => ?_))
    intro hcon
    have hre : (((1 + y : ℝ) : ℂ) + (x : ℂ) * I).re = 1 + y := by simp
    rw [hcon] at hre
    simp at hre
    have : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith
  rw [div_le_iff₀ hden]
  refine le_trans hbound ?_
  refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hden)
  exact hy₀max hy

end

end GaloisForLFunctions.HTGeometry
