/-
# Eliminating Bourgain's first-spacing count

This module joins the exact double-large-sieve inequality to the `A₆`
first-spacing theorem.  It leaves the second-spacing count visible and
replaces the first-spacing count by Bourgain's sharp
`δ Δ H^(9+ε)` majorant.

The theorem is an implication from the sharp `A₆` estimate.  Establishing
that estimate without hypotheses remains a separate obligation.
-/
import GaloisForLFunctions.RHTower.BourgainMomentCloudBounds
import GaloisForLFunctions.RHTower.BourgainA6FirstSpacingBridge

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Bourgain's double-large-sieve bound after the first-spacing count has
been discharged by the sharp `A₆` estimate. -/
theorem bourgainDoubleLargeSieve_shortCurveSum_firstSpacing_of_A6
    {ι : Type*} [Fintype ι]
    (hA6 :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ C : ℝ, 0 < C ∧
          ∀ H : ℕ,
            bourgainA6LiteralMoment H ≤
              C * (H : ℝ) ^ ε * (H : ℝ) ^ (6 : ℕ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ), 0 < H → ∀ (δ Δ : ℝ),
        0 < δ → 0 < Δ →
        1 / (H : ℝ) ^ (2 : ℕ) ≤ δ →
        1 / (H : ℝ) ≤ Δ →
      ∀ (α : Fin H → ℂ) (x : ι → BourgainPhaseSpace),
        (∀ q j,
          |x q j| ≤ bourgainA6FirstSpacingScale H δ Δ j) →
        (∀ h, ‖α h‖ ≤ 1) →
        (∑ i : ι, ‖bourgainShortCurveSum H α (x i)‖) ^
              (12 : ℕ) ≤
          (Fintype.card ι : ℝ) ^ (10 : ℕ) *
            (((Real.exp (4 * Real.pi) * 331776) *
              (∏ j : Fin 4,
                (Real.pi ^ (2 : ℕ) *
                  (1 +
                    bourgainA6FirstSpacingScale H δ Δ j *
                      bourgainMomentCoordinateBound H j)))) *
            ((bourgainScaledNearCount
                (bourgainMomentCoordinateBound H) x : ℝ) *
              (δ * Δ *
                (C * (H : ℝ) ^ ε * (H : ℝ) ^ (9 : ℕ))))) := by
  obtain ⟨C, hC, hfirst⟩ :=
    bourgainFirstSpacingCount_subpower_of_A6 hA6 hε
  refine ⟨C, hC, ?_⟩
  intro H hH δ Δ hδ hΔ hδrange hΔrange α x hx hα
  have hdls :=
    bourgainDoubleLargeSieve_shortCurveSum_coordinateBound
      α x hH
        (bourgainA6FirstSpacingScale_pos hH hδ hΔ)
        hx hα
  have hfirst' :=
    hfirst H hH hδ hΔ hδrange hΔrange
  have hcount0 :
      0 ≤ (bourgainScaledNearCount
        (bourgainMomentCoordinateBound H) x : ℝ) := by
    positivity
  have hscale0 :
      0 ≤ (Real.exp (4 * Real.pi) * 331776) *
        (∏ j : Fin 4,
          (Real.pi ^ (2 : ℕ) *
            (1 +
              bourgainA6FirstSpacingScale H δ Δ j *
                bourgainMomentCoordinateBound H j))) := by
    apply mul_nonneg
    · exact mul_nonneg (Real.exp_pos _).le (by norm_num)
    · exact Finset.prod_nonneg fun j hj => by
        apply mul_nonneg (sq_nonneg _)
        have hXY :
            0 ≤ bourgainA6FirstSpacingScale H δ Δ j *
              bourgainMomentCoordinateBound H j :=
          mul_nonneg
            (bourgainA6FirstSpacingScale_pos hH hδ hΔ j).le
            (bourgainMomentCoordinateBound_pos hH j).le
        linarith
  calc
    (∑ i : ι, ‖bourgainShortCurveSum H α (x i)‖) ^
          (12 : ℕ) ≤
        (Fintype.card ι : ℝ) ^ (10 : ℕ) *
          (((Real.exp (4 * Real.pi) * 331776) *
            (∏ j : Fin 4,
              (Real.pi ^ (2 : ℕ) *
                (1 +
                  bourgainA6FirstSpacingScale H δ Δ j *
                    bourgainMomentCoordinateBound H j)))) *
          ((bourgainScaledNearCount
              (bourgainMomentCoordinateBound H) x : ℝ) *
            (bourgainFirstSpacingCount H
              (bourgainA6FirstSpacingScale H δ Δ) : ℝ))) :=
      hdls
    _ ≤
        (Fintype.card ι : ℝ) ^ (10 : ℕ) *
          (((Real.exp (4 * Real.pi) * 331776) *
            (∏ j : Fin 4,
              (Real.pi ^ (2 : ℕ) *
                (1 +
                  bourgainA6FirstSpacingScale H δ Δ j *
                    bourgainMomentCoordinateBound H j)))) *
          ((bourgainScaledNearCount
              (bourgainMomentCoordinateBound H) x : ℝ) *
            (δ * Δ *
              (C * (H : ℝ) ^ ε * (H : ℝ) ^ (9 : ℕ))))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hfirst' hcount0)
          hscale0)
        (by positivity)

end

end RHTower
