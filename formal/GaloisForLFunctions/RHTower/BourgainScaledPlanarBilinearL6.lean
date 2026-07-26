/-
# Physical-scale factorized planar bilinear `L⁶` estimate

This module transports the independent two-parabola moment from the
four-torus to the literal physical box `[0,H²]⁴`.  The four-dimensional
integral factors exactly by Fubini, and each planar factor is handled by
`BourgainScaledParabolaDecoupling`.
-/
import GaloisForLFunctions.RHTower.BourgainScaledParabolaDecoupling

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Normalized physical-box moment of two independent scaled parabola
extensions. -/
def bourgainScaledIndependentPlanarBilinearMoment
    (H : ℕ) (a b : Fin H → ℂ) : ℝ :=
  ((H : ℝ) ^ (8 : ℕ))⁻¹ *
    ∫ y₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
      ∫ x₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        ∫ y₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ∫ x₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
            ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^ (6 : ℕ) *
              ‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^ (6 : ℕ)

/-- The unnormalized four-dimensional physical moment factors into its two
planar moments. -/
theorem integral_scaledIndependentPlanarBilinear_eq_mul
    (H : ℕ) (a b : Fin H → ℂ) :
    (∫ y₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
      ∫ x₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        ∫ y₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ∫ x₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
            ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^ (6 : ℕ) *
              ‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^ (6 : ℕ)) =
      (∫ y₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        ∫ x₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^ (6 : ℕ)) *
      (∫ y₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        ∫ x₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^ (6 : ℕ)) := by
  have hinner (x₂ y₂ y₁ : ℝ) :
      (∫ x₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^ (6 : ℕ) *
          ‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^ (6 : ℕ)) =
        (∫ x₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^ (6 : ℕ)) *
          ‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^ (6 : ℕ) := by
    exact intervalIntegral.integral_mul_const
      (‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^ (6 : ℕ))
      (fun x₁ =>
        ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^ (6 : ℕ))
  simp_rw [hinner]
  have hfirst (x₂ y₂ : ℝ) :
      (∫ y₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        (∫ x₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^ (6 : ℕ)) *
          ‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^ (6 : ℕ)) =
        (∫ y₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ∫ x₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
            ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^ (6 : ℕ)) *
          ‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^ (6 : ℕ) := by
    exact intervalIntegral.integral_mul_const
      (‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^ (6 : ℕ))
      (fun y₁ =>
        ∫ x₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^ (6 : ℕ))
  simp_rw [hfirst]
  have hsecond (y₂ : ℝ) :
      (∫ x₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        (∫ y₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ∫ x₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
            ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^ (6 : ℕ)) *
          ‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^ (6 : ℕ)) =
        (∫ y₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ∫ x₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
            ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^ (6 : ℕ)) *
          ∫ x₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
            ‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^ (6 : ℕ) := by
    exact intervalIntegral.integral_const_mul
      (∫ y₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        ∫ x₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^ (6 : ℕ))
      (fun x₂ =>
        ‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^ (6 : ℕ))
  rw [show
    (fun y₂ : ℝ =>
      ∫ x₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        (∫ y₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ∫ x₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
            ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^ (6 : ℕ)) *
          ‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^ (6 : ℕ)) =
      (fun y₂ : ℝ =>
        (∫ y₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ∫ x₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
            ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^ (6 : ℕ)) *
          ∫ x₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
            ‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^ (6 : ℕ)) by
        funext y₂
        exact hsecond y₂]
  exact intervalIntegral.integral_const_mul
    (∫ y₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
      ∫ x₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^ (6 : ℕ))
    (fun y₂ =>
      ∫ x₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        ‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^ (6 : ℕ))

/-- Exact equality between normalized physical and four-torus independent
bilinear moments. -/
theorem bourgainScaledIndependentPlanarBilinearMoment_eq_torus
    (H : ℕ) (hH : 0 < H) (a b : Fin H → ℂ) :
    bourgainScaledIndependentPlanarBilinearMoment H a b =
      bourgainIndependentPlanarBilinearMoment H H a b := by
  unfold bourgainScaledIndependentPlanarBilinearMoment
  rw [integral_scaledIndependentPlanarBilinear_eq_mul]
  rw [integral_scaledParabola_physicalSquare_eq H hH a,
    integral_scaledParabola_physicalSquare_eq H hH b]
  rw [integral_unitSquare_discreteParabola_norm_pow_six_eq,
    integral_unitSquare_discreteParabola_norm_pow_six_eq]
  rw [bourgainIndependentPlanarBilinearMoment_eq_mul]
  unfold bourgainParabolaL6Moment
  have hH0 : (H : ℝ) ^ (8 : ℕ) ≠ 0 := by positivity
  field_simp

/-- Unconditional subpower estimate for the physical, factorized local
bilinear model. -/
theorem bourgainScaledIndependentPlanarBilinearMoment_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ), 0 < H → ∀ (a b : Fin H → ℂ),
        bourgainScaledIndependentPlanarBilinearMoment H a b ≤
          C * (H : ℝ) ^ ε *
            (∑ n : Fin H, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
            (∑ n : Fin H, ‖b n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  obtain ⟨C, hC, hbound⟩ :=
    bourgainIndependentPlanarBilinearMoment_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H hH a b
  rw [bourgainScaledIndependentPlanarBilinearMoment_eq_torus H hH a b]
  exact hbound H a b

end

end RHTower
