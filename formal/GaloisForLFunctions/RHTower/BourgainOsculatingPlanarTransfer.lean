/-
# Discrete planar estimate in Bourgain's osculating coordinates

This module specializes the literal phase-coordinate change from
`BourgainOsculatingPhaseCoordinates` to the physical discrete parabola
extensions.  It proves the exact one-box pullback estimate used in
Bourgain (1.23)--(1.24), including the Jacobian, the `H⁸` volume factor,
and the unconditional subpower coefficient loss.
-/
import GaloisForLFunctions.RHTower.BourgainOsculatingPhaseCoordinates
import GaloisForLFunctions.RHTower.BourgainScaledPlanarBilinearL6
import GaloisForLFunctions.RHTower.BourgainFinTonelli

open MeasureTheory

namespace RHTower

noncomputable section

/-- Pointwise sixth power of a physical scaled parabola extension. -/
def bourgainScaledPlanarSixthMass
    (H : ℕ) (a : Fin H → ℂ) (x y : ℝ) : ℝ :=
  ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ)

/-- Product of the two independent physical planar sixth-power masses. -/
def bourgainScaledIndependentPlanarBilinearIntegrand
    (H : ℕ) (a b : Fin H → ℂ) (y : Fin 4 → ℝ) : ℝ :=
  bourgainScaledPlanarSixthMass H a (y 0) (y 1) *
    bourgainScaledPlanarSixthMass H b (y 2) (y 3)

theorem continuous_uncurry_bourgainScaledPlanarSixthMass
    (H : ℕ) (a : Fin H → ℂ) :
    Continuous (Function.uncurry (bourgainScaledPlanarSixthMass H a)) := by
  unfold bourgainScaledPlanarSixthMass
    bourgainScaledParabolaExtension
    bourgainDiscreteParabolaExtension
    bourgainUnitCharacter
  fun_prop

theorem measurable_ofReal_bourgainScaledIndependentPlanarBilinearIntegrand
    (H : ℕ) (a b : Fin H → ℂ) :
    Measurable fun y : Fin 4 → ℝ =>
      ENNReal.ofReal
        (bourgainScaledIndependentPlanarBilinearIntegrand H a b y) := by
  unfold bourgainScaledIndependentPlanarBilinearIntegrand
    bourgainScaledPlanarSixthMass
    bourgainScaledParabolaExtension
    bourgainDiscreteParabolaExtension
    bourgainUnitCharacter
  fun_prop

/-- The centered `Fin 4` norm cube of radius `H²/2` is exactly one physical
period box for the two independent planar factors. -/
theorem setLIntegral_scaledIndependentPlanarBilinear_normCube_eq
    (H : ℕ) (hH : 0 < H) (a b : Fin H → ℂ) :
    (∫⁻ y in
        {y : Fin 4 → ℝ |
          ‖y‖ ≤ (H : ℝ) ^ (2 : ℕ) / 2},
        ENNReal.ofReal
          (bourgainScaledIndependentPlanarBilinearIntegrand H a b y)) =
      ENNReal.ofReal
        (∫ y₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ∫ x₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
            ∫ y₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
              ∫ x₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
                ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^ (6 : ℕ) *
                  ‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^ (6 : ℕ)) := by
  let R : ℝ := (H : ℝ) ^ (2 : ℕ) / 2
  let A : ℝ → ℝ → ℝ := bourgainScaledPlanarSixthMass H a
  let B : ℝ → ℝ → ℝ := bourgainScaledPlanarSixthMass H b
  have hR : 0 ≤ R := by positivity
  rw [setLIntegral_fin_four_normCube hR _
    (measurable_ofReal_bourgainScaledIndependentPlanarBilinearIntegrand
      H a b)]
  change
    (∫⁻ x₀ in Set.Icc (-R) R,
      ∫⁻ x₁ in Set.Icc (-R) R,
        ∫⁻ x₂ in Set.Icc (-R) R,
          ∫⁻ x₃ in Set.Icc (-R) R,
            ENNReal.ofReal (A x₀ x₁ * B x₂ x₃)) = _
  rw [lintegral_Icc_four_ofReal_mul_eq A B
    (fun _ _ => by
      dsimp [A, bourgainScaledPlanarSixthMass]
      positivity)
    (continuous_uncurry_bourgainScaledPlanarSixthMass H a).measurable
    (continuous_uncurry_bourgainScaledPlanarSixthMass H b).measurable]
  rw [lintegral_Icc_Icc_ofReal_eq_ofReal_intervalIntegral hR A
    (continuous_uncurry_bourgainScaledPlanarSixthMass H a)
    (fun _ _ => by
      dsimp [A, bourgainScaledPlanarSixthMass]
      positivity)]
  rw [lintegral_Icc_Icc_ofReal_eq_ofReal_intervalIntegral hR B
    (continuous_uncurry_bourgainScaledPlanarSixthMass H b)
    (fun _ _ => by
      dsimp [B, bourgainScaledPlanarSixthMass]
      positivity)]
  have htrans (c : Fin H → ℂ) :
      (∫ y in (-R)..R, ∫ x in (-R)..R,
          bourgainScaledPlanarSixthMass H c x y) =
        ∫ y in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ∫ x in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
            ‖bourgainScaledParabolaExtension H c x y‖ ^ (6 : ℕ) := by
    have hupper :
        -R + (H : ℝ) ^ (2 : ℕ) = R := by
      dsimp only [R]
      ring
    simpa only [bourgainScaledPlanarSixthMass, hupper] using
      integral_scaledParabola_translatedPhysicalSquare_eq
        H hH c (-R) (-R)
  rw [htrans a, htrans b]
  have hnonneg (c : Fin H → ℂ) :
      0 ≤
        ∫ y in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ∫ x in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
            ‖bourgainScaledParabolaExtension H c x y‖ ^ (6 : ℕ) := by
    apply intervalIntegral.integral_nonneg (by positivity)
    intro y hy
    apply intervalIntegral.integral_nonneg (by positivity)
    intro x hx
    positivity
  rw [← ENNReal.ofReal_mul (hnonneg a)]
  congr 1
  exact (integral_scaledIndependentPlanarBilinear_eq_mul H a b).symm

/-- Literal localized version of Bourgain (1.23)--(1.24), specialized to the
physical discrete planar extensions. The scale hypothesis says the image
of the source cube fits in one centered physical period box. -/
theorem setLIntegral_comp_phaseCoordinates_scaledBilinear_le
    {a₀ b₀ N : ℝ} (ha₀ : 0 < a₀) (ha₀b₀ : a₀ < b₀)
    (H : ℕ) (hH : 0 < H) (a b : Fin H → ℂ)
    (hscale :
      ‖(bourgainSquareRootPhaseCoordinateContinuousLinearEquiv ha₀ ha₀b₀ :
          (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖ * N ≤
        (H : ℝ) ^ (2 : ℕ) / 2) :
    (∫⁻ x in {x : Fin 4 → ℝ | ‖x‖ ≤ N},
      ENNReal.ofReal
        (bourgainScaledIndependentPlanarBilinearIntegrand H a b
          (bourgainSquareRootPhaseCoordinates a₀ b₀ x))) ≤
      ENNReal.ofReal
          |(3 * (b₀ - a₀) ^ (4 : ℕ) /
            (32 * a₀ ^ (3 : ℕ) * b₀ ^ (3 : ℕ)))⁻¹| *
        ENNReal.ofReal
          (∫ y₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
            ∫ x₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
              ∫ y₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
                ∫ x₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
                  ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^ (6 : ℕ) *
                    ‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^
                      (6 : ℕ)) := by
  let g : (Fin 4 → ℝ) → ENNReal := fun y =>
    ENNReal.ofReal
      (bourgainScaledIndependentPlanarBilinearIntegrand H a b y)
  let C : ℝ :=
    ‖(bourgainSquareRootPhaseCoordinateContinuousLinearEquiv ha₀ ha₀b₀ :
      (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖
  let S : ℝ := (H : ℝ) ^ (2 : ℕ) / 2
  have hg : Measurable g :=
    measurable_ofReal_bourgainScaledIndependentPlanarBilinearIntegrand
      H a b
  have hsubset :
      {y : Fin 4 → ℝ | ‖y‖ ≤ C * N} ⊆
        {y : Fin 4 → ℝ | ‖y‖ ≤ S} := by
    intro y hy
    exact hy.trans hscale
  calc
    (∫⁻ x in {x : Fin 4 → ℝ | ‖x‖ ≤ N},
        ENNReal.ofReal
          (bourgainScaledIndependentPlanarBilinearIntegrand H a b
            (bourgainSquareRootPhaseCoordinates a₀ b₀ x))) ≤
        ENNReal.ofReal
            |(3 * (b₀ - a₀) ^ (4 : ℕ) /
              (32 * a₀ ^ (3 : ℕ) * b₀ ^ (3 : ℕ)))⁻¹| *
          ∫⁻ y in {y : Fin 4 → ℝ | ‖y‖ ≤ C * N}, g y := by
            simpa [g, C] using
              setLIntegral_comp_bourgainSquareRootPhaseCoordinates_le
                ha₀ ha₀b₀ g hg
    _ ≤
        ENNReal.ofReal
            |(3 * (b₀ - a₀) ^ (4 : ℕ) /
              (32 * a₀ ^ (3 : ℕ) * b₀ ^ (3 : ℕ)))⁻¹| *
          ∫⁻ y in {y : Fin 4 → ℝ | ‖y‖ ≤ S}, g y :=
      mul_le_mul_right
        (MeasureTheory.lintegral_mono_set hsubset) _
    _ = _ := by
      rw [show S = (H : ℝ) ^ (2 : ℕ) / 2 by rfl]
      rw [show g = fun y =>
          ENNReal.ofReal
            (bourgainScaledIndependentPlanarBilinearIntegrand H a b y) by
        rfl]
      rw [setLIntegral_scaledIndependentPlanarBilinear_normCube_eq
        H hH a b]

/-- Unnormalized physical bilinear mass has the expected volume factor
`H⁸` and only subpower loss beyond it. -/
theorem integral_scaledIndependentPlanarBilinear_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ), 0 < H → ∀ (a b : Fin H → ℂ),
        (∫ y₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ∫ x₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
            ∫ y₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
              ∫ x₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
                ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^ (6 : ℕ) *
                  ‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^
                    (6 : ℕ)) ≤
          (H : ℝ) ^ (8 : ℕ) *
            (C * (H : ℝ) ^ ε *
              (∑ n : Fin H, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
              (∑ n : Fin H, ‖b n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) := by
  obtain ⟨C, hC, hbound⟩ :=
    bourgainScaledIndependentPlanarBilinearMoment_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H hH a b
  let I : ℝ :=
    ∫ y₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
      ∫ x₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        ∫ y₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ∫ x₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
            ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^ (6 : ℕ) *
              ‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^ (6 : ℕ)
  have hrecover :
      I = (H : ℝ) ^ (8 : ℕ) *
        bourgainScaledIndependentPlanarBilinearMoment H a b := by
    unfold bourgainScaledIndependentPlanarBilinearMoment
    dsimp only [I]
    have hH8 : (H : ℝ) ^ (8 : ℕ) ≠ 0 := by positivity
    field_simp
  rw [show
    (∫ y₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
      ∫ x₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        ∫ y₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ∫ x₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
            ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^ (6 : ℕ) *
              ‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^ (6 : ℕ)) = I
      by rfl,
    hrecover]
  exact mul_le_mul_of_nonneg_left (hbound H hH a b) (by positivity)

/-- Sharp localized discrete planar estimate after Bourgain's literal
osculating change of variables. -/
theorem setLIntegral_comp_phaseCoordinates_scaledBilinear_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {a₀ b₀ N : ℝ}, (ha₀ : 0 < a₀) → (ha₀b₀ : a₀ < b₀) →
      ∀ (H : ℕ), 0 < H → ∀ (a b : Fin H → ℂ),
      ‖(bourgainSquareRootPhaseCoordinateContinuousLinearEquiv
          (a := a₀) (b := b₀) ha₀ ha₀b₀ :
          (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖ * N ≤
          (H : ℝ) ^ (2 : ℕ) / 2 →
      (∫⁻ x in {x : Fin 4 → ℝ | ‖x‖ ≤ N},
        ENNReal.ofReal
          (bourgainScaledIndependentPlanarBilinearIntegrand H a b
            (bourgainSquareRootPhaseCoordinates a₀ b₀ x))) ≤
        ENNReal.ofReal
            |(3 * (b₀ - a₀) ^ (4 : ℕ) /
              (32 * a₀ ^ (3 : ℕ) * b₀ ^ (3 : ℕ)))⁻¹| *
          ENNReal.ofReal
            ((H : ℝ) ^ (8 : ℕ) *
              (C * (H : ℝ) ^ ε *
                (∑ n : Fin H, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
                (∑ n : Fin H, ‖b n‖ ^ (2 : ℕ)) ^ (3 : ℕ))) := by
  obtain ⟨C, hC, hmass⟩ :=
    integral_scaledIndependentPlanarBilinear_subpower hε
  refine ⟨C, hC, ?_⟩
  intro a₀ b₀ N ha₀ ha₀b₀ H hH a b hscale
  calc
    (∫⁻ x in {x : Fin 4 → ℝ | ‖x‖ ≤ N},
        ENNReal.ofReal
          (bourgainScaledIndependentPlanarBilinearIntegrand H a b
            (bourgainSquareRootPhaseCoordinates a₀ b₀ x))) ≤
        ENNReal.ofReal
            |(3 * (b₀ - a₀) ^ (4 : ℕ) /
              (32 * a₀ ^ (3 : ℕ) * b₀ ^ (3 : ℕ)))⁻¹| *
          ENNReal.ofReal
            (∫ y₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
              ∫ x₂ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
                ∫ y₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
                  ∫ x₁ in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
                    ‖bourgainScaledParabolaExtension H a x₁ y₁‖ ^
                        (6 : ℕ) *
                      ‖bourgainScaledParabolaExtension H b x₂ y₂‖ ^
                        (6 : ℕ)) :=
      setLIntegral_comp_phaseCoordinates_scaledBilinear_le
        ha₀ ha₀b₀ H hH a b hscale
    _ ≤ _ := by
      exact mul_le_mul_right
        (ENNReal.ofReal_le_ofReal (hmass H hH a b)) _

end

end RHTower
