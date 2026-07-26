/-
# Normalized exact-curve decoupling on one physical period cell

This module transports the unconditional normalized four-cube estimate
through the exact generic osculating-coordinate Jacobian.  The resulting
bound has the sharp natural-scale factor `H⁶` and the exact two-base jet
determinant.
-/
import GaloisForLFunctions.RHTower.BourgainGenericScaledPhaseJacobian
import GaloisForLFunctions.RHTower.BourgainNaturalScaleCellTransfer

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Sharp bilinear sixth moment for the exact normalized curve on one
pulled-back physical period cell. -/
theorem
    setLIntegral_bourgainNormalizedExactLocalSum_fundamentalCell_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (hH : 0 < H)
        {q D a b : ℝ}
        (hq : 0 < q) (hq1 : q ≤ 1 / 2)
        (hD : 0 < D) (hHD : (H : ℝ) ≤ D)
        (ha0 : 0 ≤ a) (ha1 : a + (H : ℝ) / D ≤ 1)
        (hb0 : 0 ≤ b) (hb1 : b + (H : ℝ) / D ≤ 1)
        (hab : 1 / 4 ≤ b - a)
        (hsmall :
          50331648000 * (H : ℝ) ^ (3 : ℕ) / D ≤ 1 / 24),
      let φ₃ := bourgainNormalizedCubicRemainder q
      let φ₄ := bourgainNormalizedQuarticRemainder q
      let haIcc : a ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact ha0
        · have : 0 ≤ (H : ℝ) / D := by positivity
          linarith
      let hbIcc : b ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact hb0
        · have : 0 ≤ (H : ℝ) / D := by positivity
          linarith
      let _hunit :=
        isUnit_bourgainGenericPhaseCoordinateMatrix_normalized
          hq hq1 haIcc hbIcc hab
      let _hscale : (H : ℝ) / D ≠ 0 :=
        div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
      let _hHDWitness := hHD
      let _hsmallWitness := hsmall
      ∀ (c₁ c₂ : Fin H → ℂ),
        (∫⁻ x in bourgainGenericOsculatingFundamentalCell
            H φ₃ φ₄ ((H : ℝ) / D) a b,
          ENNReal.ofReal
            (‖bourgainGenericFourCurveExactLocalSum
                H φ₃ φ₄ D a c₁ x‖ ^ (6 : ℕ) *
              ‖bourgainGenericFourCurveExactLocalSum
                H φ₃ φ₄ D b c₂ x‖ ^ (6 : ℕ))) ≤
          ENNReal.ofReal
              |((((H : ℝ) / D) ^ (6 : ℕ)) *
                (bourgainGenericPhaseCoordinateMatrix
                  φ₃ φ₄ a b).det)⁻¹| *
            ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) *
            ENNReal.ofReal
              (C * (H : ℝ) ^ ε *
                (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
                (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) := by
  obtain ⟨C, hC, hcube⟩ :=
    setLIntegral_bourgainNormalizedExactLocalSum_fourCube_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H hH q D a b hq hq1 hD hHD
    ha0 ha1 hb0 hb1 hab hsmall
  dsimp only
  let φ₃ := bourgainNormalizedCubicRemainder q
  let φ₄ := bourgainNormalizedQuarticRemainder q
  have haIcc : a ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact ha0
    · have : 0 ≤ (H : ℝ) / D := by positivity
      linarith
  have hbIcc : b ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact hb0
    · have : 0 ≤ (H : ℝ) / D := by positivity
      linarith
  let hunit :=
    isUnit_bourgainGenericPhaseCoordinateMatrix_normalized
      hq hq1 haIcc hbIcc hab
  let hscale : (H : ℝ) / D ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
  let E :=
    bourgainGenericScaledPhaseContinuousLinearEquiv
      φ₃ φ₄ hscale hunit
  let X := bourgainIndependentParabolaNaturalScale H
  intro c₁ c₂
  let F : BourgainPhaseSpace → ENNReal := fun x =>
    ENNReal.ofReal
      (‖bourgainGenericFourCurveExactLocalSum
          H φ₃ φ₄ D a c₁ x‖ ^ (6 : ℕ) *
        ‖bourgainGenericFourCurveExactLocalSum
          H φ₃ φ₄ D b c₂ x‖ ^ (6 : ℕ))
  let g : BourgainPhaseSpace → ENNReal := fun y => F (E.symm y)
  have hF : Measurable F := by
    unfold F bourgainGenericFourCurveExactLocalSum
      bourgainGenericFourCurve bourgainUnitCharacter bourgainDot
    fun_prop
  have hg : Measurable g :=
    hF.comp E.symm.continuous.measurable
  have hchange :=
    setLIntegral_bourgainGenericOsculatingFundamentalCell_eq
      H φ₃ φ₄ hscale hunit F hF
  have hnatural :=
    setLIntegral_bourgainParabolaFundamentalCell_le_naturalScale_fourCube
      H hH g hg
  calc
    (∫⁻ x in bourgainGenericOsculatingFundamentalCell
        H φ₃ φ₄ ((H : ℝ) / D) a b,
      ENNReal.ofReal
        (‖bourgainGenericFourCurveExactLocalSum
            H φ₃ φ₄ D a c₁ x‖ ^ (6 : ℕ) *
          ‖bourgainGenericFourCurveExactLocalSum
            H φ₃ φ₄ D b c₂ x‖ ^ (6 : ℕ))) =
      ENNReal.ofReal
          |((((H : ℝ) / D) ^ (6 : ℕ)) *
            (bourgainGenericPhaseCoordinateMatrix
              φ₃ φ₄ a b).det)⁻¹| *
        ∫⁻ y in bourgainParabolaFundamentalCell H, g y := by
          simpa [F, g, E] using hchange
    _ ≤ ENNReal.ofReal
          |((((H : ℝ) / D) ^ (6 : ℕ)) *
            (bourgainGenericPhaseCoordinateMatrix
              φ₃ φ₄ a b).det)⁻¹| *
        (ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) *
          ∫⁻ x in bourgainFourCube,
            g (bourgainCoordinateScale X x)) := by
              exact mul_le_mul_right hnatural _
    _ ≤ ENNReal.ofReal
          |((((H : ℝ) / D) ^ (6 : ℕ)) *
            (bourgainGenericPhaseCoordinateMatrix
              φ₃ φ₄ a b).det)⁻¹| *
        (ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) *
          ENNReal.ofReal
            (C * (H : ℝ) ^ ε *
              (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
              (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ))) := by
                apply mul_le_mul_right
                apply mul_le_mul_right
                simpa [g, F, E, X, φ₃, φ₄] using
                  hcube H hH hq hq1 hD hHD
                    ha0 ha1 hb0 hb1 hab hsmall c₁ c₂
    _ = _ := by ring

end

end RHTower
