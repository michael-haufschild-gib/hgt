/-
# Normalized exact-curve decoupling on the four-cube

The paired Fourier identity converts the unconditional normalized Gaussian
estimate into a literal bilinear sixth-moment estimate on the normalized
four-cube.
-/
import GaloisForLFunctions.RHTower.BourgainGenericPairedTripleFourierIdentity

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Sharp bilinear sixth moment for the exact normalized curve on one
four-cube. -/
theorem integral_bourgainNormalizedExactLocalSum_fourCube_subpower
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
      let hunit :=
        isUnit_bourgainGenericPhaseCoordinateMatrix_normalized
          hq hq1 haIcc hbIcc hab
      let hscale : (H : ℝ) / D ≠ 0 :=
        div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
      let E :=
        bourgainGenericScaledPhaseContinuousLinearEquiv
          (bourgainNormalizedCubicRemainder q)
          (bourgainNormalizedQuarticRemainder q) hscale hunit
      let X := bourgainIndependentParabolaNaturalScale H
      ∀ (c₁ c₂ : Fin H → ℂ),
        (∫ x in bourgainFourCube,
          ‖bourgainGenericFourCurveExactLocalSum H
              (bourgainNormalizedCubicRemainder q)
              (bourgainNormalizedQuarticRemainder q)
              D a c₁ (E.symm (bourgainCoordinateScale X x))‖ ^
                (6 : ℕ) *
            ‖bourgainGenericFourCurveExactLocalSum H
              (bourgainNormalizedCubicRemainder q)
              (bourgainNormalizedQuarticRemainder q)
              D b c₂ (E.symm (bourgainCoordinateScale X x))‖ ^
                (6 : ℕ)) ≤
          C * (H : ℝ) ^ ε *
            (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
            (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  obtain ⟨C₀, hC₀, hgaussian⟩ :=
    integral_bourgainNormalizedExactPaired_gaussian_subpower hε
  refine ⟨Real.exp (4 * Real.pi) * C₀,
    mul_pos (Real.exp_pos _) hC₀, ?_⟩
  intro H hH q D a b hq hq1 hD hHD ha0 ha1 hb0 hb1 hab hsmall
  dsimp only
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
      (bourgainNormalizedCubicRemainder q)
      (bourgainNormalizedQuarticRemainder q) hscale hunit
  let X := bourgainIndependentParabolaNaturalScale H
  let p : Fin H → BourgainPhaseSpace :=
    bourgainGenericExactLeftFrequency
      (bourgainNormalizedCubicRemainder q)
      (bourgainNormalizedQuarticRemainder q)
      hscale hunit D
  let r : Fin H → BourgainPhaseSpace :=
    bourgainGenericExactRightFrequency
      (bourgainNormalizedCubicRemainder q)
      (bourgainNormalizedQuarticRemainder q)
      hscale hunit D
  intro c₁ c₂
  let w : (Fin 3 → Fin H) × (Fin 3 → Fin H) → ℂ :=
    bourgainPairedTripleWeight c₁ c₂
  have hpoint :
      (fun x : BourgainPhaseSpace =>
        ‖bourgainGenericFourCurveExactLocalSum H
            (bourgainNormalizedCubicRemainder q)
            (bourgainNormalizedQuarticRemainder q)
            D a c₁ (E.symm (bourgainCoordinateScale X x))‖ ^
              (6 : ℕ) *
          ‖bourgainGenericFourCurveExactLocalSum H
            (bourgainNormalizedCubicRemainder q)
            (bourgainNormalizedQuarticRemainder q)
            D b c₂ (E.symm (bourgainCoordinateScale X x))‖ ^
              (6 : ℕ)) =
        fun x =>
          ‖bourgainWeightedFourierSum X
            (bourgainPairedTripleCloud p r) w x‖ ^ (2 : ℕ) := by
    funext x
    symm
    exact
      norm_sq_bourgainWeightedFourierSum_pairedTripleCloud_eq_genericExact
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q)
        hscale hunit X c₁ c₂ x
  calc
    (∫ x in bourgainFourCube,
        ‖bourgainGenericFourCurveExactLocalSum H
            (bourgainNormalizedCubicRemainder q)
            (bourgainNormalizedQuarticRemainder q)
            D a c₁ (E.symm (bourgainCoordinateScale X x))‖ ^
              (6 : ℕ) *
          ‖bourgainGenericFourCurveExactLocalSum H
            (bourgainNormalizedCubicRemainder q)
            (bourgainNormalizedQuarticRemainder q)
            D b c₂ (E.symm (bourgainCoordinateScale X x))‖ ^
              (6 : ℕ)) =
      ∫ x in bourgainFourCube,
        ‖bourgainWeightedFourierSum X
          (bourgainPairedTripleCloud p r) w x‖ ^ (2 : ℕ) := by
      rw [hpoint]
    _ ≤ Real.exp (4 * Real.pi) *
        (∫ x : BourgainPhaseSpace,
          bourgainRealGaussianL2Integrand X
            (bourgainPairedTripleCloud p r) w x) :=
      integral_bourgainFourCube_l2_le_gaussian
        X (bourgainPairedTripleCloud p r) w
    _ ≤ Real.exp (4 * Real.pi) *
        (C₀ * (H : ℝ) ^ ε *
          (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
          (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) := by
      gcongr
      exact hgaussian H hH hq hq1 hD hHD
        ha0 ha1 hb0 hb1 hab hsmall c₁ c₂
    _ = (Real.exp (4 * Real.pi) * C₀) * (H : ℝ) ^ ε *
          (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
          (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
      ring

/-- Convert a nonnegative continuous four-cube integral bound to `ENNReal`. -/
theorem setLIntegral_fourCube_ofReal_le_of_integral_le
    (F : BourgainPhaseSpace → ℝ) (hF : Continuous F)
    (hF0 : ∀ x, 0 ≤ F x) {B : ℝ}
    (hbound : (∫ x in bourgainFourCube, F x) ≤ B) :
    (∫⁻ x in bourgainFourCube, ENNReal.ofReal (F x)) ≤
      ENNReal.ofReal B := by
  have hcube :
      bourgainFourCube =
        Metric.closedBall (0 : BourgainPhaseSpace) 1 := by
    ext x
    simp [bourgainFourCube, Metric.mem_closedBall, dist_zero_right]
  have hFint : IntegrableOn F bourgainFourCube := by
    rw [hcube]
    exact hF.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : BourgainPhaseSpace) 1)
  have hFnonneg :
      ∀ᵐ x ∂volume.restrict bourgainFourCube, 0 ≤ F x :=
    Filter.Eventually.of_forall hF0
  calc
    (∫⁻ x in bourgainFourCube, ENNReal.ofReal (F x)) =
        ENNReal.ofReal (∫ x in bourgainFourCube, F x) :=
      (ofReal_integral_eq_lintegral_ofReal hFint hFnonneg).symm
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hbound

/-- `ENNReal` form of normalized exact-curve four-cube decoupling. -/
theorem setLIntegral_bourgainNormalizedExactLocalSum_fourCube_subpower
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
      let hunit :=
        isUnit_bourgainGenericPhaseCoordinateMatrix_normalized
          hq hq1 haIcc hbIcc hab
      let hscale : (H : ℝ) / D ≠ 0 :=
        div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
      let E :=
        bourgainGenericScaledPhaseContinuousLinearEquiv
          (bourgainNormalizedCubicRemainder q)
          (bourgainNormalizedQuarticRemainder q) hscale hunit
      let X := bourgainIndependentParabolaNaturalScale H
      ∀ (c₁ c₂ : Fin H → ℂ),
        (∫⁻ x in bourgainFourCube,
          ENNReal.ofReal
            (‖bourgainGenericFourCurveExactLocalSum H
                (bourgainNormalizedCubicRemainder q)
                (bourgainNormalizedQuarticRemainder q)
                D a c₁ (E.symm (bourgainCoordinateScale X x))‖ ^
                  (6 : ℕ) *
              ‖bourgainGenericFourCurveExactLocalSum H
                (bourgainNormalizedCubicRemainder q)
                (bourgainNormalizedQuarticRemainder q)
                D b c₂ (E.symm (bourgainCoordinateScale X x))‖ ^
                  (6 : ℕ))) ≤
          ENNReal.ofReal
            (C * (H : ℝ) ^ ε *
              (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
              (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) := by
  obtain ⟨C, hC, hreal⟩ :=
    integral_bourgainNormalizedExactLocalSum_fourCube_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H hH q D a b hq hq1 hD hHD ha0 ha1 hb0 hb1 hab hsmall
  dsimp only
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
      (bourgainNormalizedCubicRemainder q)
      (bourgainNormalizedQuarticRemainder q) hscale hunit
  let X := bourgainIndependentParabolaNaturalScale H
  intro c₁ c₂
  let F : BourgainPhaseSpace → ℝ := fun x =>
    ‖bourgainGenericFourCurveExactLocalSum H
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q)
        D a c₁ (E.symm (bourgainCoordinateScale X x))‖ ^ (6 : ℕ) *
      ‖bourgainGenericFourCurveExactLocalSum H
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q)
        D b c₂ (E.symm (bourgainCoordinateScale X x))‖ ^ (6 : ℕ)
  have hF : Continuous F := by
    unfold F bourgainGenericFourCurveExactLocalSum
      bourgainGenericFourCurve bourgainUnitCharacter
      bourgainDot bourgainCoordinateScale
    fun_prop
  have hF0 : ∀ x, 0 ≤ F x := fun x => by
    dsimp [F]
    positivity
  apply setLIntegral_fourCube_ofReal_le_of_integral_le F hF hF0
  exact hreal H hH hq hq1 hD hHD
    ha0 ha1 hb0 hb1 hab hsmall c₁ c₂

end

end RHTower
