/-
# Exact osculating decoupling on one physical period cell

This module combines the normalized exact-curve Gaussian estimate with both
linear changes of variables.  The resulting physical estimate has the sharp
period-cell factor `H⁶`, the exact osculating Jacobian, and no additive
Taylor-error term.
-/
import GaloisForLFunctions.RHTower.BourgainNaturalScaleCellTransfer

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Generic exact change of variables through the combined scaled
osculating-coordinate map. -/
theorem setLIntegral_bourgainOsculatingFundamentalCell_generic_eq
    (H : ℕ) {scale a b : ℝ}
    (hscale : scale ≠ 0) (ha : 0 < a) (hab : a < b)
    (f : BourgainPhaseSpace → ENNReal) (hf : Measurable f) :
    (∫⁻ x in bourgainOsculatingFundamentalCell H scale a b, f x) =
      ENNReal.ofReal
          |(scale ^ (6 : ℕ) *
            (3 * (b - a) ^ (4 : ℕ) /
              (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹| *
        ∫⁻ y in bourgainParabolaFundamentalCell H,
          f ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
            hscale ha hab).symm y) := by
  let M := bourgainScaledOsculatingPhaseMatrix scale a b
  let E :=
    bourgainScaledOsculatingPhaseContinuousLinearEquiv hscale ha hab
  let g : BourgainPhaseSpace → ENNReal := fun y => f (E.symm y)
  have hM : Measurable (Matrix.toLin' M) :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable
  have hg : Measurable g :=
    hf.comp E.symm.continuous.measurable
  have hcell := measurableSet_bourgainParabolaFundamentalCell H
  have hcoord (x : BourgainPhaseSpace) :
      Matrix.toLin' M x = E x := by
    rw [Matrix.toLin'_apply]
    exact
      (bourgainScaledOsculatingPhaseMatrix_mulVec scale a b x).trans
        (bourgainScaledOsculatingPhaseContinuousLinearEquiv_apply
          hscale ha hab x).symm
  have hset :
      bourgainOsculatingFundamentalCell H scale a b =
        (Matrix.toLin' M) ⁻¹'
          bourgainParabolaFundamentalCell H := by
    ext x
    simp only [bourgainOsculatingFundamentalCell, Set.mem_preimage]
    rw [hcoord]
    exact
      bourgainScaledOsculatingPhaseContinuousLinearEquiv_apply
        hscale ha hab x |>.symm ▸ Iff.rfl
  have hcomp :
      (fun x : BourgainPhaseSpace => g (Matrix.toLin' M x)) = f := by
    funext x
    dsimp [g]
    change f (E.symm (Matrix.toLin' M x)) = f x
    rw [hcoord, ContinuousLinearEquiv.symm_apply_apply]
  calc
    (∫⁻ x in bourgainOsculatingFundamentalCell H scale a b, f x) =
        ∫⁻ x in (Matrix.toLin' M) ⁻¹'
            bourgainParabolaFundamentalCell H,
          g (Matrix.toLin' M x) := by
            rw [hset, hcomp]
    _ = ∫⁻ y in bourgainParabolaFundamentalCell H, g y ∂
          Measure.map (Matrix.toLin' M) volume := by
            symm
            exact setLIntegral_map hcell hg hM
    _ = ∫⁻ y in bourgainParabolaFundamentalCell H, g y ∂
          (ENNReal.ofReal
              |(scale ^ (6 : ℕ) *
                (3 * (b - a) ^ (4 : ℕ) /
                  (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹| •
            volume) := by
              dsimp [M]
              rw [map_bourgainScaledOsculatingPhaseMatrix_volume
                hscale ha hab]
    _ = ENNReal.ofReal
          |(scale ^ (6 : ℕ) *
            (3 * (b - a) ^ (4 : ℕ) /
              (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹| *
        ∫⁻ y in bourgainParabolaFundamentalCell H, g y := by
          rw [setLIntegral_smul_measure]
          rfl
    _ = _ := by rfl

/-- Sharp exact-curve bilinear sixth moment on one pulled-back physical
period cell. -/
theorem setLIntegral_bourgainSquareRootExactLocalSum_fundamentalCell_gaussian
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (hH : 0 < H),
      ∀ {D a b : ℝ} (hD : 0 < D) (ha : 0 < a) (hab : a < b),
      let hscale : (H : ℝ) / D ≠ 0 :=
        div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
      let E :=
        bourgainScaledOsculatingPhaseContinuousLinearEquiv
          hscale ha hab
      let X := bourgainIndependentParabolaNaturalScale H
      let δ :=
        bourgainOsculatingFrequencyPerturbationSize X
          ‖(E.symm :
            BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖
          a b ((H : ℝ) / D)
      δ ≤ 1 / 24 →
      ∀ (c₁ c₂ : Fin H → ℂ),
        (∫⁻ x in bourgainOsculatingFundamentalCell
            H ((H : ℝ) / D) a b,
          ENNReal.ofReal
            (‖bourgainSquareRootExactLocalSum H D a c₁ x‖ ^ (6 : ℕ) *
              ‖bourgainSquareRootExactLocalSum H D b c₂ x‖ ^
                (6 : ℕ))) ≤
          ENNReal.ofReal
              |((((H : ℝ) / D) ^ (6 : ℕ)) *
                (3 * (b - a) ^ (4 : ℕ) /
                  (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹| *
            ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) *
            ENNReal.ofReal
              (C * (H : ℝ) ^ ε *
                (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
                (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) := by
  obtain ⟨C, hC, hcube⟩ :=
    setLIntegral_bourgainExactLocalSum_scaledOsculating_fourCube_subpower
      hε
  refine ⟨C, hC, ?_⟩
  intro H hH D a b hD ha hab
  dsimp only
  intro hsmall c₁ c₂
  let hscale : (H : ℝ) / D ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
  let E :=
    bourgainScaledOsculatingPhaseContinuousLinearEquiv hscale ha hab
  let X := bourgainIndependentParabolaNaturalScale H
  let F : BourgainPhaseSpace → ENNReal := fun x =>
    ENNReal.ofReal
      (‖bourgainSquareRootExactLocalSum H D a c₁ x‖ ^ (6 : ℕ) *
        ‖bourgainSquareRootExactLocalSum H D b c₂ x‖ ^ (6 : ℕ))
  let g : BourgainPhaseSpace → ENNReal := fun y => F (E.symm y)
  have hF : Measurable F := by
    unfold F bourgainSquareRootExactLocalSum
      bourgainSquareRootCurvePhase bourgainSquareRootCurve
      bourgainUnitCharacter bourgainDot
    fun_prop
  have hg : Measurable g :=
    hF.comp E.symm.continuous.measurable
  have hchange :=
    setLIntegral_bourgainOsculatingFundamentalCell_generic_eq
      H hscale ha hab F hF
  have hnatural :=
    setLIntegral_bourgainParabolaFundamentalCell_le_naturalScale_fourCube
      H hH g hg
  calc
    (∫⁻ x in bourgainOsculatingFundamentalCell
        H ((H : ℝ) / D) a b,
      ENNReal.ofReal
        (‖bourgainSquareRootExactLocalSum H D a c₁ x‖ ^ (6 : ℕ) *
          ‖bourgainSquareRootExactLocalSum H D b c₂ x‖ ^ (6 : ℕ))) =
      ENNReal.ofReal
          |((((H : ℝ) / D) ^ (6 : ℕ)) *
            (3 * (b - a) ^ (4 : ℕ) /
              (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹| *
        ∫⁻ y in bourgainParabolaFundamentalCell H, g y := by
          simpa [F, g, E] using hchange
    _ ≤ ENNReal.ofReal
          |((((H : ℝ) / D) ^ (6 : ℕ)) *
            (3 * (b - a) ^ (4 : ℕ) /
              (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹| *
        (ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) *
          ∫⁻ x in bourgainFourCube,
            g (bourgainCoordinateScale X x)) := by
              exact mul_le_mul_right hnatural _
    _ ≤ ENNReal.ofReal
          |((((H : ℝ) / D) ^ (6 : ℕ)) *
            (3 * (b - a) ^ (4 : ℕ) /
              (32 * a ^ (3 : ℕ) * b ^ (3 : ℕ))))⁻¹| *
        (ENNReal.ofReal ((H : ℝ) ^ (6 : ℕ)) *
          ENNReal.ofReal
            (C * (H : ℝ) ^ ε *
              (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
              (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ))) := by
                apply mul_le_mul_right
                apply mul_le_mul_right
                simpa [g, F, E, X] using
                  hcube H hH hD ha hab hsmall c₁ c₂
    _ = _ := by ring

end

end RHTower
