/-
# Generic frequency perturbation from quadratic Taylor control

This module converts a norm bound on a four-curve's quadratic remainder into
the coordinatewise scaled frequency perturbation consumed by
`BourgainAbstractGaussianDecoupling`.  The only geometric cost is the inverse
norm of the scaled two-base jet map.
-/
import GaloisForLFunctions.RHTower.BourgainGenericOsculatingCoordinates
import GaloisForLFunctions.RHTower.BourgainAbstractGaussianDecoupling

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Sup-norm Cauchy bound for the four-coordinate dot product. -/
theorem abs_bourgainDot_le_four_mul_norm_mul_norm
    (x u : BourgainPhaseSpace) :
    |bourgainDot x u| ≤ 4 * ‖x‖ * ‖u‖ := by
  have hcoord (j : Fin 4) :
      |x j * u j| ≤ ‖x‖ * ‖u‖ := by
    rw [abs_mul]
    exact mul_le_mul
      (by simpa [Real.norm_eq_abs] using
        norm_apply_le_norm_bourgainPhaseSpace x j)
      (by simpa [Real.norm_eq_abs] using
        norm_apply_le_norm_bourgainPhaseSpace u j)
      (abs_nonneg _) (norm_nonneg _)
  calc
    |bourgainDot x u| =
        |∑ j : Fin 4, x j * u j| := by rfl
    _ ≤ ∑ j : Fin 4, |x j * u j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 4, ‖x‖ * ‖u‖ :=
      Finset.sum_le_sum fun j _ => hcoord j
    _ = 4 * ‖x‖ * ‖u‖ := by simp; ring

theorem bourgainDot_sub_right
    (x u v : BourgainPhaseSpace) :
    bourgainDot x (u - v) =
      bourgainDot x u - bourgainDot x v := by
  unfold bourgainDot
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- Exact transformed left frequency minus its quadratic parabola model. -/
theorem bourgainGenericExactLeftFrequency_sub_model
    {H : ℕ} (hH : 0 < H) (φ₃ φ₄ : ℝ → ℝ)
    {D a b : ℝ} (hD : 0 < D)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b))
    (n : Fin H) (j : Fin 4) :
    let hscale : (H : ℝ) / D ≠ 0 :=
      div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
    bourgainGenericExactLeftFrequency
          φ₃ φ₄ hscale hunit D n j -
        bourgainLeftParabolaSample (H : ℝ) n j =
      bourgainDot
        ((bourgainGenericScaledPhaseContinuousLinearEquiv
          φ₃ φ₄ hscale hunit).symm (bourgainPhaseBasis j))
        (bourgainGenericFourCurve φ₃ φ₄
            (a + (bourgainIndex n : ℝ) / D) -
          bourgainGenericFourCurveQuadraticModel φ₃ φ₄ a
            ((bourgainIndex n : ℝ) / D)) := by
  dsimp only
  let hscale : (H : ℝ) / D ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
  let E :=
    bourgainGenericScaledPhaseContinuousLinearEquiv
      φ₃ φ₄ hscale hunit
  have hmodel :=
    congrFun
      (bourgainGenericDualPullback_quadraticLeft_eq
        hH φ₃ φ₄ hD rfl hscale hunit n) j
  unfold bourgainGenericExactLeftFrequency
    bourgainDualPullbackFrequency at hmodel ⊢
  rw [← hmodel]
  rw [← bourgainDot_sub_right]
  congr 1
  abel

/-- Right-hand analogue of the exact frequency/model identity. -/
theorem bourgainGenericExactRightFrequency_sub_model
    {H : ℕ} (hH : 0 < H) (φ₃ φ₄ : ℝ → ℝ)
    {D a b : ℝ} (hD : 0 < D)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b))
    (n : Fin H) (j : Fin 4) :
    let hscale : (H : ℝ) / D ≠ 0 :=
      div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
    bourgainGenericExactRightFrequency
          φ₃ φ₄ hscale hunit D n j -
        bourgainRightParabolaSample (H : ℝ) n j =
      bourgainDot
        ((bourgainGenericScaledPhaseContinuousLinearEquiv
          φ₃ φ₄ hscale hunit).symm (bourgainPhaseBasis j))
        (bourgainGenericFourCurve φ₃ φ₄
            (b + (bourgainIndex n : ℝ) / D) -
          bourgainGenericFourCurveQuadraticModel φ₃ φ₄ b
            ((bourgainIndex n : ℝ) / D)) := by
  dsimp only
  let hscale : (H : ℝ) / D ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
  have hmodel :=
    congrFun
      (bourgainGenericDualPullback_quadraticRight_eq
        hH φ₃ φ₄ hD rfl hscale hunit n) j
  unfold bourgainGenericExactRightFrequency
    bourgainDualPullbackFrequency at hmodel ⊢
  rw [← hmodel]
  rw [← bourgainDot_sub_right]
  congr 1
  abel

/-- Uniform scaled frequency perturbation radius from a vector remainder
bound `ρ`. -/
def bourgainGenericFrequencyPerturbationSize
    (X : BourgainPhaseSpace) (inverseNorm ρ : ℝ) : ℝ :=
  4 * ‖X‖ * inverseNorm * ρ

theorem bourgainGenericFrequencyPerturbationSize_nonneg
    (X : BourgainPhaseSpace) {inverseNorm ρ : ℝ}
    (hinv : 0 ≤ inverseNorm) (hρ : 0 ≤ ρ) :
    0 ≤ bourgainGenericFrequencyPerturbationSize X inverseNorm ρ := by
  unfold bourgainGenericFrequencyPerturbationSize
  positivity

/-- Both exact generic point families obey one uniform scaled perturbation
bound whenever their vector Taylor remainders are bounded by `ρ`. -/
theorem bourgainGenericExactFrequencies_scaledPerturbation
    {H : ℕ} (hH : 0 < H) (φ₃ φ₄ : ℝ → ℝ)
    {D a b ρ : ℝ} (hD : 0 < D) (hρ : 0 ≤ ρ)
    (hunit : IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b))
    (hleft :
      ∀ n : Fin H,
        ‖bourgainGenericFourCurve φ₃ φ₄
              (a + (bourgainIndex n : ℝ) / D) -
            bourgainGenericFourCurveQuadraticModel φ₃ φ₄ a
              ((bourgainIndex n : ℝ) / D)‖ ≤ ρ)
    (hright :
      ∀ n : Fin H,
        ‖bourgainGenericFourCurve φ₃ φ₄
              (b + (bourgainIndex n : ℝ) / D) -
            bourgainGenericFourCurveQuadraticModel φ₃ φ₄ b
              ((bourgainIndex n : ℝ) / D)‖ ≤ ρ)
    (X : BourgainPhaseSpace) :
    let hscale : (H : ℝ) / D ≠ 0 :=
      div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
    let E :=
      bourgainGenericScaledPhaseContinuousLinearEquiv
        φ₃ φ₄ hscale hunit
    let δ :=
      bourgainGenericFrequencyPerturbationSize X
        ‖(E.symm : BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ ρ
    (∀ (n : Fin H) (j : Fin 4),
      |X j *
        (bourgainGenericExactLeftFrequency
            φ₃ φ₄ hscale hunit D n j -
          bourgainLeftParabolaSample (H : ℝ) n j)| ≤ δ) ∧
    (∀ (n : Fin H) (j : Fin 4),
      |X j *
        (bourgainGenericExactRightFrequency
            φ₃ φ₄ hscale hunit D n j -
          bourgainRightParabolaSample (H : ℝ) n j)| ≤ δ) := by
  dsimp only
  let hscale : (H : ℝ) / D ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
  let E :=
    bourgainGenericScaledPhaseContinuousLinearEquiv
      φ₃ φ₄ hscale hunit
  let inverseNorm :=
    ‖(E.symm : BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖
  have hXcoord (j : Fin 4) : |X j| ≤ ‖X‖ := by
    simpa [Real.norm_eq_abs] using
      norm_apply_le_norm_bourgainPhaseSpace X j
  have hxbasis (j : Fin 4) :
      ‖E.symm (bourgainPhaseBasis j)‖ ≤ inverseNorm := by
    calc
      ‖E.symm (bourgainPhaseBasis j)‖
          ≤ inverseNorm * ‖bourgainPhaseBasis j‖ :=
        (E.symm :
          BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace).le_opNorm _
      _ = inverseNorm := by simp
  constructor
  · intro n j
    rw [bourgainGenericExactLeftFrequency_sub_model
      hH φ₃ φ₄ hD hunit n j]
    rw [abs_mul]
    unfold bourgainGenericFrequencyPerturbationSize
    calc
      |X j| *
          |bourgainDot
            (E.symm (bourgainPhaseBasis j))
            (bourgainGenericFourCurve φ₃ φ₄
                (a + (bourgainIndex n : ℝ) / D) -
              bourgainGenericFourCurveQuadraticModel φ₃ φ₄ a
                ((bourgainIndex n : ℝ) / D))|
          ≤ ‖X‖ *
              (4 * ‖E.symm (bourgainPhaseBasis j)‖ *
                ‖bourgainGenericFourCurve φ₃ φ₄
                    (a + (bourgainIndex n : ℝ) / D) -
                  bourgainGenericFourCurveQuadraticModel φ₃ φ₄ a
                    ((bourgainIndex n : ℝ) / D)‖) := by
            gcongr
            exact hXcoord j
            exact abs_bourgainDot_le_four_mul_norm_mul_norm _ _
      _ ≤ ‖X‖ * (4 * inverseNorm * ρ) := by
        gcongr
        exact hxbasis j
        exact hleft n
      _ = 4 * ‖X‖ * inverseNorm * ρ := by ring
  · intro n j
    rw [bourgainGenericExactRightFrequency_sub_model
      hH φ₃ φ₄ hD hunit n j]
    rw [abs_mul]
    unfold bourgainGenericFrequencyPerturbationSize
    calc
      |X j| *
          |bourgainDot
            (E.symm (bourgainPhaseBasis j))
            (bourgainGenericFourCurve φ₃ φ₄
                (b + (bourgainIndex n : ℝ) / D) -
              bourgainGenericFourCurveQuadraticModel φ₃ φ₄ b
                ((bourgainIndex n : ℝ) / D))|
          ≤ ‖X‖ *
              (4 * ‖E.symm (bourgainPhaseBasis j)‖ *
                ‖bourgainGenericFourCurve φ₃ φ₄
                    (b + (bourgainIndex n : ℝ) / D) -
                  bourgainGenericFourCurveQuadraticModel φ₃ φ₄ b
                    ((bourgainIndex n : ℝ) / D)‖) := by
            gcongr
            exact hXcoord j
            exact abs_bourgainDot_le_four_mul_norm_mul_norm _ _
      _ ≤ ‖X‖ * (4 * inverseNorm * ρ) := by
        gcongr
        exact hxbasis j
        exact hright n
      _ = 4 * ‖X‖ * inverseNorm * ρ := by ring

end

end RHTower
