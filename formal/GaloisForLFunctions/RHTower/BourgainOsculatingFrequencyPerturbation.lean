/-
# Taylor perturbation of exact osculating frequencies

This module controls exact square-root frequencies after the scaled
osculating change of variables.  The control is multiplicative at the
frequency level: every transformed point lies in an explicit scaled
neighborhood of its independent-parabola model.  No coefficient `ℓ¹` error
appears.
-/
import GaloisForLFunctions.RHTower.BourgainOsculatingQuadraticFrequencies

namespace RHTower

noncomputable section

/-- Scalar quadratic Taylor remainder for the square-root curve phase, with
the third-derivative constant discharged explicitly. -/
theorem abs_bourgainSquareRootCurvePhase_sub_quadratic_le
    {a Δ s : ℝ} (ha : 0 < a) (hΔ : 0 < Δ)
    (hs0 : 0 ≤ s) (hsΔ : s ≤ Δ)
    (x : BourgainPhaseSpace) :
    |bourgainSquareRootCurvePhase x (a ^ (2 : ℕ) + s) -
        bourgainSquareRootQuadraticLocalPhase a x s| ≤
      (‖x‖ * bourgainSquareRootThirdDerivativeBound a) *
        Δ ^ (3 : ℕ) / 2 := by
  have hinterval : a ^ (2 : ℕ) ≤ a ^ (2 : ℕ) + Δ := by linarith
  have hsample :
      a ^ (2 : ℕ) + s ∈
        Set.Icc (a ^ (2 : ℕ)) (a ^ (2 : ℕ) + Δ) := by
    constructor <;> linarith
  have hcont :
      ContDiffOn ℝ 3 (bourgainSquareRootCurvePhase x)
        (Set.Icc (a ^ (2 : ℕ)) (a ^ (2 : ℕ) + Δ)) := by
    intro y hy
    have hypos : 0 < y := (sq_pos_of_pos ha).trans_le hy.1
    have hfun :
        bourgainSquareRootCurvePhase x =
          fun t : ℝ =>
            x 0 * t + x 1 * t ^ (2 : ℕ) +
              x 2 * t ^ (3 / 2 : ℝ) + x 3 * t ^ (1 / 2 : ℝ) := by
      funext t
      simp [bourgainSquareRootCurvePhase, bourgainDot,
        bourgainSquareRootCurve, Fin.sum_univ_four]
    rw [hfun]
    have hpow3 : ContDiffAt ℝ 3
        (fun t : ℝ => t ^ (3 / 2 : ℝ)) y :=
      Real.contDiffAt_rpow_const_of_ne hypos.ne'
    have hpow1 : ContDiffAt ℝ 3
        (fun t : ℝ => t ^ (1 / 2 : ℝ)) y :=
      Real.contDiffAt_rpow_const_of_ne hypos.ne'
    exact ((((contDiffAt_const.mul contDiffAt_id).add
        (contDiffAt_const.mul (contDiffAt_id.pow 2))).add
          (contDiffAt_const.mul hpow3)).add
            (contDiffAt_const.mul hpow1)).contDiffWithinAt
  have hrem :=
    bourgain_quadraticTaylorWithin_remainder_of_sub_le
      hinterval hcont hsample
      (show
        0 ≤ ‖x‖ * bourgainSquareRootThirdDerivativeBound a by
          unfold bourgainSquareRootThirdDerivativeBound
          positivity)
      (fun y hy =>
        norm_iteratedDerivWithin_bourgainSquareRootCurvePhase_three_le
          ha hΔ hy x)
      (show
        (a ^ (2 : ℕ) + s) - a ^ (2 : ℕ) ≤ Δ by linarith)
  rw [taylorWithinEval_bourgainSquareRootCurvePhase_two ha hΔ x] at hrem
  simpa [Real.norm_eq_abs] using hrem

/-- Uniform perturbation radius for both transformed curve pieces. -/
def bourgainOsculatingFrequencyPerturbationSize
    (X : BourgainPhaseSpace) (inverseNorm a b Δ : ℝ) : ℝ :=
  ‖X‖ * inverseNorm *
    max (bourgainSquareRootThirdDerivativeBound a)
      (bourgainSquareRootThirdDerivativeBound b) *
    Δ ^ (3 : ℕ) / 2

theorem bourgainOsculatingFrequencyPerturbationSize_nonneg
    (X : BourgainPhaseSpace) {inverseNorm a b Δ : ℝ}
    (hinv : 0 ≤ inverseNorm) (ha : 0 < a) (_hb : 0 < b)
    (hΔ : 0 ≤ Δ) :
    0 ≤ bourgainOsculatingFrequencyPerturbationSize
      X inverseNorm a b Δ := by
  unfold bourgainOsculatingFrequencyPerturbationSize
    bourgainSquareRootThirdDerivativeBound
  positivity

/-- Exact transformed left frequency differs from its independent-parabola
sample by the scalar Taylor remainder evaluated on one inverse basis vector. -/
theorem bourgainExactLeftOsculatingFrequency_sub_model
    {H : ℕ} (hH : 0 < H) {D a b : ℝ}
    (hD : 0 < D) (ha : 0 < a) (hab : a < b)
    (n : Fin H) (j : Fin 4) :
    bourgainExactLeftOsculatingFrequency
          (div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne')
          ha hab D n j -
        bourgainLeftParabolaSample (H : ℝ) n j =
      bourgainSquareRootCurvePhase
          ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
            (div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne')
            ha hab).symm (bourgainPhaseBasis j))
          (a ^ (2 : ℕ) + (bourgainIndex n : ℝ) / D) -
        bourgainSquareRootQuadraticLocalPhase a
          ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
            (div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne')
            ha hab).symm (bourgainPhaseBasis j))
          ((bourgainIndex n : ℝ) / D) := by
  rw [← bourgainDualPullback_quadraticLeft_eq
    hH hD ha hab n]
  unfold bourgainExactLeftOsculatingFrequency
    bourgainDualPullbackFrequency
  rw [bourgainDot_quadraticCurveModel_sub_base]
  unfold bourgainSquareRootQuadraticLocalPhase
    bourgainSquareRootCurvePhase bourgainDot
  simp only [Pi.sub_apply]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring
  rfl

/-- Right-hand analogue of the exact frequency/model identity. -/
theorem bourgainExactRightOsculatingFrequency_sub_model
    {H : ℕ} (hH : 0 < H) {D a b : ℝ}
    (hD : 0 < D) (ha : 0 < a) (hab : a < b)
    (n : Fin H) (j : Fin 4) :
    bourgainExactRightOsculatingFrequency
          (div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne')
          ha hab D n j -
        bourgainRightParabolaSample (H : ℝ) n j =
      bourgainSquareRootCurvePhase
          ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
            (div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne')
            ha hab).symm (bourgainPhaseBasis j))
          (b ^ (2 : ℕ) + (bourgainIndex n : ℝ) / D) -
        bourgainSquareRootQuadraticLocalPhase b
          ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
            (div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne')
            ha hab).symm (bourgainPhaseBasis j))
          ((bourgainIndex n : ℝ) / D) := by
  rw [← bourgainDualPullback_quadraticRight_eq
    hH hD ha hab n]
  unfold bourgainExactRightOsculatingFrequency
    bourgainDualPullbackFrequency
  rw [bourgainDot_quadraticCurveModel_sub_base]
  unfold bourgainSquareRootQuadraticLocalPhase
    bourgainSquareRootCurvePhase bourgainDot
  simp only [Pi.sub_apply]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring
  rfl

/-- Both exact transformed point families obey one explicit uniform scaled
frequency perturbation bound. -/
theorem bourgainExactOsculatingFrequencies_scaledPerturbation
    {H : ℕ} (hH : 0 < H) {D a b Δ : ℝ}
    (hD : 0 < D) (ha : 0 < a) (hab : a < b)
    (hΔ : 0 < Δ)
    (hsample : ∀ n : Fin H, (bourgainIndex n : ℝ) / D ≤ Δ)
    (X : BourgainPhaseSpace) :
    let hscale :
        (H : ℝ) / D ≠ 0 :=
      div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
    let inverseNorm : ℝ :=
      ‖((bourgainScaledOsculatingPhaseContinuousLinearEquiv
        hscale ha hab).symm :
          BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖
    let δ :=
      bourgainOsculatingFrequencyPerturbationSize
        X inverseNorm a b Δ
    (∀ (n : Fin H) (j : Fin 4),
      |X j *
        (bourgainExactLeftOsculatingFrequency
            hscale ha hab D n j -
          bourgainLeftParabolaSample (H : ℝ) n j)| ≤ δ) ∧
    (∀ (n : Fin H) (j : Fin 4),
      |X j *
        (bourgainExactRightOsculatingFrequency
            hscale ha hab D n j -
          bourgainRightParabolaSample (H : ℝ) n j)| ≤ δ) := by
  dsimp only
  let E :=
    bourgainScaledOsculatingPhaseContinuousLinearEquiv
      (div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne') ha hab
  let inverseNorm : ℝ :=
    ‖(E.symm : BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖
  have hinv0 : 0 ≤ inverseNorm := norm_nonneg _
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
    rw [bourgainExactLeftOsculatingFrequency_sub_model
      hH hD ha hab n j]
    have hs0 : 0 ≤ (bourgainIndex n : ℝ) / D := by positivity
    have hrem :=
      abs_bourgainSquareRootCurvePhase_sub_quadratic_le
        ha hΔ hs0 (hsample n) (E.symm (bourgainPhaseBasis j))
    have hthird :
        bourgainSquareRootThirdDerivativeBound a ≤
          max (bourgainSquareRootThirdDerivativeBound a)
            (bourgainSquareRootThirdDerivativeBound b) :=
      le_max_left _ _
    have hthird0 :
        0 ≤ bourgainSquareRootThirdDerivativeBound a := by
      unfold bourgainSquareRootThirdDerivativeBound
      positivity
    have hmax0 :
        0 ≤ max (bourgainSquareRootThirdDerivativeBound a)
          (bourgainSquareRootThirdDerivativeBound b) :=
      hthird0.trans hthird
    have hpow0 : 0 ≤ Δ ^ (3 : ℕ) := by positivity
    rw [abs_mul]
    unfold bourgainOsculatingFrequencyPerturbationSize
    calc
      |X j| *
          |bourgainSquareRootCurvePhase
                (E.symm (bourgainPhaseBasis j))
                (a ^ (2 : ℕ) + (bourgainIndex n : ℝ) / D) -
              bourgainSquareRootQuadraticLocalPhase a
                (E.symm (bourgainPhaseBasis j))
                ((bourgainIndex n : ℝ) / D)|
          ≤ |X j| *
              ((‖E.symm (bourgainPhaseBasis j)‖ *
                  bourgainSquareRootThirdDerivativeBound a) *
                Δ ^ (3 : ℕ) / 2) := by
            gcongr
      _ ≤ ‖X‖ *
            ((‖E.symm (bourgainPhaseBasis j)‖ *
                bourgainSquareRootThirdDerivativeBound a) *
              Δ ^ (3 : ℕ) / 2) := by
          exact mul_le_mul_of_nonneg_right
            (hXcoord j) (by positivity)
      _ ≤ ‖X‖ *
            ((inverseNorm *
                bourgainSquareRootThirdDerivativeBound a) *
              Δ ^ (3 : ℕ) / 2) := by
          gcongr
          exact hxbasis j
      _ ≤ ‖X‖ *
            ((inverseNorm *
                max (bourgainSquareRootThirdDerivativeBound a)
                  (bourgainSquareRootThirdDerivativeBound b)) *
              Δ ^ (3 : ℕ) / 2) := by
          gcongr
          exact hthird
      _ = ‖X‖ * inverseNorm *
            max (bourgainSquareRootThirdDerivativeBound a)
              (bourgainSquareRootThirdDerivativeBound b) *
            Δ ^ (3 : ℕ) / 2 := by
          ring
  · intro n j
    rw [bourgainExactRightOsculatingFrequency_sub_model
      hH hD ha hab n j]
    have hs0 : 0 ≤ (bourgainIndex n : ℝ) / D := by positivity
    have hrem :=
      abs_bourgainSquareRootCurvePhase_sub_quadratic_le
        (ha.trans hab) hΔ hs0 (hsample n)
        (E.symm (bourgainPhaseBasis j))
    have hthird :
        bourgainSquareRootThirdDerivativeBound b ≤
          max (bourgainSquareRootThirdDerivativeBound a)
            (bourgainSquareRootThirdDerivativeBound b) :=
      le_max_right _ _
    have hthird0 :
        0 ≤ bourgainSquareRootThirdDerivativeBound b := by
      unfold bourgainSquareRootThirdDerivativeBound
      positivity
    have hmax0 :
        0 ≤ max (bourgainSquareRootThirdDerivativeBound a)
          (bourgainSquareRootThirdDerivativeBound b) :=
      hthird0.trans hthird
    have hpow0 : 0 ≤ Δ ^ (3 : ℕ) := by positivity
    rw [abs_mul]
    unfold bourgainOsculatingFrequencyPerturbationSize
    calc
      |X j| *
          |bourgainSquareRootCurvePhase
                (E.symm (bourgainPhaseBasis j))
                (b ^ (2 : ℕ) + (bourgainIndex n : ℝ) / D) -
              bourgainSquareRootQuadraticLocalPhase b
                (E.symm (bourgainPhaseBasis j))
                ((bourgainIndex n : ℝ) / D)|
          ≤ |X j| *
              ((‖E.symm (bourgainPhaseBasis j)‖ *
                  bourgainSquareRootThirdDerivativeBound b) *
                Δ ^ (3 : ℕ) / 2) := by
            gcongr
      _ ≤ ‖X‖ *
            ((‖E.symm (bourgainPhaseBasis j)‖ *
                bourgainSquareRootThirdDerivativeBound b) *
              Δ ^ (3 : ℕ) / 2) := by
          exact mul_le_mul_of_nonneg_right
            (hXcoord j) (by positivity)
      _ ≤ ‖X‖ *
            ((inverseNorm *
                bourgainSquareRootThirdDerivativeBound b) *
              Δ ^ (3 : ℕ) / 2) := by
          gcongr
          exact hxbasis j
      _ ≤ ‖X‖ *
            ((inverseNorm *
                max (bourgainSquareRootThirdDerivativeBound a)
                  (bourgainSquareRootThirdDerivativeBound b)) *
              Δ ^ (3 : ℕ) / 2) := by
          gcongr
          exact hthird
      _ = ‖X‖ * inverseNorm *
            max (bourgainSquareRootThirdDerivativeBound a)
              (bourgainSquareRootThirdDerivativeBound b) *
            Δ ^ (3 : ℕ) / 2 := by
          ring

end

end RHTower
