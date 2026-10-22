import GaloisForLFunctions.HTGeometry.PolynomialODE.JetRankThreeSeamRestriction

/-!
# Source-positive seam obstruction

Strict positivity of normalized source and reconstructed discriminant gap does not by itself force
rank-three reflected D1 positivity.  At the exact rational seam scale `R = 5/2`, source-positive
coordinates have `Q = 1/64` and reconstructed gap `25/4`, but universal seam D1 polynomial is
strictly negative.  Thus any successful physical-chamber proof must use additional orbit data.
-/

open Complex Real

namespace HTGeometry

noncomputable section

/-- Source-positive coordinates on universal modular seam with squared scale `X`. -/
def modularThetaSourcePositiveSeamState (X : ℝ) :
    ModularThetaSourcePositiveState → ℂ
  | .U => 0
  | .B => 0
  | .Q => ((X - 6) / 16 : ℝ)

/-- On seam, source-positive reconstruction returns squared modular scale exactly. -/
theorem eval_modularThetaSourcePositiveGap_seamState (X : ℝ) :
    MvPolynomial.eval (modularThetaSourcePositiveSeamState X)
      modularThetaSourcePositiveGap = X := by
  simp [modularThetaSourcePositiveSeamState, modularThetaSourcePositiveGap]
  ring

/-- Seam normalized source is positive exactly beyond sharp scale wall `X = 6`. -/
theorem modularThetaSourcePositiveSeamState_Q_pos_iff (X : ℝ) :
    0 < (modularThetaSourcePositiveSeamState X
      ModularThetaSourcePositiveState.Q).re ↔ 6 < X := by
  simp [modularThetaSourcePositiveSeamState]

/-- Rational source-positive seam state selected by `R = 5/2`. -/
def modularThetaSourcePositiveRationalSeamState :
    ModularThetaSourcePositiveState → ℂ :=
  modularThetaSourcePositiveSeamState (25 / 4)

/-- Source-positive chart evaluation at rational seam equals Lyapunov seam evaluation. -/
theorem eval_modularThetaSourcePositiveChartPullback_rationalSeam
    (P : ModularThetaLyapunovPolynomial) :
    MvPolynomial.eval modularThetaSourcePositiveRationalSeamState
        (modularThetaSourcePositiveChartPullback P) =
      MvPolynomial.eval (modularThetaLyapunovSeamState (5 / 2)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
      simp only [map_add]
      rw [hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, map_mul, hP,
        modularThetaSourcePositiveChartPullback_X]
      rw [map_mul]
      apply congrArg (fun z : ℂ =>
        MvPolynomial.eval (modularThetaLyapunovSeamState (5 / 2)) P * z)
      cases i <;>
        simp [modularThetaSourcePositiveChartCoordinate,
          modularThetaSourcePositiveGap,
          modularThetaSourcePositiveRationalSeamState,
          modularThetaSourcePositiveSeamState,
          modularThetaLyapunovSeamState]
      all_goals ring

/-- Rational seam state has positive normalized source. -/
theorem modularThetaSourcePositiveRationalSeamState_Q_pos :
    0 < (modularThetaSourcePositiveRationalSeamState
      ModularThetaSourcePositiveState.Q).re := by
  rw [modularThetaSourcePositiveRationalSeamState,
    modularThetaSourcePositiveSeamState_Q_pos_iff]
  norm_num

/-- Reconstructed discriminant gap at rational seam is exactly `(5/2)² = 25/4`. -/
theorem eval_modularThetaSourcePositiveGap_rationalSeam :
    MvPolynomial.eval modularThetaSourcePositiveRationalSeamState
      modularThetaSourcePositiveGap = 25 / 4 := by
  simpa [modularThetaSourcePositiveRationalSeamState] using
    eval_modularThetaSourcePositiveGap_seamState (25 / 4)

/-- Universal rank-three reflected seam polynomial is strictly negative at gap `25/4`. -/
theorem modularThetaReflectedEighthSeamPolynomial_twentyFiveFourths_re_neg :
    (modularThetaReflectedEighthSeamPolynomial (25 / 4)).re < 0 := by
  norm_num [modularThetaReflectedEighthSeamPolynomial]

/-- Source-positive D1 itself equals exact seam polynomial at rational obstruction state. -/
theorem eval_modularThetaSourcePositiveReflectedEighthPolynomial_rationalSeam :
    MvPolynomial.eval modularThetaSourcePositiveRationalSeamState
        modularThetaSourcePositiveReflectedEighthPolynomial =
      modularThetaReflectedEighthSeamPolynomial (25 / 4) := by
  rw [← modularThetaSourcePositiveChart_reflectedEighthPolynomial,
    eval_modularThetaSourcePositiveChartPullback_rationalSeam,
    eval_modularThetaLyapunovReflectedEighthPolynomial_seam]
  norm_num

/-- Literal source-positive D1 polynomial is negative at rational obstruction state. -/
theorem eval_modularThetaSourcePositiveReflectedEighthPolynomial_rationalSeam_re_neg :
    (MvPolynomial.eval modularThetaSourcePositiveRationalSeamState
      modularThetaSourcePositiveReflectedEighthPolynomial).re < 0 := by
  rw [eval_modularThetaSourcePositiveReflectedEighthPolynomial_rationalSeam]
  exact modularThetaReflectedEighthSeamPolynomial_twentyFiveFourths_re_neg

/-- Exact no-go: positive source and positive reconstructed gap coexist with negative literal D1. -/
theorem modularThetaSourcePositiveGap_not_sufficient_for_seamD1 :
    0 < (modularThetaSourcePositiveRationalSeamState
      ModularThetaSourcePositiveState.Q).re ∧
      0 < (MvPolynomial.eval modularThetaSourcePositiveRationalSeamState
        modularThetaSourcePositiveGap).re ∧
      (MvPolynomial.eval modularThetaSourcePositiveRationalSeamState
        modularThetaSourcePositiveReflectedEighthPolynomial).re < 0 := by
  rw [eval_modularThetaSourcePositiveGap_rationalSeam]
  exact ⟨modularThetaSourcePositiveRationalSeamState_Q_pos, by norm_num,
    eval_modularThetaSourcePositiveReflectedEighthPolynomial_rationalSeam_re_neg⟩

end

end HTGeometry
