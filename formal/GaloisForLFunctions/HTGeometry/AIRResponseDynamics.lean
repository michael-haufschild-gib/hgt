import GaloisForLFunctions.HTGeometry.AIRResponseCore
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Constructed mixed response cells and neutral two-bloc drift

Araújo, arXiv:2609.05560, Corollary 4 and Proposition 5. A trigonometric parameterization
constructs a strict mixed response cell for every real parameter. The actual AIR force then
has the exact reversal threshold two sevenths. The separate reduced two-bloc vector field
has a closed neutral translating solution, with all normalization and critical-gain algebra
proved rather than assumed. No assertion continues an AIR trajectory beyond its cell.
-/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- An entire real parameter family lying strictly inside the mixed-response wedge. -/
def mixedResponseHalfGap (s : ℝ) : ℝ := 1 / 2 + Real.sin s / 40

theorem mixedResponseHalfGap_bounds (s : ℝ) :
    19 / 40 ≤ mixedResponseHalfGap s ∧ mixedResponseHalfGap s ≤ 21 / 40 := by
  have h₁ := Real.neg_one_le_sin s
  have h₂ := Real.sin_le_one s
  unfold mixedResponseHalfGap
  constructor <;> linarith

/-- In the constructed cell, mean collapse is attractive to both blocs. -/
theorem airResponse_mixed_mean_collapse (s : ℝ) :
    airResponse (3 / 5) (9 / 10) (2 / 5) (-mixedResponseHalfGap s) = -mixedResponseHalfGap s := by
  have hy := mixedResponseHalfGap_bounds s
  have hp : 0 < mixedResponseHalfGap s := by linarith
  have ha : |-mixedResponseHalfGap s| < (3 / 5 : ℝ) := by
    rw [abs_neg, abs_of_pos hp]
    linarith
  unfold airResponse
  rw [if_pos ha]

/-- In the same cell, direct exposure to the opposite bloc is repulsive. -/
theorem airResponse_mixed_opposite (s : ℝ) :
    airResponse (3 / 5) (9 / 10) (2 / 5) (-2 * mixedResponseHalfGap s) =
      (4 / 5) * mixedResponseHalfGap s := by
  have hy := mixedResponseHalfGap_bounds s
  have hp : -2 * mixedResponseHalfGap s < 0 := by linarith
  have ha : ¬ |-2 * mixedResponseHalfGap s| < (3 / 5 : ℝ) := by
    rw [abs_of_neg hp]
    linarith
  have hr : ¬ |-2 * mixedResponseHalfGap s| < (9 / 10 : ℝ) := by
    rw [abs_of_neg hp]
    linarith
  unfold airResponse
  rw [if_neg ha, if_neg hr]
  ring

/-- The actual AIR velocity of the positive bloc under mean collapse. -/
def mixedResponseVelocity (s lam : ℝ) : ℝ :=
  (1 - lam) / 2 * airResponse (3 / 5) (9 / 10) (2 / 5) (-2 * mixedResponseHalfGap s) +
    lam * airResponse (3 / 5) (9 / 10) (2 / 5) (-mixedResponseHalfGap s)

/-- Exact reversal law for the actual response, with the cell conditions discharged. -/
theorem mixedResponseVelocity_eq (s lam : ℝ) :
    mixedResponseVelocity s lam = (2 - 7 * lam) / 5 * mixedResponseHalfGap s := by
  rw [mixedResponseVelocity, airResponse_mixed_opposite, airResponse_mixed_mean_collapse]
  ring

theorem mixedResponseVelocity_positive_iff (s lam : ℝ) :
    0 < mixedResponseVelocity s lam ↔ lam < 2 / 7 := by
  rw [mixedResponseVelocity_eq]
  have hy := mixedResponseHalfGap_bounds s
  constructor <;> intro h <;> nlinarith

theorem mixedResponseVelocity_zero_iff (s lam : ℝ) :
    mixedResponseVelocity s lam = 0 ↔ lam = 2 / 7 := by
  rw [mixedResponseVelocity_eq]
  have hy := mixedResponseHalfGap_bounds s
  constructor <;> intro h <;> nlinarith

theorem mixedResponseVelocity_negative_iff (s lam : ℝ) :
    mixedResponseVelocity s lam < 0 ↔ 2 / 7 < lam := by
  rw [mixedResponseVelocity_eq]
  have hy := mixedResponseHalfGap_bounds s
  constructor <;> intro h <;> nlinarith

/-- Positive-bloc component of the exact reduced mixed-cell vector field. -/
def reducedBlocPlus (eta lam q qhat gap : ℝ) : ℝ :=
  (1 - lam) * (1 - q) * eta * gap - lam * (1 - qhat) * gap

/-- Negative-bloc component of the same reduced vector field. -/
def reducedBlocMinus (eta lam q qhat gap : ℝ) : ℝ :=
  -(1 - lam) * q * eta * gap + lam * qhat * gap

/-- Both true and represented prevalence cancel from the gap equation. -/
theorem reducedBloc_gap (eta lam q qhat gap : ℝ) :
    reducedBlocPlus eta lam q qhat gap - reducedBlocMinus eta lam q qhat gap =
      ((1 - lam) * eta - lam) * gap := by
  unfold reducedBlocPlus reducedBlocMinus
  ring

/-- Only prevalence error drives the true population mean. -/
theorem reducedBloc_mean_drift (eta lam q qhat gap : ℝ) :
    q * reducedBlocPlus eta lam q qhat gap + (1 - q) * reducedBlocMinus eta lam q qhat gap =
      lam * (qhat - q) * gap := by
  unfold reducedBlocPlus reducedBlocMinus
  ring

/-- A strictly positive repulsion gain and its exact neutral mediation weight. -/
def responseNeutralGain (r : ℝ) : ℝ := (r ^ 2 + 1) / (r ^ 2 + 2)

theorem responseNeutralGain_range (r : ℝ) : 0 < responseNeutralGain r ∧ responseNeutralGain r < 1 := by
  have hd : 0 < r ^ 2 + 2 := by positivity
  unfold responseNeutralGain
  constructor
  · positivity
  · rw [div_lt_one hd]
    linarith

/-- At the constructed critical gain, both blocs translate at the same exact velocity. -/
theorem reducedBloc_neutral_velocity (r q qhat gap : ℝ) :
    reducedBlocPlus (r ^ 2 + 1) (responseNeutralGain r) q qhat gap =
      responseNeutralGain r * (qhat - q) * gap ∧
    reducedBlocMinus (r ^ 2 + 1) (responseNeutralGain r) q qhat gap =
      responseNeutralGain r * (qhat - q) * gap := by
  have hd : r ^ 2 + 2 ≠ 0 := by positivity
  unfold reducedBlocPlus reducedBlocMinus responseNeutralGain
  constructor <;> field_simp <;> ring

/-- The exact neutral solution has linear mean drift and a fixed bloc separation. -/
def responseNeutralPlus (r q qhat gap m₀ t : ℝ) : ℝ :=
  m₀ + responseNeutralGain r * (qhat - q) * gap * t + (1 - q) * gap

def responseNeutralMinus (r q qhat gap m₀ t : ℝ) : ℝ :=
  m₀ + responseNeutralGain r * (qhat - q) * gap * t - q * gap

theorem responseNeutral_gap_constant (r q qhat gap m₀ t : ℝ) :
    responseNeutralPlus r q qhat gap m₀ t - responseNeutralMinus r q qhat gap m₀ t = gap := by
  unfold responseNeutralPlus responseNeutralMinus
  ring

theorem responseNeutral_mean (r q qhat gap m₀ t : ℝ) :
    q * responseNeutralPlus r q qhat gap m₀ t +
      (1 - q) * responseNeutralMinus r q qhat gap m₀ t =
        m₀ + responseNeutralGain r * (qhat - q) * gap * t := by
  unfold responseNeutralPlus responseNeutralMinus
  ring

/-- The positive component solves the neutral reduced ODE at every time. -/
theorem responseNeutralPlus_solves (r q qhat gap m₀ t : ℝ) :
    HasDerivAt (responseNeutralPlus r q qhat gap m₀)
      (reducedBlocPlus (r ^ 2 + 1) (responseNeutralGain r) q qhat gap) t := by
  rw [(reducedBloc_neutral_velocity r q qhat gap).1]
  unfold responseNeutralPlus
  simpa only [id_eq, mul_one] using
    (((hasDerivAt_id t).const_mul (responseNeutralGain r * (qhat - q) * gap)).const_add m₀).add_const ((1 - q) * gap)

/-- The negative component solves the same neutral reduced ODE. -/
theorem responseNeutralMinus_solves (r q qhat gap m₀ t : ℝ) :
    HasDerivAt (responseNeutralMinus r q qhat gap m₀)
      (reducedBlocMinus (r ^ 2 + 1) (responseNeutralGain r) q qhat gap) t := by
  rw [(reducedBloc_neutral_velocity r q qhat gap).2]
  unfold responseNeutralMinus
  simpa only [id_eq, mul_one] using
    (((hasDerivAt_id t).const_mul (responseNeutralGain r * (qhat - q) * gap)).const_add m₀).sub_const (q * gap)

end
end GaloisForLFunctions.HTGeometry
