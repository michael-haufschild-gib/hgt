import Mathlib

/-!
# Algebraic value interface for the first corrected Brascamp--Lieb inequality

Popescu's one-dimensional refinement of Brascamp--Lieb iterates the Witten resolvent.  Its first
correction is available when `V'' > 0` and `1 + A((V'')⁻¹) > 0`, where

`A(E) = (2 E'' + 2 V' E' - (E')² / E + 4 E V'') / 4`.

This file isolates the pointwise algebra needed to verify that second positivity condition.  It
does not assert the analytic resolvent inequality: it converts the inverse-curvature jet into the
single denominator-free value

`3(V''')² + 8(V'')³ - 2 V'''' V'' - 2 V''' V'' V'`.

The interface is reusable for hypertranscendental source densities whose logarithmic derivatives
are known by constraints or value relations even when no finite evolution law exists.
-/

namespace HTGeometry

noncomputable section

/-- The scalar differential expression `A(E)` in the first Popescu correction.  The arguments are
the point values of `V'`, `V''`, `E`, `E'`, and `E''`, respectively. -/
def oneDimBrascampLiebCorrectionA
    (V₁ V₂ E E₁ E₂ : ℝ) : ℝ :=
  (2 * E₂ + 2 * V₁ * E₁ - E₁ ^ 2 / E + 4 * E * V₂) / 4

/-- First derivative jet of the inverse curvature `1 / V''`. -/
def inverseCurvatureFirstJet (V₂ V₃ : ℝ) : ℝ :=
  -V₃ / V₂ ^ 2

/-- Second derivative jet of the inverse curvature `1 / V''`. -/
def inverseCurvatureSecondJet (V₂ V₃ V₄ : ℝ) : ℝ :=
  2 * V₃ ^ 2 / V₂ ^ 3 - V₄ / V₂ ^ 2

/-- Denominator-free positivity value controlling the first corrected Brascamp--Lieb weight. -/
def oneDimBrascampLiebFirstCorrectionNumerator
    (V₁ V₂ V₃ V₄ : ℝ) : ℝ :=
  3 * V₃ ^ 2 + 8 * V₂ ^ 3 - 2 * V₄ * V₂ - 2 * V₃ * V₂ * V₁

/-- The inverse-curvature substitution turns `1 + A((V'')⁻¹)` into one rational value with the
Popescu numerator. -/
theorem one_add_oneDimBrascampLiebCorrectionA_inverseCurvature
    {V₁ V₂ V₃ V₄ : ℝ} (hV₂ : V₂ ≠ 0) :
    1 + oneDimBrascampLiebCorrectionA V₁ V₂ (1 / V₂)
        (inverseCurvatureFirstJet V₂ V₃)
        (inverseCurvatureSecondJet V₂ V₃ V₄) =
      oneDimBrascampLiebFirstCorrectionNumerator V₁ V₂ V₃ V₄ /
        (4 * V₂ ^ 3) := by
  unfold oneDimBrascampLiebCorrectionA inverseCurvatureFirstJet
    inverseCurvatureSecondJet oneDimBrascampLiebFirstCorrectionNumerator
  field_simp [hV₂]
  ring

/-- Popescu's second weight `V'' * (1 + A((V'')⁻¹))`. -/
def oneDimBrascampLiebSecondWeight
    (V₁ V₂ V₃ V₄ : ℝ) : ℝ :=
  V₂ *
    (1 + oneDimBrascampLiebCorrectionA V₁ V₂ (1 / V₂)
      (inverseCurvatureFirstJet V₂ V₃)
      (inverseCurvatureSecondJet V₂ V₃ V₄))

/-- Exact denominator-free form of the second iterated Witten weight. -/
theorem oneDimBrascampLiebSecondWeight_eq
    {V₁ V₂ V₃ V₄ : ℝ} (hV₂ : V₂ ≠ 0) :
    oneDimBrascampLiebSecondWeight V₁ V₂ V₃ V₄ =
      oneDimBrascampLiebFirstCorrectionNumerator V₁ V₂ V₃ V₄ /
        (4 * V₂ ^ 2) := by
  rw [oneDimBrascampLiebSecondWeight,
    one_add_oneDimBrascampLiebCorrectionA_inverseCurvature hV₂]
  field_simp [hV₂]

/-- For positive curvature, positivity of the analytic correction denominator is exactly
positivity of its denominator-free numerator. -/
theorem one_add_oneDimBrascampLiebCorrectionA_inverseCurvature_pos_iff
    {V₁ V₂ V₃ V₄ : ℝ} (hV₂ : 0 < V₂) :
    0 < 1 + oneDimBrascampLiebCorrectionA V₁ V₂ (1 / V₂)
        (inverseCurvatureFirstJet V₂ V₃)
        (inverseCurvatureSecondJet V₂ V₃ V₄) ↔
      0 < oneDimBrascampLiebFirstCorrectionNumerator V₁ V₂ V₃ V₄ := by
  rw [one_add_oneDimBrascampLiebCorrectionA_inverseCurvature hV₂.ne']
  have hden : 0 < 4 * V₂ ^ 3 := by positivity
  constructor
  · intro h
    have heq : oneDimBrascampLiebFirstCorrectionNumerator V₁ V₂ V₃ V₄ =
        (oneDimBrascampLiebFirstCorrectionNumerator V₁ V₂ V₃ V₄ /
          (4 * V₂ ^ 3)) * (4 * V₂ ^ 3) := by
      field_simp [hden.ne']
    rw [heq]
    positivity
  · intro h
    exact div_pos h hden

/-- The same positivity equivalence in the second-weight normalization used by the iterated
resolvent construction. -/
theorem oneDimBrascampLiebSecondWeight_pos_iff
    {V₁ V₂ V₃ V₄ : ℝ} (hV₂ : 0 < V₂) :
    0 < oneDimBrascampLiebSecondWeight V₁ V₂ V₃ V₄ ↔
      0 < oneDimBrascampLiebFirstCorrectionNumerator V₁ V₂ V₃ V₄ := by
  rw [oneDimBrascampLiebSecondWeight_eq hV₂.ne']
  have hden : 0 < 4 * V₂ ^ 2 := by positivity
  constructor
  · intro h
    have heq : oneDimBrascampLiebFirstCorrectionNumerator V₁ V₂ V₃ V₄ =
        (oneDimBrascampLiebFirstCorrectionNumerator V₁ V₂ V₃ V₄ /
          (4 * V₂ ^ 2)) * (4 * V₂ ^ 2) := by
      field_simp [hden.ne']
    rw [heq]
    positivity
  · intro h
    exact div_pos h hden

/-- Once the Popescu denominator is positive, the squared derivative value subtracted from the
ordinary Brascamp--Lieb bound is nonnegative. -/
theorem oneDimBrascampLiebCorrectionValue_nonneg
    (derivativeValue correctionDenominator : ℝ)
    (hden : 0 ≤ correctionDenominator) :
    0 ≤ derivativeValue ^ 2 / correctionDenominator := by
  exact div_nonneg (sq_nonneg _) hden

/-! ### Exact transfer to a quadratic-moment certificate -/

/-- A corrected quadratic Brascamp--Lieb value bound discharges the target moment inequality.
This is the algebraic consumer of the positive Popescu remainder: no uniform curvature floor is
needed once the variable-curvature value `J` and correction value `C` are retained. -/
theorem correctedQuadraticBrascampLiebCertificate
    {a₀ a₁ a₂ J C c : ℝ}
    (hvariance : a₀ * a₂ - a₁ ^ 2 ≤ 4 * a₀ * J - a₀ * C)
    (hcertificate :
      64 * c ^ 2 * a₀ * J - 16 * c ^ 2 * a₀ * C ≤
        (45 - 16 * c ^ 2) * a₁ ^ 2) :
    16 * c ^ 2 * a₀ * a₂ ≤ 45 * a₁ ^ 2 := by
  have hscale : 0 ≤ 16 * c ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hvariance hscale
  nlinarith

/-- Every uncorrected variable-curvature certificate implies the corrected certificate when the
Popescu value is nonnegative. -/
theorem correctedQuadraticCertificate_of_uncorrected
    {a₀ a₁ J C c : ℝ}
    (ha₀ : 0 ≤ a₀) (hC : 0 ≤ C)
    (huncorrected :
      64 * c ^ 2 * a₀ * J ≤ (45 - 16 * c ^ 2) * a₁ ^ 2) :
    64 * c ^ 2 * a₀ * J - 16 * c ^ 2 * a₀ * C ≤
      (45 - 16 * c ^ 2) * a₁ ^ 2 := by
  have hcorrection : 0 ≤ 16 * c ^ 2 * a₀ * C := by positivity
  linarith

/-- For positive mass and a nonzero scale, a strictly positive Popescu value gives a strict
improvement over the uncorrected left-hand side. -/
theorem correctedQuadraticCertificate_strictlyImproves
    {a₀ J C c : ℝ} (ha₀ : 0 < a₀) (hC : 0 < C) (hc : c ≠ 0) :
    64 * c ^ 2 * a₀ * J - 16 * c ^ 2 * a₀ * C <
      64 * c ^ 2 * a₀ * J := by
  have hcorrection : 0 < 16 * c ^ 2 * a₀ * C := by positivity
  linarith

end

end HTGeometry
