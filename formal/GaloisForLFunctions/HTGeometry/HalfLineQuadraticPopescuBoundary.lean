import GaloisForLFunctions.HTGeometry.OneDimBrascampLiebCorrection

/-!
# Half-line boundary value of the quadratic Popescu observable

For the quadratic test `f(x) = x²`, the first inverse-curvature observable in Popescu's
Brascamp--Lieb refinement is

`(V'')⁻¹ f' = 2x / V''`.

On a half-line this observable has zero boundary trace independently of the potential.  Its
derivative is the static jet value

`2 (V'' - x V''') / (V'')²`.

The corresponding correction density has the denominator-free form

`16 (V'' - x V''')² / (V'' N_V)`,

where `N_V` is the first Popescu numerator.  Thus positive curvature and `N_V > 0` make the
correction nonnegative, while it is strictly positive exactly away from the single value relation
`V'' = x V'''`.  At the half-line endpoint it is automatically strict.

These are pointwise and boundary statements.  The analytic resolvent inequality and the
integrability of the correction density remain separate inputs.
-/

namespace HTGeometry

noncomputable section

/-- The inverse-curvature observable `(V'')⁻¹ f'` for the quadratic test `f(x)=x²`. -/
def oneDimQuadraticInverseCurvatureObservable
    (curvature : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * x / curvature x

/-- Pointwise derivative value of the quadratic inverse-curvature observable. -/
def oneDimQuadraticInverseCurvatureScore
    (x V₂ V₃ : ℝ) : ℝ :=
  2 * (V₂ - x * V₃) / V₂ ^ 2

/-- Differentiating `2x / V''` uses only the curvature value and its first jet. -/
theorem hasDerivAt_oneDimQuadraticInverseCurvatureObservable
    {curvature curvature' : ℝ → ℝ} {x : ℝ}
    (hcurvature : HasDerivAt curvature (curvature' x) x)
    (hcurvature_ne : curvature x ≠ 0) :
    HasDerivAt (oneDimQuadraticInverseCurvatureObservable curvature)
      (oneDimQuadraticInverseCurvatureScore x (curvature x) (curvature' x)) x := by
  unfold oneDimQuadraticInverseCurvatureObservable
    oneDimQuadraticInverseCurvatureScore
  convert ((hasDerivAt_id x).const_mul 2).div hcurvature hcurvature_ne using 1
  field_simp [hcurvature_ne]
  simp only [id_eq]
  ring

/-- The quadratic inverse-curvature observable satisfies the Dirichlet trace required at the
half-line endpoint, without a condition on the potential. -/
@[simp] theorem oneDimQuadraticInverseCurvatureObservable_zero
    (curvature : ℝ → ℝ) :
    oneDimQuadraticInverseCurvatureObservable curvature 0 = 0 := by
  simp [oneDimQuadraticInverseCurvatureObservable]

/-- At the endpoint the correction score is exactly twice the inverse curvature. -/
theorem oneDimQuadraticInverseCurvatureScore_zero
    {V₂ V₃ : ℝ} :
    oneDimQuadraticInverseCurvatureScore 0 V₂ V₃ = 2 / V₂ := by
  unfold oneDimQuadraticInverseCurvatureScore
  by_cases hV₂ : V₂ = 0
  · simp [hV₂]
  · field_simp [hV₂]
    ring

/-- The pointwise first Popescu correction density selected by the quadratic observable. -/
def oneDimQuadraticPopescuCorrectionDensity
    (x V₁ V₂ V₃ V₄ : ℝ) : ℝ :=
  oneDimQuadraticInverseCurvatureScore x V₂ V₃ ^ 2 /
    (1 + oneDimBrascampLiebCorrectionA V₁ V₂ (1 / V₂)
      (inverseCurvatureFirstJet V₂ V₃)
      (inverseCurvatureSecondJet V₂ V₃ V₄))

/-- Exact denominator-free form of the quadratic correction density. -/
theorem oneDimQuadraticPopescuCorrectionDensity_eq
    {x V₁ V₂ V₃ V₄ : ℝ}
    (hV₂ : V₂ ≠ 0)
    (hN : oneDimBrascampLiebFirstCorrectionNumerator V₁ V₂ V₃ V₄ ≠ 0) :
    oneDimQuadraticPopescuCorrectionDensity x V₁ V₂ V₃ V₄ =
      16 * (V₂ - x * V₃) ^ 2 /
        (V₂ * oneDimBrascampLiebFirstCorrectionNumerator V₁ V₂ V₃ V₄) := by
  rw [oneDimQuadraticPopescuCorrectionDensity,
    one_add_oneDimBrascampLiebCorrectionA_inverseCurvature hV₂]
  unfold oneDimQuadraticInverseCurvatureScore
  field_simp [hV₂, hN]
  ring

/-- Positive curvature and a positive Popescu numerator make the quadratic correction density
strict exactly when the curvature and dilation-curvature values do not coincide. -/
theorem oneDimQuadraticPopescuCorrectionDensity_pos_iff
    {x V₁ V₂ V₃ V₄ : ℝ}
    (hV₂ : 0 < V₂)
    (hN : 0 < oneDimBrascampLiebFirstCorrectionNumerator V₁ V₂ V₃ V₄) :
    0 < oneDimQuadraticPopescuCorrectionDensity x V₁ V₂ V₃ V₄ ↔
      V₂ - x * V₃ ≠ 0 := by
  rw [oneDimQuadraticPopescuCorrectionDensity_eq hV₂.ne' hN.ne']
  have hden : 0 <
      V₂ * oneDimBrascampLiebFirstCorrectionNumerator V₁ V₂ V₃ V₄ :=
    mul_pos hV₂ hN
  constructor
  · intro h hzero
    rw [hzero] at h
    norm_num at h
  · intro hnonzero
    exact div_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hnonzero)) hden

/-- The half-line endpoint correction density is automatically strictly positive whenever the
two Popescu weights are positive. -/
theorem oneDimQuadraticPopescuCorrectionDensity_zero_pos
    {V₁ V₂ V₃ V₄ : ℝ}
    (hV₂ : 0 < V₂)
    (hN : 0 < oneDimBrascampLiebFirstCorrectionNumerator V₁ V₂ V₃ V₄) :
    0 < oneDimQuadraticPopescuCorrectionDensity 0 V₁ V₂ V₃ V₄ := by
  rw [oneDimQuadraticPopescuCorrectionDensity_pos_iff hV₂ hN]
  simpa using hV₂.ne'

/-- The correction density is nonnegative at every point under the same positivity hypotheses. -/
theorem oneDimQuadraticPopescuCorrectionDensity_nonneg
    {x V₁ V₂ V₃ V₄ : ℝ}
    (hV₂ : 0 < V₂)
    (hN : 0 < oneDimBrascampLiebFirstCorrectionNumerator V₁ V₂ V₃ V₄) :
    0 ≤ oneDimQuadraticPopescuCorrectionDensity x V₁ V₂ V₃ V₄ := by
  rw [oneDimQuadraticPopescuCorrectionDensity_eq hV₂.ne' hN.ne']
  exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg hV₂.le hN.le)

end

end HTGeometry
