import Mathlib

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Positive signal amplitude, with admissibility carried as data. -/
abbrev PositiveSignal := {q : ℝ // 0 < q}

/-- Universal local quadratic model for a matched-filter profile. -/
def greedyBumpProfile {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Q : PositiveSignal) (g δ : E) : ℝ :=
  @inner ℝ E _ g δ - (Q : ℝ) / 2 * ‖δ‖ ^ 2

/-- Newton displacement in the matched isotropic geometry. -/
def greedyBumpDisplacement {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Q : PositiveSignal) (g : E) : E :=
  ((Q : ℝ)⁻¹) • g

/-- Exact quadratic completion underlying Proposition 5.1. -/
theorem greedyBumpProfile_completion {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Q : PositiveSignal) (g δ : E) :
    greedyBumpProfile Q g δ =
      ‖g‖ ^ 2 / (2 * (Q : ℝ)) -
        (Q : ℝ) / 2 * ‖δ - greedyBumpDisplacement Q g‖ ^ 2 := by
  rw [norm_sub_sq_real]
  simp only [greedyBumpProfile, greedyBumpDisplacement, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs]
  rw [abs_of_pos (inv_pos.mpr Q.property)]
  rw [real_inner_comm δ g]
  field_simp [ne_of_gt Q.property]
  ring

/-- The Newton displacement attains the exact local-profile gain. -/
theorem greedyBumpProfile_at_displacement {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Q : PositiveSignal) (g : E) :
    greedyBumpProfile Q g (greedyBumpDisplacement Q g) =
      ‖g‖ ^ 2 / (2 * (Q : ℝ)) := by
  rw [greedyBumpProfile_completion]
  simp

/-- Every displacement is bounded by the Newton-profile gain. -/
theorem greedyBumpProfile_le_gain {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Q : PositiveSignal) (g δ : E) :
    greedyBumpProfile Q g δ ≤ ‖g‖ ^ 2 / (2 * (Q : ℝ)) := by
  rw [greedyBumpProfile_completion]
  exact sub_le_self _ (mul_nonneg
    (div_nonneg (le_of_lt Q.property) (by norm_num)) (sq_nonneg _))

/-- Positive-definite template metric, with nondegeneracy carried as data. -/
structure PositiveTemplateMetric (D : ℕ) where
  matrix : Matrix (Fin D) (Fin D) ℝ
  posDef : matrix.PosDef

/-- Proposition 5.1's local quadratic profile in arbitrary template coordinates. -/
def greedyBumpMetricProfile {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) (g δ : Fin D → ℝ) : ℝ :=
  g ⬝ᵥ δ - (Q : ℝ) / 2 * (δ ⬝ᵥ G.matrix.mulVec δ)

/-- Proposition 5.1's metric optimizer `δ̂ = G⁻¹g/Q`. -/
def greedyBumpMetricDisplacement {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) (g : Fin D → ℝ) : Fin D → ℝ :=
  ((Q : ℝ)⁻¹) • G.matrix⁻¹.mulVec g

/-- A positive real template metric has a symmetric bilinear pairing. -/
theorem PositiveTemplateMetric.dotProduct_mulVec_comm {D : ℕ}
    (G : PositiveTemplateMetric D) (u v : Fin D → ℝ) :
    u ⬝ᵥ G.matrix.mulVec v = v ⬝ᵥ G.matrix.mulVec u := by
  have hsym : G.matrix.transpose = G.matrix := by
    simpa [Matrix.IsHermitian] using G.posDef.isHermitian.eq
  have hvec (w : Fin D → ℝ) : w ᵥ* G.matrix = G.matrix.mulVec w := by
    calc
      w ᵥ* G.matrix = w ᵥ* G.matrix.transpose := by rw [hsym]
      _ = G.matrix.mulVec w := Matrix.vecMul_transpose G.matrix w
  rw [Matrix.dotProduct_mulVec, hvec, dotProduct_comm]

/-- At `G⁻¹g/Q`, the metric profile gains exactly `gᵀG⁻¹g/(2Q)`. -/
theorem greedyBumpMetricProfile_at_displacement {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) (g : Fin D → ℝ) :
    greedyBumpMetricProfile Q G g (greedyBumpMetricDisplacement Q G g) =
      (g ⬝ᵥ G.matrix⁻¹.mulVec g) / (2 * (Q : ℝ)) := by
  let x := G.matrix⁻¹.mulVec g
  have hdet : IsUnit G.matrix.det :=
    (Matrix.isUnit_iff_isUnit_det G.matrix).mp G.posDef.isUnit
  have hx : G.matrix.mulVec x = g := by
    dsimp only [x]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
      Matrix.one_mulVec]
  have hQ : (Q : ℝ) ≠ 0 := ne_of_gt Q.property
  unfold greedyBumpMetricProfile greedyBumpMetricDisplacement
  change g ⬝ᵥ ((Q : ℝ)⁻¹ • x) -
      (Q : ℝ) / 2 *
        (((Q : ℝ)⁻¹ • x) ⬝ᵥ G.matrix.mulVec ((Q : ℝ)⁻¹ • x)) = _
  simp only [Matrix.mulVec_smul, hx, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [dotProduct_comm g x]
  field_simp [hQ]
  ring

/-- Exact metric square completion around `G⁻¹g/Q`. -/
theorem greedyBumpMetricProfile_completion {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) (g δ : Fin D → ℝ) :
    greedyBumpMetricProfile Q G g δ =
      (g ⬝ᵥ G.matrix⁻¹.mulVec g) / (2 * (Q : ℝ)) -
        (Q : ℝ) / 2 *
          ((δ - greedyBumpMetricDisplacement Q G g) ⬝ᵥ
            G.matrix.mulVec (δ - greedyBumpMetricDisplacement Q G g)) := by
  let x := G.matrix⁻¹.mulVec g
  have hdet : IsUnit G.matrix.det :=
    (Matrix.isUnit_iff_isUnit_det G.matrix).mp G.posDef.isUnit
  have hx : G.matrix.mulVec x = g := by
    dsimp only [x]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
      Matrix.one_mulVec]
  have hQ : (Q : ℝ) ≠ 0 := ne_of_gt Q.property
  have hcross : x ⬝ᵥ G.matrix.mulVec δ = g ⬝ᵥ δ := by
    calc
      x ⬝ᵥ G.matrix.mulVec δ = δ ⬝ᵥ G.matrix.mulVec x :=
        G.dotProduct_mulVec_comm x δ
      _ = δ ⬝ᵥ g := by rw [hx]
      _ = g ⬝ᵥ δ := dotProduct_comm δ g
  unfold greedyBumpMetricProfile greedyBumpMetricDisplacement
  change g ⬝ᵥ δ - (Q : ℝ) / 2 * (δ ⬝ᵥ G.matrix.mulVec δ) =
      (g ⬝ᵥ x) / (2 * (Q : ℝ)) - (Q : ℝ) / 2 *
        ((δ - (Q : ℝ)⁻¹ • x) ⬝ᵥ
          G.matrix.mulVec (δ - (Q : ℝ)⁻¹ • x))
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hx, dotProduct_sub,
    sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [hcross, dotProduct_comm g x, dotProduct_comm δ g]
  field_simp [hQ]
  ring

/-- No metric displacement exceeds the Newton-profile gain. -/
theorem greedyBumpMetricProfile_le_gain {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) (g δ : Fin D → ℝ) :
    greedyBumpMetricProfile Q G g δ ≤
      (g ⬝ᵥ G.matrix⁻¹.mulVec g) / (2 * (Q : ℝ)) := by
  rw [greedyBumpMetricProfile_completion]
  apply sub_le_self
  apply mul_nonneg
  · exact div_nonneg Q.property.le (by norm_num)
  · simpa only [star_trivial] using
      G.posDef.posSemidef.dotProduct_mulVec_nonneg
        (δ - greedyBumpMetricDisplacement Q G g)

/-- The metric optimizer is the unique displacement attaining the gain. -/
theorem greedyBumpMetricProfile_eq_gain_iff {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) (g δ : Fin D → ℝ) :
    greedyBumpMetricProfile Q G g δ =
        (g ⬝ᵥ G.matrix⁻¹.mulVec g) / (2 * (Q : ℝ)) ↔
      δ = greedyBumpMetricDisplacement Q G g := by
  constructor
  · intro h
    rw [greedyBumpMetricProfile_completion] at h
    have hquad : (δ - greedyBumpMetricDisplacement Q G g) ⬝ᵥ
        G.matrix.mulVec (δ - greedyBumpMetricDisplacement Q G g) = 0 := by
      have hQhalf : 0 < (Q : ℝ) / 2 := div_pos Q.property (by norm_num)
      nlinarith
    by_contra hne
    have hdiff : δ - greedyBumpMetricDisplacement Q G g ≠ 0 := sub_ne_zero.mpr hne
    have hpos := G.posDef.dotProduct_mulVec_pos hdiff
    simp only [star_trivial] at hpos
    linarith
  · rintro rfl
    exact greedyBumpMetricProfile_at_displacement Q G g

/-- Matched high-signal Hessian `H_Q = Q G`. -/
def greedyBumpHessian {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) : Matrix (Fin D) (Fin D) ℝ :=
  (Q : ℝ) • G.matrix

/-- Determinant volume scales by exactly `Q^D`. -/
theorem greedyBumpHessian_det {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) :
    (greedyBumpHessian Q G).det =
      (Q : ℝ) ^ D * G.matrix.det := by
  simp [greedyBumpHessian]

/-- The trials-volume density scales by exactly `Q^(D/2)`. -/
theorem greedyBumpHessian_sqrt_det {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) :
    Real.sqrt (greedyBumpHessian Q G).det =
      (Q : ℝ) ^ ((D : ℝ) / 2) * Real.sqrt G.matrix.det := by
  rw [greedyBumpHessian_det,
    Real.sqrt_mul (pow_nonneg (le_of_lt Q.property) D)]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast]
  rw [← Real.rpow_mul (le_of_lt Q.property)]
  congr 1
  ring

/-- Matched trace penalty collapses to dimension divided by signal. -/
theorem greedyBumpHessian_trace_inv_mul {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) :
    Matrix.trace ((greedyBumpHessian Q G)⁻¹ * G.matrix) =
      (D : ℝ) / (Q : ℝ) := by
  letI : Invertible (Q : ℝ) := invertibleOfNonzero (ne_of_gt Q.property)
  have hdet : IsUnit G.matrix.det :=
    (Matrix.isUnit_iff_isUnit_det G.matrix).mp G.posDef.isUnit
  rw [greedyBumpHessian, Matrix.inv_smul _ _ hdet, Matrix.smul_mul,
    Matrix.nonsing_inv_mul _ hdet, Matrix.trace_smul, Matrix.trace_one]
  simp [invOf_eq_inv, div_eq_mul_inv]
  ring

/-- Proposition 5.1's local bias term is exactly `D/(2Q)`. -/
theorem greedyBump_matched_bias {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) :
    (1 / 2 : ℝ) * Matrix.trace
      ((greedyBumpHessian Q G)⁻¹ * G.matrix) =
        (D : ℝ) / (2 * (Q : ℝ)) := by
  rw [greedyBumpHessian_trace_inv_mul]
  field_simp

/-- Logarithm of the leading trials-factor law `K Q^D`. -/
def greedyBumpLogTrialsFactor (D : ℕ) (K : PositiveSignal) (Q : ℝ) : ℝ :=
  Real.log (K : ℝ) + (D : ℝ) * Real.log Q

/-- The leading log trials factor has slope `D/Q` at every positive signal. -/
theorem greedyBumpLogTrialsFactor_hasDerivAt (D : ℕ) (K Q : PositiveSignal) :
    HasDerivAt (greedyBumpLogTrialsFactor D K) ((D : ℝ) / (Q : ℝ)) (Q : ℝ) := by
  unfold greedyBumpLogTrialsFactor
  simpa only [div_eq_mul_inv, mul_comm] using
    ((Real.hasDerivAt_log (ne_of_gt Q.property)).const_mul (D : ℝ)).const_add
      (Real.log (K : ℝ))

/-- On the positive domain, this is exactly `log (K Q^D)`. -/
theorem greedyBumpLogTrialsFactor_eq_log_power (D : ℕ) (K Q : PositiveSignal) :
    greedyBumpLogTrialsFactor D K (Q : ℝ) =
      Real.log ((K : ℝ) * (Q : ℝ) ^ D) := by
  rw [greedyBumpLogTrialsFactor,
    Real.log_mul (ne_of_gt K.property) (pow_ne_zero _ (ne_of_gt Q.property)),
    Real.log_pow]

/-- The paper's bridge: matched local bias equals half the log trials-factor slope. -/
theorem greedyBump_matchedBias_eq_half_logTrialsSlope {D : ℕ}
    (Q : PositiveSignal) (G : PositiveTemplateMetric D) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q G)⁻¹ * G.matrix) =
      (1 / 2 : ℝ) * ((D : ℝ) / (Q : ℝ)) := by
  rw [greedyBumpHessian_trace_inv_mul]

/-- Differential form: trials-factor log slope is twice matched local bias. -/
theorem greedyBumpLogTrialsFactor_hasDerivAt_twiceMatchedBias {D : ℕ}
    (K Q : PositiveSignal) (G : PositiveTemplateMetric D) :
    HasDerivAt (greedyBumpLogTrialsFactor D K)
      (2 * ((1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q G)⁻¹ * G.matrix))) (Q : ℝ) := by
  convert greedyBumpLogTrialsFactor_hasDerivAt D K Q using 1
  rw [greedyBumpHessian_trace_inv_mul]
  ring

/-- Leading localization covariance `Q⁻²G⁻¹` of fitted template coordinates. -/
def greedyBumpLocalizationCovariance {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) : Matrix (Fin D) (Fin D) ℝ :=
  ((Q : ℝ)⁻¹ ^ 2) • G.matrix⁻¹

/-- Localization covariance remains positive definite. -/
theorem greedyBumpLocalizationCovariance_posDef {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) :
    (greedyBumpLocalizationCovariance Q G).PosDef := by
  apply G.posDef.inv.smul
  exact sq_pos_of_pos (inv_pos.mpr Q.property)

/-- Exact determinant form of the `Q⁻²G⁻¹` localization law. -/
theorem greedyBumpLocalizationCovariance_det {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) :
    (greedyBumpLocalizationCovariance Q G).det =
      ((Q : ℝ)⁻¹ ^ 2) ^ D * G.matrix.det⁻¹ := by
  simp [greedyBumpLocalizationCovariance, Matrix.det_nonsing_inv]

/-- Expected squared localization radius in metric units is `D/Q²`. -/
theorem greedyBumpLocalizationCovariance_trace_mul {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) :
    Matrix.trace (greedyBumpLocalizationCovariance Q G * G.matrix) =
      (D : ℝ) / (Q : ℝ) ^ 2 := by
  have hdet : IsUnit G.matrix.det :=
    (Matrix.isUnit_iff_isUnit_det G.matrix).mp G.posDef.isUnit
  rw [greedyBumpLocalizationCovariance, Matrix.smul_mul,
    Matrix.nonsing_inv_mul _ hdet, Matrix.trace_smul, Matrix.trace_one]
  simp only [smul_eq_mul, Fintype.card_fin]
  field_simp [ne_of_gt Q.property]

/-- Logarithm of the leading localization-volume law `K Q⁻ᴰ`. -/
def greedyBumpLogLocalizationVolume (D : ℕ) (K : PositiveSignal) (Q : ℝ) : ℝ :=
  Real.log (K : ℝ) - (D : ℝ) * Real.log Q

/-- The leading log localization volume has slope `-D/Q`. -/
theorem greedyBumpLogLocalizationVolume_hasDerivAt
    (D : ℕ) (K Q : PositiveSignal) :
    HasDerivAt (greedyBumpLogLocalizationVolume D K)
      (-((D : ℝ) / (Q : ℝ))) (Q : ℝ) := by
  unfold greedyBumpLogLocalizationVolume
  simpa only [div_eq_mul_inv, mul_comm, neg_mul] using
    ((Real.hasDerivAt_log (ne_of_gt Q.property)).const_mul (D : ℝ)).const_sub
      (Real.log (K : ℝ))

/-- On the positive domain, this is exactly `log (K / Q^D)`. -/
theorem greedyBumpLogLocalizationVolume_eq_log_div_power
    (D : ℕ) (K Q : PositiveSignal) :
    greedyBumpLogLocalizationVolume D K (Q : ℝ) =
      Real.log ((K : ℝ) / (Q : ℝ) ^ D) := by
  rw [greedyBumpLogLocalizationVolume,
    Real.log_div (ne_of_gt K.property) (pow_ne_zero _ (ne_of_gt Q.property)),
    Real.log_pow]

/-- Localization-volume form: bias is minus half the log-volume slope. -/
theorem greedyBumpLogLocalizationVolume_hasDerivAt_negTwiceMatchedBias
    {D : ℕ} (K Q : PositiveSignal) (G : PositiveTemplateMetric D) :
    HasDerivAt (greedyBumpLogLocalizationVolume D K)
      (-2 * ((1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q G)⁻¹ * G.matrix))) (Q : ℝ) := by
  convert greedyBumpLogLocalizationVolume_hasDerivAt D K Q using 1
  rw [greedyBumpHessian_trace_inv_mul]
  ring

/-- Closed package of the paper's optimizer, trials-volume, trace, and bias laws. -/
structure GreedyBumpMetricLaws {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) : Prop where
  profileAtOptimizer : ∀ g : Fin D → ℝ,
    greedyBumpMetricProfile Q G g (greedyBumpMetricDisplacement Q G g) =
      (g ⬝ᵥ G.matrix⁻¹.mulVec g) / (2 * (Q : ℝ))
  profileUpperBound : ∀ g δ : Fin D → ℝ,
    greedyBumpMetricProfile Q G g δ ≤
      (g ⬝ᵥ G.matrix⁻¹.mulVec g) / (2 * (Q : ℝ))
  uniqueOptimizer : ∀ g δ : Fin D → ℝ,
    greedyBumpMetricProfile Q G g δ =
        (g ⬝ᵥ G.matrix⁻¹.mulVec g) / (2 * (Q : ℝ)) ↔
      δ = greedyBumpMetricDisplacement Q G g
  determinant :
    (greedyBumpHessian Q G).det = (Q : ℝ) ^ D * G.matrix.det
  trialsVolume :
    Real.sqrt (greedyBumpHessian Q G).det =
      (Q : ℝ) ^ ((D : ℝ) / 2) * Real.sqrt G.matrix.det
  tracePenalty :
    Matrix.trace ((greedyBumpHessian Q G)⁻¹ * G.matrix) =
      (D : ℝ) / (Q : ℝ)
  localBias :
    (1 / 2 : ℝ) * Matrix.trace
      ((greedyBumpHessian Q G)⁻¹ * G.matrix) =
      (D : ℝ) / (2 * (Q : ℝ))
  logTrialsSlope : ∀ K : PositiveSignal,
    HasDerivAt (greedyBumpLogTrialsFactor D K)
      ((D : ℝ) / (Q : ℝ)) (Q : ℝ)
  trialsBiasBridge : ∀ K : PositiveSignal,
    HasDerivAt (greedyBumpLogTrialsFactor D K)
      (2 * ((1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q G)⁻¹ * G.matrix))) (Q : ℝ)
  localizationSlope : ∀ K : PositiveSignal,
    HasDerivAt (greedyBumpLogLocalizationVolume D K)
      (-((D : ℝ) / (Q : ℝ))) (Q : ℝ)
  localizationBiasBridge : ∀ K : PositiveSignal,
    HasDerivAt (greedyBumpLogLocalizationVolume D K)
      (-2 * ((1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q G)⁻¹ * G.matrix))) (Q : ℝ)
  localizationCovariancePosDef :
    (greedyBumpLocalizationCovariance Q G).PosDef
  localizationCovarianceDet :
    (greedyBumpLocalizationCovariance Q G).det =
      ((Q : ℝ)⁻¹ ^ 2) ^ D * G.matrix.det⁻¹
  localizationMetricRadius :
    Matrix.trace (greedyBumpLocalizationCovariance Q G * G.matrix) =
      (D : ℝ) / (Q : ℝ) ^ 2

/-- Every bundled positive metric satisfies all fourteen matched local-search laws. -/
theorem greedyBumpMetricLaws_closed {D : ℕ} (Q : PositiveSignal)
    (G : PositiveTemplateMetric D) : GreedyBumpMetricLaws Q G where
  profileAtOptimizer := greedyBumpMetricProfile_at_displacement Q G
  profileUpperBound := greedyBumpMetricProfile_le_gain Q G
  uniqueOptimizer := greedyBumpMetricProfile_eq_gain_iff Q G
  determinant := greedyBumpHessian_det Q G
  trialsVolume := greedyBumpHessian_sqrt_det Q G
  tracePenalty := greedyBumpHessian_trace_inv_mul Q G
  localBias := greedyBump_matched_bias Q G
  logTrialsSlope := fun K => greedyBumpLogTrialsFactor_hasDerivAt D K Q
  trialsBiasBridge := fun K =>
    greedyBumpLogTrialsFactor_hasDerivAt_twiceMatchedBias K Q G
  localizationSlope := fun K =>
    greedyBumpLogLocalizationVolume_hasDerivAt D K Q
  localizationBiasBridge := fun K =>
    greedyBumpLogLocalizationVolume_hasDerivAt_negTwiceMatchedBias K Q G
  localizationCovariancePosDef := greedyBumpLocalizationCovariance_posDef Q G
  localizationCovarianceDet := greedyBumpLocalizationCovariance_det Q G
  localizationMetricRadius := greedyBumpLocalizationCovariance_trace_mul Q G

/-- Every coordinate of a standard Gaussian has unit second moment. -/
theorem greedyBump_integral_coordinate_sq_stdGaussian {D : ℕ} (i : Fin D) :
    ∫ x : EuclideanSpace ℝ (Fin D), (x i) ^ 2
      ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin D)) = 1 := by
  rw [← variance_of_integral_eq_zero (by fun_prop)]
  · rw [← ProbabilityTheory.multivariateGaussian_zero_one]
    simpa using ProbabilityTheory.variance_eval_multivariateGaussian
      (μ := (0 : EuclideanSpace ℝ (Fin D)))
      (S := (1 : Matrix (Fin D) (Fin D) ℝ)) Matrix.PosSemidef.one i
  · simpa using ProbabilityTheory.integral_strongDual_stdGaussian
      (E := EuclideanSpace ℝ (Fin D)) (EuclideanSpace.proj i)

/-- Corollary 5.1's `chi-square_D` variable has exact mean `D`. -/
theorem greedyBump_integral_norm_sq_stdGaussian (D : ℕ) :
    ∫ x : EuclideanSpace ℝ (Fin D), ‖x‖ ^ 2
      ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin D)) = D := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum]
  · simp [greedyBump_integral_coordinate_sq_stdGaussian]
  · intro i hi
    exact ((IsGaussian.memLp_two_id
      (μ := ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin D)))).continuousLinearMap_comp
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin D) →L[ℝ] ℝ)).integrable_sq

/-- `chi-square_D` realized as squared norm of the standard Gaussian score. -/
def greedyBumpChiSquare (D : ℕ) : ProbabilityMeasure ℝ where
  val := (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin D))).map
    (fun x => ‖x‖ ^ 2)
  property := Measure.isProbabilityMeasure_map (by fun_prop)

/-- The bundled `chi-square_D` law has exact mean `D`. -/
theorem greedyBumpChiSquare_mean (D : ℕ) :
    ∫ u : ℝ, u ∂(greedyBumpChiSquare D : Measure ℝ) = D := by
  change ∫ u : ℝ, u ∂((ProbabilityTheory.stdGaussian
    (EuclideanSpace ℝ (Fin D))).map (fun x => ‖x‖ ^ 2)) = D
  rw [integral_map (by fun_prop) (by fun_prop)]
  exact greedyBump_integral_norm_sq_stdGaussian D

/-- Newton displacement has the paper's normalized `chi-square_D` law. -/
theorem greedyBumpDisplacement_chiSquare_law (D : ℕ) (Q : PositiveSignal) :
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin D))).map
      (fun g => (Q : ℝ) ^ 2 * ‖greedyBumpDisplacement Q g‖ ^ 2) =
        (greedyBumpChiSquare D : Measure ℝ) := by
  have hfun :
      (fun g : EuclideanSpace ℝ (Fin D) =>
        (Q : ℝ) ^ 2 * ‖greedyBumpDisplacement Q g‖ ^ 2) =
      fun g => ‖g‖ ^ 2 := by
    funext g
    simp only [greedyBumpDisplacement, norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos (inv_pos.mpr Q.property)]
    field_simp [ne_of_gt Q.property]
  rw [hfun]
  change _ = (ProbabilityTheory.stdGaussian
    (EuclideanSpace ℝ (Fin D))).map (fun g => ‖g‖ ^ 2)
  rfl

/-- Expected optimized local-profile gain is exactly `D/(2Q)`. -/
theorem greedyBump_expected_profile_gain (D : ℕ) (Q : PositiveSignal) :
    ∫ g : EuclideanSpace ℝ (Fin D),
        greedyBumpProfile Q g (greedyBumpDisplacement Q g)
      ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin D)) =
        (D : ℝ) / (2 * (Q : ℝ)) := by
  simp_rw [greedyBumpProfile_at_displacement]
  rw [integral_div, greedyBump_integral_norm_sq_stdGaussian]

/-- Template/tangent pair satisfying the normalized-template orthogonality law. -/
structure OrthogonalTemplateTangent (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  template : E
  tangent : E
  orthogonal : @inner ℝ E _ template tangent = 0

/-- Data residual after subtracting the matched signal component. -/
def greedyBumpResidual {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Q : ℝ) (data template : E) : E :=
  data - Q • template

/-- Proposition 6.1 bridge: score derivative couples only to residual noise. -/
theorem greedyBump_matchedFilter_derivative_bridge
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (pair : OrthogonalTemplateTangent E) (Q : ℝ) (data : E) :
    @inner ℝ E _ data pair.tangent =
      @inner ℝ E _ (greedyBumpResidual Q data pair.template) pair.tangent := by
  simp [greedyBumpResidual, inner_sub_left, real_inner_smul_left, pair.orthogonal]

/-- Complex template/tangent pair satisfying normalized-template orthogonality. -/
structure OrthogonalComplexTemplateTangent (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] where
  template : E
  tangent : E
  orthogonal : @inner ℂ E _ template tangent = 0

/-- Complex-data residual after subtracting a real matched amplitude. -/
def greedyBumpComplexResidual {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (Q : ℝ) (data template : E) : E :=
  data - (Q : ℂ) • template

/-- Complex matched-filter bridge used by arithmetic Hilbert-space sources. -/
theorem greedyBump_complexMatchedFilter_derivative_bridge
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (pair : OrthogonalComplexTemplateTangent E) (Q : ℝ) (data : E) :
    @inner ℂ E _ data pair.tangent =
      @inner ℂ E _ (greedyBumpComplexResidual Q data pair.template) pair.tangent := by
  simp [greedyBumpComplexResidual, pair.orthogonal]

/-- Exact, independence-free local/remote maximum decomposition. -/
theorem greedyBump_max_decomposition (baseline localValue remote : ℝ) :
    max localValue remote - baseline =
      (localValue - baseline) + max (remote - localValue) 0 := by
  rcases le_total remote localValue with h | h
  · simp [max_eq_left h, sub_nonpos.mpr h]
  · simp [max_eq_right h, sub_nonneg.mpr h]

/-- Remote competition correction is always nonnegative. -/
theorem greedyBump_remote_correction_nonneg (localValue remote : ℝ) :
    0 ≤ max (remote - localValue) 0 := le_max_right _ _

end

end GaloisForLFunctions.HTGeometry
