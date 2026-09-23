import GaloisForLFunctions.HTGeometry.EinastoShapeRadialInverse
import GaloisForLFunctions.HTGeometry.EinastoGaussianRegularGeometry

/-!
# Actual normalized metric jets for the singular side of the Einasto threshold

Parameterize every 0<q<2 by q=2/(1+exp(k)). In the actual radial inverse,
the quadratic background and algebraic sign defect disappear after division
by the leading profile power. All three metric jets have explicit normalized
limits. No nonzero coupling, bounded derivative, or regularity premise is
used; zero coupling is retained for the later exact classification.
-/
noncomputable section
open Filter Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def einastoSubquadraticShape (k : ℝ) : ℝ := -log (2 / (1 + exp k))

theorem einastoSubquadraticShape_exponent (k : ℝ) :
    exp (-einastoSubquadraticShape k) = 2 / (1 + exp k) := by
  unfold einastoSubquadraticShape
  rw [neg_neg, exp_log (by positivity : 0 < 2 / (1 + exp k))]

theorem einastoSubquadraticShape_exponent_lt_two (k : ℝ) : exp (-einastoSubquadraticShape k) < 2 := by
  rw [einastoSubquadraticShape_exponent]
  apply (div_lt_iff₀ (by positivity : 0 < 1 + exp k)).mpr
  linarith [exp_pos k]

theorem einastoProfilePower_inverse_scaled_exp (l a t : ℝ) :
    exp t ^ (2 : ℕ) / einastoProfilePower l a (exp t) = exp ((2 - exp (-a)) * t + exp (-a) * l) := by
  rw [einastoProfilePower_exp, sq, ← exp_add, ← exp_sub]
  congr 1
  ring

/-- The quadratic part is negligible compared with the actual leading profile power. -/
theorem einastoSubquadraticWeight_inverse_limit (l k : ℝ) :
    Tendsto (fun t => exp t ^ (2 : ℕ) / einastoProfilePower l (einastoSubquadraticShape k) (exp t)) atBot (𝓝 0) := by
  simp_rw [einastoProfilePower_inverse_scaled_exp]
  have hlin : Tendsto (fun t : ℝ => (2 - exp (-einastoSubquadraticShape k)) * t) atBot atBot :=
    tendsto_id.const_mul_atBot (sub_pos.mpr (einastoSubquadraticShape_exponent_lt_two k))
  have h := (tendsto_exp_atBot.comp hlin).mul_const (exp (exp (-einastoSubquadraticShape k) * l))
  simpa only [exp_add, Function.comp_def, zero_mul] using h

/-- The inverse radial weight diverges, with its sign and growth proved analytically. -/
theorem einastoSubquadraticWeight_tendsto_atTop (l k : ℝ) :
    Tendsto (fun t => einastoProfilePower l (einastoSubquadraticShape k) (exp t) / exp t ^ (2 : ℕ)) atBot atTop := by
  simp_rw [einastoProfilePower_scaled_exp]
  have hlin : Tendsto (fun t : ℝ => (exp (-einastoSubquadraticShape k) - 2) * t) atBot atTop :=
    tendsto_id.const_mul_atBot_of_neg (sub_neg.mpr (einastoSubquadraticShape_exponent_lt_two k))
  simpa only [exp_sub, Function.comp_def] using
    (tendsto_exp_atTop.comp hlin).atTop_div_const (exp_pos (exp (-einastoSubquadraticShape k) * l))

/-- The nonzero power correction survives; the original core and sign defect drop out. -/
theorem einastoSubquadraticMetric_normalized_limit (d l k σ β : ℝ) :
    Tendsto (fun t => (1 - einastoShapePerturbedMetric d l (einastoSubquadraticShape k) σ β (exp t)) /
      einastoProfilePower l (einastoSubquadraticShape k) (exp t)) atBot
      (𝓝 (-β * einastoPowerCorrectionCoefficient d (einastoSubquadraticShape k))) := by
  let a := einastoSubquadraticShape k
  have he : (fun t => (1 - einastoShapePerturbedMetric d l a σ β (exp t)) / einastoProfilePower l a (exp t)) =
      (fun t => (exp t ^ (2 : ℕ) / einastoProfilePower l a (exp t)) *
        ((1 - einastoMetric d l a (exp t)) / exp t ^ (2 : ℕ) - β * (einastoDefectCorrection d l a σ (exp t) / exp t ^ (2 : ℕ))) -
          β * (einastoPowerCorrection d l a (exp t) / einastoProfilePower l a (exp t))) := by
    funext t
    unfold einastoShapePerturbedMetric einastoShapeCorrection
    field_simp [(einastoProfilePower_pos l a t).ne']
    ring
  change Tendsto (fun t => (1 - einastoShapePerturbedMetric d l a σ β (exp t)) / einastoProfilePower l a (exp t)) atBot _
  rw [he]
  have hB := (einastoMetric_quadratic_core_limit d l a).sub ((einastoDefectCorrection_quadratic_limit d l a σ).const_mul β)
  have h := ((einastoSubquadraticWeight_inverse_limit l k).mul hB).sub
    ((einastoPowerCorrection_normalized_limit d l a).const_mul β)
  simpa only [zero_mul, zero_sub, neg_mul] using h

/-- The actual first derivative has the exact power-law coefficient q. -/
theorem einastoSubquadraticMetric_scaled_derivative_limit (d l k σ β : ℝ) :
    Tendsto (fun t => exp t * deriv (einastoShapePerturbedMetric d l (einastoSubquadraticShape k) σ β) (exp t) /
      einastoProfilePower l (einastoSubquadraticShape k) (exp t)) atBot
      (𝓝 (β * (exp (-einastoSubquadraticShape k) * einastoPowerCorrectionCoefficient d (einastoSubquadraticShape k)))) := by
  let a := einastoSubquadraticShape k
  have he : (fun t => exp t * deriv (einastoShapePerturbedMetric d l a σ β) (exp t) / einastoProfilePower l a (exp t)) =
      (fun t => (exp t ^ (2 : ℕ) / einastoProfilePower l a (exp t)) *
        (deriv (einastoMetric d l a) (exp t) / exp t + β * (deriv (einastoDefectCorrection d l a σ) (exp t) / exp t)) +
          β * (exp t * deriv (einastoPowerCorrection d l a) (exp t) / einastoProfilePower l a (exp t))) := by
    funext t
    rw [(einastoShapePerturbedMetric_hasDerivAt d l a σ β t).deriv,
      (einastoShapeCorrection_hasDerivAt d l a σ t).deriv]
    field_simp [(einastoProfilePower_pos l a t).ne']
    ring
  change Tendsto (fun t => exp t * deriv (einastoShapePerturbedMetric d l a σ β) (exp t) / einastoProfilePower l a (exp t)) atBot _
  rw [he]
  have hB := (einastoMetric_scaled_first_derivative_limit d l a).add
    ((einastoDefectCorrection_scaled_derivative_limit d l a σ).const_mul β)
  have h := ((einastoSubquadraticWeight_inverse_limit l k).mul hB).add
    ((einastoPowerCorrection_scaled_derivative_limit d l a).const_mul β)
  simpa only [zero_mul, zero_add] using h

/-- The actual second derivative has the exact power-law coefficient q(q-1). -/
theorem einastoSubquadraticMetric_scaled_second_derivative_limit (d l k σ β : ℝ) :
    Tendsto (fun t => exp t ^ (2 : ℕ) * deriv (deriv (einastoShapePerturbedMetric d l (einastoSubquadraticShape k) σ β)) (exp t) /
      einastoProfilePower l (einastoSubquadraticShape k) (exp t)) atBot
      (𝓝 (β * (exp (-einastoSubquadraticShape k) * (exp (-einastoSubquadraticShape k) - 1) *
        einastoPowerCorrectionCoefficient d (einastoSubquadraticShape k)))) := by
  let a := einastoSubquadraticShape k
  have he : (fun t => exp t ^ (2 : ℕ) * deriv (deriv (einastoShapePerturbedMetric d l a σ β)) (exp t) / einastoProfilePower l a (exp t)) =
      (fun t => (exp t ^ (2 : ℕ) / einastoProfilePower l a (exp t)) *
        (deriv (deriv (einastoMetric d l a)) (exp t) + β * deriv (deriv (einastoDefectCorrection d l a σ)) (exp t)) +
          β * (exp t ^ (2 : ℕ) * deriv (deriv (einastoPowerCorrection d l a)) (exp t) / einastoProfilePower l a (exp t))) := by
    funext t
    rw [(einastoShapePerturbedMetric_second_hasDerivAt d l a σ β t).deriv,
      (einastoShapeCorrection_second_hasDerivAt d l a σ t).deriv]
    field_simp [(einastoProfilePower_pos l a t).ne']
    ring
  change Tendsto (fun t => exp t ^ (2 : ℕ) * deriv (deriv (einastoShapePerturbedMetric d l a σ β)) (exp t) / einastoProfilePower l a (exp t)) atBot _
  rw [he]
  have hB := (einastoMetricSecondJet_core_limit d l a).add
    ((einastoDefectCorrection_second_derivative_limit d l a σ).const_mul β)
  have h := ((einastoSubquadraticWeight_inverse_limit l k).mul hB).add
    ((einastoPowerCorrection_scaled_second_derivative_limit d l a).const_mul β)
  simpa only [zero_mul, zero_add] using h

end GaloisForLFunctions.HTGeometry
