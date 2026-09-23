import GaloisForLFunctions.HTGeometry.EinastoShapeCurvature

/-!
# Exact shape-dependent decomposition of the quadratic Einasto source

For arXiv:2608.23600's quadratic correction, the source splits into a bounded
algebraic-sign defect and a single power of radius times a continuous factor.
That factor has a strictly negative central value for every Einasto shape.
This identifies the leading singular term from actual metric derivatives.
-/
noncomputable section
open Filter Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

/-- Continuous factor left after removing the exact radial power from the corrected source. -/
def einastoShapeSourceFactor (d l a r : ℝ) : ℝ :=
  let q := exp (-a)
  let u := einastoProfilePower l a r
  let ρ := einastoDensity d l a r
  4 * Real.pi * ρ ^ (2 : ℕ) * q * r ^ (2 : ℕ) * (q * u - 4) -
    2 * einastoMetric d l a r * q * ρ *
      ((q + 1) * (q + 4) - q * (3 * q + 5) * u + q ^ (2 : ℕ) * u ^ (2 : ℕ)) -
    q * ρ * r ^ (2 : ℕ) * (2 * einastoCore d l a r - 8 * Real.pi * ρ) * (q + 4 - q * u)

/-- The entire difference between the two algebraic signs is a bounded curvature square. -/
def einastoShapeSourceDefect (d l a σ r : ℝ) : ℝ :=
  (σ - 1) * einastoShapeRicci d l a r ^ (2 : ℕ) / (16 * Real.pi)

theorem einastoShapeSourceFactor_continuous (d l a : ℝ) : Continuous (einastoShapeSourceFactor d l a) := by
  have hD := einastoDensity_continuous d l a
  have hU := einastoProfilePower_continuous l a
  have hf := einastoMetric_continuous d l a
  have hC := einastoCore_continuous d l a
  unfold einastoShapeSourceFactor
  dsimp only
  fun_prop

theorem einastoShapeSourceDefect_continuous (d l a σ : ℝ) : Continuous (einastoShapeSourceDefect d l a σ) :=
  (continuous_const.mul ((einastoShapeRicci_continuous d l a).pow 2)).div_const (16 * Real.pi)

theorem einastoShapeSourceFactor_core (d l a : ℝ) :
    einastoShapeSourceFactor d l a 0 = -2 * exp (-a) * exp d * (exp (-a) + 1) * (exp (-a) + 4) := by
  unfold einastoShapeSourceFactor
  rw [einastoProfilePower_zero, einastoDensity_zero, einastoMetric_zero]
  ring

/-- The leading coefficient cannot vanish at any positive shape exponent or density. -/
theorem einastoShapeSourceFactor_core_neg (d l a : ℝ) : einastoShapeSourceFactor d l a 0 < 0 := by
  rw [einastoShapeSourceFactor_core]
  have h : 0 < 2 * exp (-a) * exp d * (exp (-a) + 1) * (exp (-a) + 4) := by positivity
  linarith

theorem einastoShapeSourceDefect_core (d l a σ : ℝ) :
    einastoShapeSourceDefect d l a σ 0 = 64 * Real.pi * (σ - 1) * exp d ^ (2 : ℕ) := by
  unfold einastoShapeSourceDefect
  rw [einastoShapeRicci_core]
  field_simp
  ring

/-- Exact factorization of the actual radial source, with no asymptotic assumptions. -/
theorem einastoShapeSource_decomposition (d l a σ t : ℝ) :
    quadraticRadialSource σ (einastoMetric d l a) (exp t) =
      einastoProfilePower l a (exp t) / exp t ^ (2 : ℕ) * einastoShapeSourceFactor d l a (exp t) +
        einastoShapeSourceDefect d l a σ (exp t) := by
  unfold quadraticRadialSource
  rw [einastoShapeRicci_actual, radialEinsteinDensity_einasto,
    einastoShapeRicci_actual_derivative, einastoShapeRicci_actual_second_derivative,
    einastoMetricFirstJet_actual]
  unfold einastoShapeSourceFactor einastoShapeSourceDefect einastoShapeRicci
    einastoShapeRicciSlope einastoShapeRicciSecond einastoMetricFirstJet
  dsimp only
  field_simp
  ring

theorem einastoProfilePower_scaled_exp (l a t : ℝ) :
    einastoProfilePower l a (exp t) / exp t ^ (2 : ℕ) = exp ((exp (-a) - 2) * t - exp (-a) * l) := by
  rw [einastoProfilePower_exp, sq, ← exp_add, ← exp_sub]
  congr 1
  ring

/-- A single exponential of logarithmic radius carries all possible source divergence. -/
theorem einastoShapeSource_exp_decomposition (d l a σ t : ℝ) :
    quadraticRadialSource σ (einastoMetric d l a) (exp t) =
      exp ((exp (-a) - 2) * t - exp (-a) * l) * einastoShapeSourceFactor d l a (exp t) +
        einastoShapeSourceDefect d l a σ (exp t) := by
  rw [einastoShapeSource_decomposition, einastoProfilePower_scaled_exp]

theorem einastoShapeSourceFactor_core_limit (d l a : ℝ) :
    Tendsto (fun t => einastoShapeSourceFactor d l a (exp t)) atBot
      (𝓝 (-2 * exp (-a) * exp d * (exp (-a) + 1) * (exp (-a) + 4))) := by
  rw [← einastoShapeSourceFactor_core d l a]
  exact (einastoShapeSourceFactor_continuous d l a).continuousAt.tendsto.comp tendsto_exp_atBot

theorem einastoShapeSourceDefect_core_limit (d l a σ : ℝ) :
    Tendsto (fun t => einastoShapeSourceDefect d l a σ (exp t)) atBot
      (𝓝 (64 * Real.pi * (σ - 1) * exp d ^ (2 : ℕ))) := by
  rw [← einastoShapeSourceDefect_core d l a σ]
  exact (einastoShapeSourceDefect_continuous d l a σ).continuousAt.tendsto.comp tendsto_exp_atBot

/-- The normalized leading term is nonzero, independently of the paper's algebraic-sign discrepancy. -/
theorem einastoShapeSource_normalized_limit (d l a σ : ℝ) :
    Tendsto (fun t => (quadraticRadialSource σ (einastoMetric d l a) (exp t) -
      einastoShapeSourceDefect d l a σ (exp t)) * exp ((2 - exp (-a)) * t + exp (-a) * l)) atBot
      (𝓝 (-2 * exp (-a) * exp d * (exp (-a) + 1) * (exp (-a) + 4))) := by
  have he : (fun t => (quadraticRadialSource σ (einastoMetric d l a) (exp t) -
      einastoShapeSourceDefect d l a σ (exp t)) * exp ((2 - exp (-a)) * t + exp (-a) * l)) =
      (fun t => einastoShapeSourceFactor d l a (exp t)) := by
    funext t
    rw [einastoShapeSource_exp_decomposition, add_sub_cancel_right, mul_right_comm, ← exp_add]
    have hz : ((exp (-a) - 2) * t - exp (-a) * l) +
        ((2 - exp (-a)) * t + exp (-a) * l) = 0 := by ring
    rw [hz, exp_zero, one_mul]
  rw [he]
  exact einastoShapeSourceFactor_core_limit d l a

end GaloisForLFunctions.HTGeometry
