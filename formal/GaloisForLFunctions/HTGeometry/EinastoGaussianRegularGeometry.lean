import GaloisForLFunctions.HTGeometry.EinastoGaussianRadialInverse
import GaloisForLFunctions.HTGeometry.EinastoQuadraticCurvatureObstruction

/-!
# A nontrivial regular Gaussian survivor of the quadratic curvature correction

The actual Gaussian source integral gives a first-order metric with a finite
central Ricci and Kretschmann limit, for every scalar perturbation parameter.
All three derivative combinations in the curvature formula are controlled.
The limiting geometry is determined by one explicit multiplier, and both the
literal appendix sign and the corrected algebraic sign increase central
Kretschmann curvature at every positive coupling while keeping it finite.
These are exact statements about the constructed first-order family, not an
identification with a full nonlinear solution of the field equations.
-/
noncomputable section
open Filter Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

/-- The normalized metric derivative is controlled for every Einasto shape. -/
theorem einastoMetric_scaled_first_derivative_limit (d l a : ℝ) :
    Tendsto (fun t => deriv (einastoMetric d l a) (exp t) / exp t) atBot
      (𝓝 (-16 * Real.pi * exp d / 3)) := by
  have he : (fun t => deriv (einastoMetric d l a) (exp t) / exp t) =
      (fun t => 2 * einastoCore d l a (exp t) - 8 * Real.pi * einastoDensity d l a (exp t)) := by
    funext t
    rw [einastoMetricFirstJet_actual]
    unfold einastoMetricFirstJet
    field_simp
  rw [he]
  have hC := ((einastoCore_continuous d l a).continuousAt.tendsto.comp tendsto_exp_atBot).const_mul 2
  have hD := ((einastoDensity_continuous d l a).continuousAt.tendsto.comp tendsto_exp_atBot).const_mul (8 * Real.pi)
  have h := hC.sub hD
  simp only [Function.comp_apply, einastoCore_zero, einastoDensity_zero] at h
  have hc : 2 * (4 * Real.pi * exp d / 3) - 8 * Real.pi * exp d = -16 * Real.pi * exp d / 3 := by ring
  rwa [hc] at h

def einastoGaussianPerturbedMetric (d l σ β r : ℝ) : ℝ :=
  einastoMetric d l einastoGaussianShape r + β * einastoGaussianCorrection d l σ r

def einastoGaussianMetricCoefficient (d l σ β : ℝ) : ℝ :=
  -8 * Real.pi * exp d / 3 + β * einastoGaussianCorrectionCoefficient d l σ

/-- Explicit core multiplier induced by the actual source integral. -/
def einastoGaussianCoreMultiplier (d l σ β : ℝ) : ℝ :=
  1 + 72 * β / exp l ^ (2 : ℕ) + 64 * Real.pi * β * (1 - σ) * exp d

theorem einastoGaussianMetricCoefficient_eq (d l σ β : ℝ) :
    einastoGaussianMetricCoefficient d l σ β =
      -8 * Real.pi * exp d / 3 * einastoGaussianCoreMultiplier d l σ β := by
  unfold einastoGaussianMetricCoefficient einastoGaussianCoreMultiplier
  rw [einastoGaussianCorrectionCoefficient_eq]
  ring

theorem einastoGaussianPerturbedMetric_continuous (d l σ β : ℝ) :
    Continuous (einastoGaussianPerturbedMetric d l σ β) :=
  (einastoMetric_continuous d l einastoGaussianShape).add
    (continuous_const.mul (einastoGaussianCorrection_continuous d l σ))

theorem einastoGaussianPerturbedMetric_center (d l σ β : ℝ) :
    einastoGaussianPerturbedMetric d l σ β 0 = 1 := by
  simp only [einastoGaussianPerturbedMetric, einastoMetric_zero,
    einastoGaussianCorrection_center, mul_zero, add_zero]

theorem einastoGaussianPerturbedMetric_core_limit (d l σ β : ℝ) :
    Tendsto (einastoGaussianPerturbedMetric d l σ β) (𝓝 0) (𝓝 1) := by
  simpa only [einastoGaussianPerturbedMetric_center] using
    (einastoGaussianPerturbedMetric_continuous d l σ β).continuousAt.tendsto (x := 0)

theorem einastoGaussianPerturbedMetric_eventually_pos (d l σ β : ℝ) :
    ∀ᶠ t in atBot, 0 < einastoGaussianPerturbedMetric d l σ β (exp t) :=
  ((einastoGaussianPerturbedMetric_core_limit d l σ β).comp tendsto_exp_atBot).eventually
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))

theorem einastoGaussianPerturbedMetric_hasDerivAt (d l σ β t : ℝ) :
    HasDerivAt (einastoGaussianPerturbedMetric d l σ β)
      (deriv (einastoMetric d l einastoGaussianShape) (exp t) +
        β * deriv (einastoGaussianCorrection d l σ) (exp t)) (exp t) := by
  have hf := einastoMetric_derivative d l einastoGaussianShape t
  have hh := einastoGaussianCorrection_hasDerivAt d l σ t
  unfold einastoGaussianPerturbedMetric
  rw [hf.deriv, hh.deriv]
  simpa only [Pi.add_def] using hf.add (hh.const_mul β)

/-- The second metric derivative is actual, obtained from proved derivatives of both summands. -/
theorem einastoGaussianPerturbedMetric_second_hasDerivAt (d l σ β t : ℝ) :
    HasDerivAt (deriv (einastoGaussianPerturbedMetric d l σ β))
      (deriv (deriv (einastoMetric d l einastoGaussianShape)) (exp t) +
        β * deriv (deriv (einastoGaussianCorrection d l σ)) (exp t)) (exp t) := by
  have hf := einastoMetric_second_derivative d l einastoGaussianShape t
  have hh := einastoGaussianCorrection_second_hasDerivAt d l σ t
  rw [hf.deriv, hh.deriv]
  have h := hf.add (hh.const_mul β)
  simp only [Pi.add_def] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  have he := (einastoGaussianPerturbedMetric_hasDerivAt d l σ β (log r)).deriv
  simpa only [exp_log hr] using he

theorem einastoGaussianPerturbedMetric_quadratic_limit (d l σ β : ℝ) :
    Tendsto (fun t => (1 - einastoGaussianPerturbedMetric d l σ β (exp t)) / exp t ^ (2 : ℕ)) atBot
      (𝓝 (-einastoGaussianMetricCoefficient d l σ β)) := by
  have he : (fun t => (1 - einastoGaussianPerturbedMetric d l σ β (exp t)) / exp t ^ (2 : ℕ)) =
      (fun t => (1 - einastoMetric d l einastoGaussianShape (exp t)) / exp t ^ (2 : ℕ) -
        β * (einastoGaussianCorrection d l σ (exp t) / exp t ^ (2 : ℕ))) := by
    funext t
    unfold einastoGaussianPerturbedMetric
    ring
  rw [he]
  have h := (einastoMetric_quadratic_core_limit d l einastoGaussianShape).sub
    ((einastoGaussianCorrection_quadratic_limit d l σ).const_mul β)
  have hc : 8 * Real.pi * exp d / 3 - β * einastoGaussianCorrectionCoefficient d l σ =
      -einastoGaussianMetricCoefficient d l σ β := by
    unfold einastoGaussianMetricCoefficient
    ring
  rwa [hc] at h

theorem einastoGaussianPerturbedMetric_scaled_derivative_limit (d l σ β : ℝ) :
    Tendsto (fun t => deriv (einastoGaussianPerturbedMetric d l σ β) (exp t) / exp t) atBot
      (𝓝 (2 * einastoGaussianMetricCoefficient d l σ β)) := by
  have he : (fun t => deriv (einastoGaussianPerturbedMetric d l σ β) (exp t) / exp t) =
      (fun t => deriv (einastoMetric d l einastoGaussianShape) (exp t) / exp t +
        β * (deriv (einastoGaussianCorrection d l σ) (exp t) / exp t)) := by
    funext t
    rw [(einastoGaussianPerturbedMetric_hasDerivAt d l σ β t).deriv]
    ring
  rw [he]
  have h := (einastoMetric_scaled_first_derivative_limit d l einastoGaussianShape).add
    ((einastoGaussianCorrection_scaled_derivative_limit d l σ).const_mul β)
  have hc : -16 * Real.pi * exp d / 3 + β * (2 * einastoGaussianCorrectionCoefficient d l σ) =
      2 * einastoGaussianMetricCoefficient d l σ β := by
    unfold einastoGaussianMetricCoefficient
    ring
  rwa [hc] at h

theorem einastoGaussianPerturbedMetric_second_derivative_limit (d l σ β : ℝ) :
    Tendsto (fun t => deriv (deriv (einastoGaussianPerturbedMetric d l σ β)) (exp t)) atBot
      (𝓝 (2 * einastoGaussianMetricCoefficient d l σ β)) := by
  have he : (fun t => deriv (deriv (einastoGaussianPerturbedMetric d l σ β)) (exp t)) =
      (fun t => deriv (deriv (einastoMetric d l einastoGaussianShape)) (exp t) +
        β * deriv (deriv (einastoGaussianCorrection d l σ)) (exp t)) := by
    funext t
    exact (einastoGaussianPerturbedMetric_second_hasDerivAt d l σ β t).deriv
  rw [he]
  have h := (einastoMetricSecondJet_core_limit d l einastoGaussianShape).add
    ((einastoGaussianCorrection_second_derivative_limit d l σ).const_mul β)
  have hc : -16 * Real.pi * exp d / 3 + β * (2 * einastoGaussianCorrectionCoefficient d l σ) =
      2 * einastoGaussianMetricCoefficient d l σ β := by
    unfold einastoGaussianMetricCoefficient
    ring
  rwa [hc] at h

/-- Signed Ricci curvature remains finite and is fixed by the same quadratic coefficient. -/
theorem einastoGaussianPerturbedMetric_Ricci_limit (d l σ β : ℝ) :
    Tendsto (fun t => radialRicciScalar (einastoGaussianPerturbedMetric d l σ β) (exp t)) atBot
      (𝓝 (12 * einastoGaussianMetricCoefficient d l σ β)) := by
  have he : (fun t => radialRicciScalar (einastoGaussianPerturbedMetric d l σ β) (exp t)) =
      (fun t => deriv (deriv (einastoGaussianPerturbedMetric d l σ β)) (exp t) +
        4 * (deriv (einastoGaussianPerturbedMetric d l σ β) (exp t) / exp t) -
        2 * ((1 - einastoGaussianPerturbedMetric d l σ β (exp t)) / exp t ^ (2 : ℕ))) := by
    funext t
    unfold radialRicciScalar
    field_simp
    ring
  rw [he]
  have h := ((einastoGaussianPerturbedMetric_second_derivative_limit d l σ β).add
    ((einastoGaussianPerturbedMetric_scaled_derivative_limit d l σ β).const_mul 4)).sub
    ((einastoGaussianPerturbedMetric_quadratic_limit d l σ β).const_mul 2)
  have hc : 2 * einastoGaussianMetricCoefficient d l σ β + 4 * (2 * einastoGaussianMetricCoefficient d l σ β) -
      2 * (-einastoGaussianMetricCoefficient d l σ β) = 12 * einastoGaussianMetricCoefficient d l σ β := by ring
  rwa [hc] at h

/-- Complete control of the actual Kretschmann expression, not merely of the metric value. -/
theorem einastoGaussianPerturbedMetric_Kretschmann_limit (d l σ β : ℝ) :
    Tendsto (fun t => radialKretschmannScalar (einastoGaussianPerturbedMetric d l σ β) (exp t)) atBot
      (𝓝 (24 * einastoGaussianMetricCoefficient d l σ β ^ (2 : ℕ))) := by
  unfold radialKretschmannScalar
  have h := (((einastoGaussianPerturbedMetric_second_derivative_limit d l σ β).pow 2).add
    (((einastoGaussianPerturbedMetric_scaled_derivative_limit d l σ β).pow 2).const_mul 4)).add
    (((einastoGaussianPerturbedMetric_quadratic_limit d l σ β).pow 2).const_mul 4)
  have hc : (2 * einastoGaussianMetricCoefficient d l σ β) ^ (2 : ℕ) + 4 * (2 * einastoGaussianMetricCoefficient d l σ β) ^ (2 : ℕ) +
      4 * (-einastoGaussianMetricCoefficient d l σ β) ^ (2 : ℕ) = 24 * einastoGaussianMetricCoefficient d l σ β ^ (2 : ℕ) := by ring
  rwa [hc] at h

theorem einastoGaussianPerturbedMetric_Ricci_explicit (d l σ β : ℝ) :
    Tendsto (fun t => radialRicciScalar (einastoGaussianPerturbedMetric d l σ β) (exp t)) atBot
      (𝓝 (-32 * Real.pi * exp d * einastoGaussianCoreMultiplier d l σ β)) := by
  have h := einastoGaussianPerturbedMetric_Ricci_limit d l σ β
  rw [einastoGaussianMetricCoefficient_eq] at h
  have hc : 12 * (-8 * Real.pi * exp d / 3 * einastoGaussianCoreMultiplier d l σ β) =
      -32 * Real.pi * exp d * einastoGaussianCoreMultiplier d l σ β := by ring
  rwa [hc] at h

theorem einastoGaussianPerturbedMetric_Kretschmann_explicit (d l σ β : ℝ) :
    Tendsto (fun t => radialKretschmannScalar (einastoGaussianPerturbedMetric d l σ β) (exp t)) atBot
      (𝓝 ((512 * Real.pi ^ (2 : ℕ) * exp d ^ (2 : ℕ) / 3) * einastoGaussianCoreMultiplier d l σ β ^ (2 : ℕ))) := by
  have h := einastoGaussianPerturbedMetric_Kretschmann_limit d l σ β
  rw [einastoGaussianMetricCoefficient_eq] at h
  have hc : 24 * (-8 * Real.pi * exp d / 3 * einastoGaussianCoreMultiplier d l σ β) ^ (2 : ℕ) =
      (512 * Real.pi ^ (2 : ℕ) * exp d ^ (2 : ℕ) / 3) * einastoGaussianCoreMultiplier d l σ β ^ (2 : ℕ) := by ring
  rwa [hc] at h

theorem einastoGaussianCoreMultiplier_corrected_sign (d l β : ℝ) :
    einastoGaussianCoreMultiplier d l 1 β = 1 + 72 * β / exp l ^ (2 : ℕ) := by
  unfold einastoGaussianCoreMultiplier
  ring

theorem einastoGaussianCoreMultiplier_appendix_sign (d l β : ℝ) :
    einastoGaussianCoreMultiplier d l (-1) β = 1 + 72 * β / exp l ^ (2 : ℕ) + 128 * Real.pi * β * exp d := by
  unfold einastoGaussianCoreMultiplier
  ring

theorem einastoGaussianCoreMultiplier_corrected_gt_one (d l b : ℝ) :
    1 < einastoGaussianCoreMultiplier d l 1 (exp b) := by
  rw [einastoGaussianCoreMultiplier_corrected_sign]
  have h : 0 < 72 * exp b / exp l ^ (2 : ℕ) := by positivity
  linarith

theorem einastoGaussianCoreMultiplier_appendix_gt_one (d l b : ℝ) :
    1 < einastoGaussianCoreMultiplier d l (-1) (exp b) := by
  rw [einastoGaussianCoreMultiplier_appendix_sign]
  have h1 : 0 < 72 * exp b / exp l ^ (2 : ℕ) := by positivity
  have h2 : 0 < 128 * Real.pi * exp b * exp d := by positivity
  linarith

/-- Positive coupling changes the Gaussian core nontrivially while retaining finite curvature. -/
theorem einastoGaussian_corrected_core_growth (d l b : ℝ) :
    ∃ k : ℝ, Tendsto (fun t => radialKretschmannScalar (einastoGaussianPerturbedMetric d l 1 (exp b)) (exp t)) atBot (𝓝 k) ∧
      512 * Real.pi ^ (2 : ℕ) * exp d ^ (2 : ℕ) / 3 < k := by
  refine ⟨(512 * Real.pi ^ (2 : ℕ) * exp d ^ (2 : ℕ) / 3) * einastoGaussianCoreMultiplier d l 1 (exp b) ^ (2 : ℕ),
    einastoGaussianPerturbedMetric_Kretschmann_explicit d l 1 (exp b), ?_⟩
  have h := einastoGaussianCoreMultiplier_corrected_gt_one d l b
  have hp : 0 < 512 * Real.pi ^ (2 : ℕ) * exp d ^ (2 : ℕ) / 3 := by positivity
  have hs : 1 < einastoGaussianCoreMultiplier d l 1 (exp b) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (einastoGaussianCoreMultiplier d l 1 (exp b) - 1)]
  have hm := mul_pos hp (sub_pos.mpr hs)
  nlinarith

/-- The paper's literal appendix integral has the same nontrivial regular survivor. -/
theorem einastoGaussian_appendix_core_growth (d l b : ℝ) :
    ∃ k : ℝ, Tendsto (fun t => radialKretschmannScalar (einastoGaussianPerturbedMetric d l (-1) (exp b)) (exp t)) atBot (𝓝 k) ∧
      512 * Real.pi ^ (2 : ℕ) * exp d ^ (2 : ℕ) / 3 < k := by
  refine ⟨(512 * Real.pi ^ (2 : ℕ) * exp d ^ (2 : ℕ) / 3) * einastoGaussianCoreMultiplier d l (-1) (exp b) ^ (2 : ℕ),
    einastoGaussianPerturbedMetric_Kretschmann_explicit d l (-1) (exp b), ?_⟩
  have h := einastoGaussianCoreMultiplier_appendix_gt_one d l b
  have hp : 0 < 512 * Real.pi ^ (2 : ℕ) * exp d ^ (2 : ℕ) / 3 := by positivity
  have hs : 1 < einastoGaussianCoreMultiplier d l (-1) (exp b) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (einastoGaussianCoreMultiplier d l (-1) (exp b) - 1)]
  have hm := mul_pos hp (sub_pos.mpr hs)
  nlinarith

end GaloisForLFunctions.HTGeometry
