import GaloisForLFunctions.HTGeometry.EinastoSuperGaussianRadialInverse
import GaloisForLFunctions.HTGeometry.EinastoGaussianRegularGeometry

/-!
# Finite actual curvature for every super-Gaussian first-order correction

Complete the regular side q>2 of the quadratic source audit in arXiv:2608.23600.
The constructed metric has actual first and second derivatives and finite
central Ricci and Kretschmann limits for every coupling. For the algebraic
sign consistent with equation (6), the original central curvature is preserved.
The appendix sign instead changes it by an explicit density-dependent factor.
These are exact results for the integral's first-order metric family.
-/
noncomputable section
open Filter Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def einastoSuperGaussianPerturbedMetric (d l k σ β r : ℝ) : ℝ :=
  einastoMetric d l (einastoSuperGaussianShape k) r + β * einastoSuperGaussianCorrection d l k σ r

def einastoSuperGaussianMetricCoefficient (d l k σ β : ℝ) : ℝ :=
  -8 * Real.pi * exp d / 3 + β * einastoSuperGaussianCorrectionCoefficient d l k σ

/-- Explicit core multiplier induced by the actual source integral. -/
def einastoSuperGaussianCoreMultiplier (d σ β : ℝ) : ℝ :=
  1 + 64 * Real.pi * β * (1 - σ) * exp d

theorem einastoSuperGaussianMetricCoefficient_eq (d l k σ β : ℝ) :
    einastoSuperGaussianMetricCoefficient d l k σ β =
      -8 * Real.pi * exp d / 3 * einastoSuperGaussianCoreMultiplier d σ β := by
  unfold einastoSuperGaussianMetricCoefficient einastoSuperGaussianCoreMultiplier
  rw [einastoSuperGaussianCorrectionCoefficient_eq]
  ring

theorem einastoSuperGaussianPerturbedMetric_continuous (d l k σ β : ℝ) :
    Continuous (einastoSuperGaussianPerturbedMetric d l k σ β) :=
  (einastoMetric_continuous d l (einastoSuperGaussianShape k)).add
    (continuous_const.mul (einastoSuperGaussianCorrection_continuous d l k σ))

theorem einastoSuperGaussianPerturbedMetric_center (d l k σ β : ℝ) :
    einastoSuperGaussianPerturbedMetric d l k σ β 0 = 1 := by
  simp only [einastoSuperGaussianPerturbedMetric, einastoMetric_zero,
    einastoSuperGaussianCorrection_center, mul_zero, add_zero]

theorem einastoSuperGaussianPerturbedMetric_core_limit (d l k σ β : ℝ) :
    Tendsto (einastoSuperGaussianPerturbedMetric d l k σ β) (𝓝 0) (𝓝 1) := by
  simpa only [einastoSuperGaussianPerturbedMetric_center] using
    (einastoSuperGaussianPerturbedMetric_continuous d l k σ β).continuousAt.tendsto (x := 0)

theorem einastoSuperGaussianPerturbedMetric_eventually_pos (d l k σ β : ℝ) :
    ∀ᶠ t in atBot, 0 < einastoSuperGaussianPerturbedMetric d l k σ β (exp t) :=
  ((einastoSuperGaussianPerturbedMetric_core_limit d l k σ β).comp tendsto_exp_atBot).eventually
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))

theorem einastoSuperGaussianPerturbedMetric_hasDerivAt (d l k σ β t : ℝ) :
    HasDerivAt (einastoSuperGaussianPerturbedMetric d l k σ β)
      (deriv (einastoMetric d l (einastoSuperGaussianShape k)) (exp t) +
        β * deriv (einastoSuperGaussianCorrection d l k σ) (exp t)) (exp t) := by
  have hf := einastoMetric_derivative d l (einastoSuperGaussianShape k) t
  have hh := einastoSuperGaussianCorrection_hasDerivAt d l k σ t
  unfold einastoSuperGaussianPerturbedMetric
  rw [hf.deriv, hh.deriv]
  simpa only [Pi.add_def] using hf.add (hh.const_mul β)

/-- The second metric derivative is actual, obtained from proved derivatives of both summands. -/
theorem einastoSuperGaussianPerturbedMetric_second_hasDerivAt (d l k σ β t : ℝ) :
    HasDerivAt (deriv (einastoSuperGaussianPerturbedMetric d l k σ β))
      (deriv (deriv (einastoMetric d l (einastoSuperGaussianShape k))) (exp t) +
        β * deriv (deriv (einastoSuperGaussianCorrection d l k σ)) (exp t)) (exp t) := by
  have hf := einastoMetric_second_derivative d l (einastoSuperGaussianShape k) t
  have hh := einastoSuperGaussianCorrection_second_hasDerivAt d l k σ t
  rw [hf.deriv, hh.deriv]
  have h := hf.add (hh.const_mul β)
  simp only [Pi.add_def] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  have he := (einastoSuperGaussianPerturbedMetric_hasDerivAt d l k σ β (log r)).deriv
  simpa only [exp_log hr] using he

theorem einastoSuperGaussianPerturbedMetric_quadratic_limit (d l k σ β : ℝ) :
    Tendsto (fun t => (1 - einastoSuperGaussianPerturbedMetric d l k σ β (exp t)) / exp t ^ (2 : ℕ)) atBot
      (𝓝 (-einastoSuperGaussianMetricCoefficient d l k σ β)) := by
  have he : (fun t => (1 - einastoSuperGaussianPerturbedMetric d l k σ β (exp t)) / exp t ^ (2 : ℕ)) =
      (fun t => (1 - einastoMetric d l (einastoSuperGaussianShape k) (exp t)) / exp t ^ (2 : ℕ) -
        β * (einastoSuperGaussianCorrection d l k σ (exp t) / exp t ^ (2 : ℕ))) := by
    funext t
    unfold einastoSuperGaussianPerturbedMetric
    ring
  rw [he]
  have h := (einastoMetric_quadratic_core_limit d l (einastoSuperGaussianShape k)).sub
    ((einastoSuperGaussianCorrection_quadratic_limit d l k σ).const_mul β)
  have hc : 8 * Real.pi * exp d / 3 - β * einastoSuperGaussianCorrectionCoefficient d l k σ =
      -einastoSuperGaussianMetricCoefficient d l k σ β := by
    unfold einastoSuperGaussianMetricCoefficient
    ring
  rwa [hc] at h

theorem einastoSuperGaussianPerturbedMetric_scaled_derivative_limit (d l k σ β : ℝ) :
    Tendsto (fun t => deriv (einastoSuperGaussianPerturbedMetric d l k σ β) (exp t) / exp t) atBot
      (𝓝 (2 * einastoSuperGaussianMetricCoefficient d l k σ β)) := by
  have he : (fun t => deriv (einastoSuperGaussianPerturbedMetric d l k σ β) (exp t) / exp t) =
      (fun t => deriv (einastoMetric d l (einastoSuperGaussianShape k)) (exp t) / exp t +
        β * (deriv (einastoSuperGaussianCorrection d l k σ) (exp t) / exp t)) := by
    funext t
    rw [(einastoSuperGaussianPerturbedMetric_hasDerivAt d l k σ β t).deriv]
    ring
  rw [he]
  have h := (einastoMetric_scaled_first_derivative_limit d l (einastoSuperGaussianShape k)).add
    ((einastoSuperGaussianCorrection_scaled_derivative_limit d l k σ).const_mul β)
  have hc : -16 * Real.pi * exp d / 3 + β * (2 * einastoSuperGaussianCorrectionCoefficient d l k σ) =
      2 * einastoSuperGaussianMetricCoefficient d l k σ β := by
    unfold einastoSuperGaussianMetricCoefficient
    ring
  rwa [hc] at h

theorem einastoSuperGaussianPerturbedMetric_second_derivative_limit (d l k σ β : ℝ) :
    Tendsto (fun t => deriv (deriv (einastoSuperGaussianPerturbedMetric d l k σ β)) (exp t)) atBot
      (𝓝 (2 * einastoSuperGaussianMetricCoefficient d l k σ β)) := by
  have he : (fun t => deriv (deriv (einastoSuperGaussianPerturbedMetric d l k σ β)) (exp t)) =
      (fun t => deriv (deriv (einastoMetric d l (einastoSuperGaussianShape k))) (exp t) +
        β * deriv (deriv (einastoSuperGaussianCorrection d l k σ)) (exp t)) := by
    funext t
    exact (einastoSuperGaussianPerturbedMetric_second_hasDerivAt d l k σ β t).deriv
  rw [he]
  have h := (einastoMetricSecondJet_core_limit d l (einastoSuperGaussianShape k)).add
    ((einastoSuperGaussianCorrection_second_derivative_limit d l k σ).const_mul β)
  have hc : -16 * Real.pi * exp d / 3 + β * (2 * einastoSuperGaussianCorrectionCoefficient d l k σ) =
      2 * einastoSuperGaussianMetricCoefficient d l k σ β := by
    unfold einastoSuperGaussianMetricCoefficient
    ring
  rwa [hc] at h

/-- Signed Ricci curvature remains finite and is fixed by the same quadratic coefficient. -/
theorem einastoSuperGaussianPerturbedMetric_Ricci_limit (d l k σ β : ℝ) :
    Tendsto (fun t => radialRicciScalar (einastoSuperGaussianPerturbedMetric d l k σ β) (exp t)) atBot
      (𝓝 (12 * einastoSuperGaussianMetricCoefficient d l k σ β)) := by
  have he : (fun t => radialRicciScalar (einastoSuperGaussianPerturbedMetric d l k σ β) (exp t)) =
      (fun t => deriv (deriv (einastoSuperGaussianPerturbedMetric d l k σ β)) (exp t) +
        4 * (deriv (einastoSuperGaussianPerturbedMetric d l k σ β) (exp t) / exp t) -
        2 * ((1 - einastoSuperGaussianPerturbedMetric d l k σ β (exp t)) / exp t ^ (2 : ℕ))) := by
    funext t
    unfold radialRicciScalar
    field_simp
    ring
  rw [he]
  have h := ((einastoSuperGaussianPerturbedMetric_second_derivative_limit d l k σ β).add
    ((einastoSuperGaussianPerturbedMetric_scaled_derivative_limit d l k σ β).const_mul 4)).sub
    ((einastoSuperGaussianPerturbedMetric_quadratic_limit d l k σ β).const_mul 2)
  have hc : 2 * einastoSuperGaussianMetricCoefficient d l k σ β + 4 * (2 * einastoSuperGaussianMetricCoefficient d l k σ β) -
      2 * (-einastoSuperGaussianMetricCoefficient d l k σ β) = 12 * einastoSuperGaussianMetricCoefficient d l k σ β := by ring
  rwa [hc] at h

/-- Complete control of the actual Kretschmann expression, not merely of the metric value. -/
theorem einastoSuperGaussianPerturbedMetric_Kretschmann_limit (d l k σ β : ℝ) :
    Tendsto (fun t => radialKretschmannScalar (einastoSuperGaussianPerturbedMetric d l k σ β) (exp t)) atBot
      (𝓝 (24 * einastoSuperGaussianMetricCoefficient d l k σ β ^ (2 : ℕ))) := by
  unfold radialKretschmannScalar
  have h := (((einastoSuperGaussianPerturbedMetric_second_derivative_limit d l k σ β).pow 2).add
    (((einastoSuperGaussianPerturbedMetric_scaled_derivative_limit d l k σ β).pow 2).const_mul 4)).add
    (((einastoSuperGaussianPerturbedMetric_quadratic_limit d l k σ β).pow 2).const_mul 4)
  have hc : (2 * einastoSuperGaussianMetricCoefficient d l k σ β) ^ (2 : ℕ) + 4 * (2 * einastoSuperGaussianMetricCoefficient d l k σ β) ^ (2 : ℕ) +
      4 * (-einastoSuperGaussianMetricCoefficient d l k σ β) ^ (2 : ℕ) = 24 * einastoSuperGaussianMetricCoefficient d l k σ β ^ (2 : ℕ) := by ring
  rwa [hc] at h

theorem einastoSuperGaussianPerturbedMetric_Ricci_explicit (d l k σ β : ℝ) :
    Tendsto (fun t => radialRicciScalar (einastoSuperGaussianPerturbedMetric d l k σ β) (exp t)) atBot
      (𝓝 (-32 * Real.pi * exp d * einastoSuperGaussianCoreMultiplier d σ β)) := by
  have h := einastoSuperGaussianPerturbedMetric_Ricci_limit d l k σ β
  rw [einastoSuperGaussianMetricCoefficient_eq] at h
  have hc : 12 * (-8 * Real.pi * exp d / 3 * einastoSuperGaussianCoreMultiplier d σ β) =
      -32 * Real.pi * exp d * einastoSuperGaussianCoreMultiplier d σ β := by ring
  rwa [hc] at h

theorem einastoSuperGaussianPerturbedMetric_Kretschmann_explicit (d l k σ β : ℝ) :
    Tendsto (fun t => radialKretschmannScalar (einastoSuperGaussianPerturbedMetric d l k σ β) (exp t)) atBot
      (𝓝 ((512 * Real.pi ^ (2 : ℕ) * exp d ^ (2 : ℕ) / 3) * einastoSuperGaussianCoreMultiplier d σ β ^ (2 : ℕ))) := by
  have h := einastoSuperGaussianPerturbedMetric_Kretschmann_limit d l k σ β
  rw [einastoSuperGaussianMetricCoefficient_eq] at h
  have hc : 24 * (-8 * Real.pi * exp d / 3 * einastoSuperGaussianCoreMultiplier d σ β) ^ (2 : ℕ) =
      (512 * Real.pi ^ (2 : ℕ) * exp d ^ (2 : ℕ) / 3) * einastoSuperGaussianCoreMultiplier d σ β ^ (2 : ℕ) := by ring
  rwa [hc] at h

theorem einastoSuperGaussianCoreMultiplier_corrected_sign (d β : ℝ) :
    einastoSuperGaussianCoreMultiplier d 1 β = 1 := by
  unfold einastoSuperGaussianCoreMultiplier
  ring

theorem einastoSuperGaussianCoreMultiplier_appendix_sign (d β : ℝ) :
    einastoSuperGaussianCoreMultiplier d (-1) β = 1 + 128 * Real.pi * β * exp d := by
  unfold einastoSuperGaussianCoreMultiplier
  ring

/-- The corrected-sign source preserves the original central Ricci curvature at every coupling. -/
theorem einastoSuperGaussian_corrected_Ricci_preserved (d l k β : ℝ) :
    Tendsto (fun t => radialRicciScalar (einastoSuperGaussianPerturbedMetric d l k 1 β) (exp t)) atBot
      (𝓝 (-32 * Real.pi * exp d)) := by
  simpa only [einastoSuperGaussianCoreMultiplier_corrected_sign, mul_one] using
    einastoSuperGaussianPerturbedMetric_Ricci_explicit d l k 1 β

/-- Preservation of the actual curvature invariant, not only the central metric value. -/
theorem einastoSuperGaussian_corrected_Kretschmann_preserved (d l k β : ℝ) :
    Tendsto (fun t => radialKretschmannScalar (einastoSuperGaussianPerturbedMetric d l k 1 β) (exp t)) atBot
      (𝓝 (512 * Real.pi ^ (2 : ℕ) * exp d ^ (2 : ℕ) / 3)) := by
  simpa only [einastoSuperGaussianCoreMultiplier_corrected_sign, one_pow, mul_one] using
    einastoSuperGaussianPerturbedMetric_Kretschmann_explicit d l k 1 β

theorem einastoSuperGaussianCoreMultiplier_appendix_gt_one (d b : ℝ) :
    1 < einastoSuperGaussianCoreMultiplier d (-1) (exp b) := by
  rw [einastoSuperGaussianCoreMultiplier_appendix_sign]
  have h : 0 < 128 * Real.pi * exp b * exp d := by positivity
  linarith

/-- With the literal appendix sign, every positive coupling strictly increases finite central curvature. -/
theorem einastoSuperGaussian_appendix_core_growth (d l k b : ℝ) :
    ∃ K : ℝ, Tendsto (fun t => radialKretschmannScalar (einastoSuperGaussianPerturbedMetric d l k (-1) (exp b)) (exp t)) atBot (𝓝 K) ∧
      512 * Real.pi ^ (2 : ℕ) * exp d ^ (2 : ℕ) / 3 < K := by
  refine ⟨(512 * Real.pi ^ (2 : ℕ) * exp d ^ (2 : ℕ) / 3) * einastoSuperGaussianCoreMultiplier d (-1) (exp b) ^ (2 : ℕ),
    einastoSuperGaussianPerturbedMetric_Kretschmann_explicit d l k (-1) (exp b), ?_⟩
  have h := einastoSuperGaussianCoreMultiplier_appendix_gt_one d b
  have hp : 0 < 512 * Real.pi ^ (2 : ℕ) * exp d ^ (2 : ℕ) / 3 := by positivity
  have hs : 1 < einastoSuperGaussianCoreMultiplier d (-1) (exp b) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (einastoSuperGaussianCoreMultiplier d (-1) (exp b) - 1)]
  have hm := mul_pos hp (sub_pos.mpr hs)
  nlinarith

end GaloisForLFunctions.HTGeometry
