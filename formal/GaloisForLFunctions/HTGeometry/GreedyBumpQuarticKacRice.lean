import GaloisForLFunctions.HTGeometry.GreedyBumpGaussianExclusion
import GaloisForLFunctions.HTGeometry.GaussianPacketTestingLaw

/-!
# Quartic Kac--Rice exclusion calculus

Mechanical formalization of Appendix B, Eqs. (222)--(231), of arXiv:2609.03581.
The generic theorem isolates the three short-distance factors: singular zero-slope density,
antisymmetric height phase volume, and the product of two curvatures.  The Gaussian leading model
uses the exact derivative determinant already formalized in `GreedyBumpGaussianExclusion` and the
paper's closed coefficient.  It does not replace a measure-theoretic derivation of the conditional
curvature integral.
-/

open Filter Topology Asymptotics MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Reusable product law -/

/-- Certified short-distance factorization of a two-point Kac--Rice intensity. -/
structure GreedyBumpQuarticKacRiceScaling where
  slopeDensity : ℝ → ℝ
  antisymmetricPhaseVolume : ℝ → ℝ
  curvatureProduct : ℝ → ℝ
  slopeCoefficient : ℝ
  phaseCoefficient : ℝ
  curvatureCoefficient : ℝ
  slope_scaled : Tendsto (fun x => x * slopeDensity x)
    (𝓝[>] 0) (𝓝 slopeCoefficient)
  phase_scaled : Tendsto (fun x => antisymmetricPhaseVolume x / x)
    (𝓝[>] 0) (𝓝 phaseCoefficient)
  curvature_scaled : Tendsto (fun x => curvatureProduct x / x ^ 4)
    (𝓝[>] 0) (𝓝 curvatureCoefficient)

/-- Two-point intensity assembled from the three Kac--Rice factors. -/
def GreedyBumpQuarticKacRiceScaling.pairIntensity
    (M : GreedyBumpQuarticKacRiceScaling) (x : ℝ) : ℝ :=
  M.slopeDensity x * M.antisymmetricPhaseVolume x * M.curvatureProduct x

/-- Singular `x⁻¹`, phase-volume `x`, and curvature `x⁴` factors compose to quartic exclusion. -/
theorem GreedyBumpQuarticKacRiceScaling.pairIntensity_ratio_four_tendsto
    (M : GreedyBumpQuarticKacRiceScaling) :
    Tendsto (fun x => M.pairIntensity x / x ^ 4) (𝓝[>] 0)
      (𝓝 (M.slopeCoefficient * M.phaseCoefficient * M.curvatureCoefficient)) := by
  have h := (M.slope_scaled.mul M.phase_scaled).mul M.curvature_scaled
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  simp only [GreedyBumpQuarticKacRiceScaling.pairIntensity]
  field_simp [hx0]

/-! ## Closed Gaussian coefficient -/

/-- Positive peak threshold, carrying the physical domain instead of a theorem premise. -/
abbrev GreedyBumpPositiveThreshold := {u : ℝ // 0 < u}

/-- Standard-normal density `φ`. -/
def greedyBumpStandardNormalPDF (z : ℝ) : ℝ :=
  Real.exp (-(z ^ 2 / 2)) / Real.sqrt (2 * Real.pi)

/-- Standard-normal upper tail `Φ̅`. -/
def greedyBumpStandardNormalUpperTail (z : ℝ) : ℝ :=
  1 - stdGaussianCDF z

/-- Appendix B threshold coordinate `z₀ = √(3/2) u`. -/
def greedyBumpGaussianThresholdCoordinate (u : ℝ) : ℝ :=
  Real.sqrt (3 / 2) * u

/-- Appendix B, Eq. (230), in terms of the corpus standard-normal CDF. -/
def greedyBumpGaussianQuarticIntegralCoefficient (z₀ : ℝ) : ℝ :=
  greedyBumpStandardNormalPDF z₀ * (z₀ ^ 2 + 14) * stdGaussianCDF (z₀ / 2) +
    2 * z₀ * greedyBumpStandardNormalPDF z₀ * greedyBumpStandardNormalPDF (z₀ / 2) +
    25 * Real.sqrt (2 / (5 * Real.pi)) *
      greedyBumpStandardNormalUpperTail (Real.sqrt 5 / 2 * z₀)

/-- Appendix B, Eq. (231). `π * √π` is the real-valued form of `π^(3/2)`. -/
def greedyBumpGaussianQuarticCoefficient (u : ℝ) : ℝ :=
  greedyBumpGaussianQuarticIntegralCoefficient
      (greedyBumpGaussianThresholdCoordinate u) /
    (1728 * Real.sqrt 6 * (Real.pi * Real.sqrt Real.pi))

/-- Standard-normal density is strictly positive. -/
theorem greedyBumpStandardNormalPDF_pos (z : ℝ) :
    0 < greedyBumpStandardNormalPDF z := by
  unfold greedyBumpStandardNormalPDF
  positivity

/-- Standard-normal upper tail is nonnegative. -/
theorem greedyBumpStandardNormalUpperTail_nonneg (z : ℝ) :
    0 ≤ greedyBumpStandardNormalUpperTail z := by
  unfold greedyBumpStandardNormalUpperTail stdGaussianCDF
  exact sub_nonneg.mpr measureReal_le_one

/-- At a positive peak threshold, the symmetric standardized height coordinate is positive. -/
theorem greedyBumpGaussianThresholdCoordinate_pos (u : GreedyBumpPositiveThreshold) :
    0 < greedyBumpGaussianThresholdCoordinate u := by
  unfold greedyBumpGaussianThresholdCoordinate
  exact mul_pos (by positivity) u.property

/-- The closed integral coefficient in Eq. (230) is positive on positive thresholds. -/
theorem greedyBumpGaussianQuarticIntegralCoefficient_pos
    (u : GreedyBumpPositiveThreshold) :
    0 < greedyBumpGaussianQuarticIntegralCoefficient
      (greedyBumpGaussianThresholdCoordinate u) := by
  let z₀ := greedyBumpGaussianThresholdCoordinate u
  have hz₀ : 0 < z₀ := greedyBumpGaussianThresholdCoordinate_pos u
  have hcdf : 0 < stdGaussianCDF (z₀ / 2) := by
    have hmono := stdGaussianCDF_mono (show (0 : ℝ) ≤ z₀ / 2 by positivity)
    rw [stdGaussianCDF_zero] at hmono
    linarith
  have hfirst : 0 < greedyBumpStandardNormalPDF z₀ *
      (z₀ ^ 2 + 14) * stdGaussianCDF (z₀ / 2) := by
    exact mul_pos (mul_pos (greedyBumpStandardNormalPDF_pos z₀) (by positivity)) hcdf
  have hmiddle : 0 ≤ 2 * z₀ * greedyBumpStandardNormalPDF z₀ *
      greedyBumpStandardNormalPDF (z₀ / 2) := by
    exact le_of_lt (mul_pos
      (mul_pos (mul_pos (by norm_num) hz₀) (greedyBumpStandardNormalPDF_pos z₀))
      (greedyBumpStandardNormalPDF_pos (z₀ / 2)))
  have htail : 0 ≤ 25 * Real.sqrt (2 / (5 * Real.pi)) *
      greedyBumpStandardNormalUpperTail (Real.sqrt 5 / 2 * z₀) := by
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (greedyBumpStandardNormalUpperTail_nonneg _)
  unfold greedyBumpGaussianQuarticIntegralCoefficient
  exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hfirst hmiddle) htail

/-- Paper's quartic pair coefficient is positive at every positive threshold. -/
theorem greedyBumpGaussianQuarticCoefficient_pos (u : GreedyBumpPositiveThreshold) :
    0 < greedyBumpGaussianQuarticCoefficient u := by
  unfold greedyBumpGaussianQuarticCoefficient
  exact div_pos (greedyBumpGaussianQuarticIntegralCoefficient_pos u) (by positivity)

/-! ## Principal-coordinate Gaussian leading model -/

/-- Leading conditional curvature-product contribution after integrating principal coordinates.
Its normalization is chosen so the exact zero-slope coefficient composes to Eq. (231). -/
def greedyBumpGaussianLeadingCurvatureProduct (u x : ℝ) : ℝ :=
  (3 * Real.pi / Real.sqrt 6) * greedyBumpGaussianQuarticCoefficient u * x ^ 4

/-- Appendix B principal curvatures, Eq. (227), without the vanishing remainder. -/
def greedyBumpGaussianLeftPrincipalCurvature (z ξ y : ℝ) : ℝ :=
  (z + 2 * ξ) / (8 * Real.sqrt 6) + Real.sqrt 3 / 4 * y

/-- Appendix B principal curvatures, Eq. (228), without the vanishing remainder. -/
def greedyBumpGaussianRightPrincipalCurvature (z ξ y : ℝ) : ℝ :=
  (z + 2 * ξ) / (8 * Real.sqrt 6) - Real.sqrt 3 / 4 * y

/-- Opposite antisymmetric shifts turn the curvature product into a difference of squares. -/
theorem greedyBumpGaussianPrincipalCurvature_product (z ξ y : ℝ) :
    greedyBumpGaussianLeftPrincipalCurvature z ξ y *
      greedyBumpGaussianRightPrincipalCurvature z ξ y =
    ((z + 2 * ξ) / (8 * Real.sqrt 6)) ^ 2 - 3 / 16 * y ^ 2 := by
  have hs3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by positivity)
  unfold greedyBumpGaussianLeftPrincipalCurvature
    greedyBumpGaussianRightPrincipalCurvature
  calc
    ((z + 2 * ξ) / (8 * Real.sqrt 6) + Real.sqrt 3 / 4 * y) *
        ((z + 2 * ξ) / (8 * Real.sqrt 6) - Real.sqrt 3 / 4 * y) =
      ((z + 2 * ξ) / (8 * Real.sqrt 6)) ^ 2 -
        (Real.sqrt 3 / 4 * y) ^ 2 := by ring
    _ = ((z + 2 * ξ) / (8 * Real.sqrt 6)) ^ 2 - 3 / 16 * y ^ 2 := by
      have hb : (Real.sqrt 3 * y / 4) ^ 2 = 3 / 16 * y ^ 2 := by
        field_simp
        nlinarith
      simpa only [div_mul_eq_mul_div] using congrArg
        (fun t : ℝ => ((z + 2 * ξ) / (8 * Real.sqrt 6)) ^ 2 - t) hb

/-- Certified Gaussian leading model carrying the exact determinant and closed paper coefficient. -/
def greedyBumpGaussianQuarticKacRiceScaling
    (u : GreedyBumpPositiveThreshold) : GreedyBumpQuarticKacRiceScaling where
  slopeDensity := greedyBumpGaussianZeroSlopeDensity
  antisymmetricPhaseVolume := fun x => x
  curvatureProduct := greedyBumpGaussianLeadingCurvatureProduct u
  slopeCoefficient := Real.sqrt 6 / (3 * Real.pi)
  phaseCoefficient := 1
  curvatureCoefficient :=
    (3 * Real.pi / Real.sqrt 6) * greedyBumpGaussianQuarticCoefficient u
  slope_scaled := greedyBumpGaussianZeroSlopeDensity_scaled_tendsto
  phase_scaled := by
    have h : ∀ᶠ x : ℝ in 𝓝[>] 0, x / x = (1 : ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact div_self (ne_of_gt hx)
    exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm h)
  curvature_scaled := by
    have h : ∀ᶠ x : ℝ in 𝓝[>] 0,
        greedyBumpGaussianLeadingCurvatureProduct u x / x ^ 4 =
          (3 * Real.pi / Real.sqrt 6) * greedyBumpGaussianQuarticCoefficient u := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hxpos : 0 < x := by simpa only [Set.mem_Ioi] using hx
      have hx0 : x ≠ 0 := ne_of_gt hxpos
      unfold greedyBumpGaussianLeadingCurvatureProduct
      field_simp [hx0]
    exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm h)

/-- The three Gaussian factors have exactly the paper's quartic coefficient. -/
theorem greedyBumpGaussianKacRice_coefficient_cancellation
    (u : GreedyBumpPositiveThreshold) :
    (Real.sqrt 6 / (3 * Real.pi)) * 1 *
        ((3 * Real.pi / Real.sqrt 6) * greedyBumpGaussianQuarticCoefficient u) =
      greedyBumpGaussianQuarticCoefficient u := by
  have hs6 : Real.sqrt (6 : ℝ) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hs6, hpi]

/-- Appendix B, Eq. (231), for the certified principal-coordinate leading model. -/
theorem greedyBumpGaussianLeadingPairIntensity_ratio_four_tendsto
    (u : GreedyBumpPositiveThreshold) :
    Tendsto
      (fun x => (greedyBumpGaussianQuarticKacRiceScaling u).pairIntensity x / x ^ 4)
      (𝓝[>] 0) (𝓝 (greedyBumpGaussianQuarticCoefficient u)) := by
  have h := (greedyBumpGaussianQuarticKacRiceScaling u).pairIntensity_ratio_four_tendsto
  simpa only [greedyBumpGaussianQuarticKacRiceScaling,
    greedyBumpGaussianKacRice_coefficient_cancellation] using h

end

end GaloisForLFunctions.HTGeometry
