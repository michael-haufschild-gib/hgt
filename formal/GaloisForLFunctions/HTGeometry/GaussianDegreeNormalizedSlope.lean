import GaloisForLFunctions.HTGeometry.GaussianVerticalRadiusMonotonicity
import GaloisForLFunctions.HTGeometry.GaussianPolynomialParabolicDefect

/-!
# Polynomial degree growth of the full coordinate-weighted phase slope

A degree-independent envelope bounds the squared slope after normalization by
(d+3)²√(d+3). This gives polynomial rather than factorial degree dependence.
-/

open scoped Real NNReal
noncomputable section

namespace GaloisForLFunctions

/-- The degree weight required by the complete coordinate-error slope. -/
def gaussianDegreeWeight (d : ℕ) : ℝ := ((d : ℝ) + 3) ^ 2 * Real.sqrt ((d : ℝ) + 3)

theorem gaussianDegreeWeight_pos (d : ℕ) : 0 < gaussianDegreeWeight d := by
  unfold gaussianDegreeWeight
  positivity

theorem sqrt_le_gaussianDegreeWeight (d : ℕ) :
    Real.sqrt ((d : ℝ) + 3) ≤ gaussianDegreeWeight d := by
  have hd : 1 ≤ ((d : ℝ) + 3) ^ 2 := by nlinarith only [Nat.cast_nonneg (α := ℝ) d]
  exact le_mul_of_one_le_left (Real.sqrt_nonneg _) hd

theorem one_le_gaussianDegreeWeight (d : ℕ) : 1 ≤ gaussianDegreeWeight d :=
  (Real.one_le_sqrt.mpr (by linarith only [Nat.cast_nonneg (α := ℝ) d])).trans
    (sqrt_le_gaussianDegreeWeight d)

/-- A degree-independent envelope for the first vertical slope. -/
def normalizedGaussianVerticalSlope (ε : ℝ) : ℝ :=
  Real.exp (π * ε ^ 2) *
    (Real.sqrt (4 * π) * Real.exp (|ε| * Real.sqrt (4 * π)) + Real.sqrt (4 * π) + π * |ε|)

/-- A degree-independent envelope for the coordinate-weighted slope. -/
def gaussianNormalizedSlopeEnvelope (ε : ℝ) : ℝ :=
  normalizedGaussianVerticalSlope ε * (Real.sqrt (4 * π) / (2 * π)) +
    Real.exp (π * ε ^ 2) * (Real.exp (|ε| * Real.sqrt (4 * π)) + |ε| * Real.sqrt (4 * π))

theorem normalizedGaussianVerticalSlope_nonneg (ε : ℝ) :
    0 ≤ normalizedGaussianVerticalSlope ε := by unfold normalizedGaussianVerticalSlope; positivity

theorem gaussianNormalizedSlopeEnvelope_nonneg (ε : ℝ) :
    0 ≤ gaussianNormalizedSlopeEnvelope ε := by
  unfold gaussianNormalizedSlopeEnvelope
  have h := normalizedGaussianVerticalSlope_nonneg ε
  positivity

theorem continuous_gaussianNormalizedSlopeEnvelope : Continuous gaussianNormalizedSlopeEnvelope := by
  unfold gaussianNormalizedSlopeEnvelope normalizedGaussianVerticalSlope
  fun_prop

/-- The complete defect is degree-independent at the polynomial degree scale. -/
theorem verticalPolynomialGaussianDefect_degreeWeight_le (d : ℕ) (ε : ℝ≥0) :
    verticalPolynomialGaussianDefect d ((ε : ℝ) / gaussianDegreeWeight d) ≤
      parabolicGaussianDefect ε := by
  have hroot : Real.sqrt ((d : ℝ) + 1) ≤ gaussianDegreeWeight d :=
    (Real.sqrt_le_sqrt (by linarith)).trans (sqrt_le_gaussianDegreeWeight d)
  have hrpos : 0 < Real.sqrt ((d : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  let R : ℝ≥0 := ⟨(ε : ℝ) / gaussianDegreeWeight d, div_nonneg ε.coe_nonneg (gaussianDegreeWeight_pos d).le⟩
  let S : ℝ≥0 := ⟨(ε : ℝ) / Real.sqrt ((d : ℝ) + 1), div_nonneg ε.coe_nonneg hrpos.le⟩
  have hrs : R ≤ S := div_le_div_of_nonneg_left ε.coe_nonneg hrpos hroot
  exact (verticalPolynomialGaussianDefect_radius_mono d hrs).trans
    (verticalPolynomialGaussianDefect_parabolic_le d ε)

/-- The first slope costs only one square root of degree after normalization. -/
theorem gaussianVerticalDefectSlope_degreeWeight_le (d : ℕ) (ε : ℝ≥0) :
    gaussianVerticalDefectSlope (d + 1) ((ε : ℝ) / gaussianDegreeWeight d) ≤
      Real.sqrt ((d : ℝ) + 3) * normalizedGaussianVerticalSlope ε := by
  let v := Real.sqrt ((d : ℝ) + 3)
  let A := Real.sqrt (4 * π)
  let R := (ε : ℝ) / gaussianDegreeWeight d
  have hv1 : 1 ≤ v := Real.one_le_sqrt.mpr (by linarith only [Nat.cast_nonneg (α := ℝ) d])
  have hvw : v ≤ gaussianDegreeWeight d := sqrt_le_gaussianDegreeWeight d
  have hR0 : 0 ≤ R := div_nonneg ε.coe_nonneg (gaussianDegreeWeight_pos d).le
  have hR : R ≤ (ε : ℝ) := div_le_self ε.coe_nonneg (one_le_gaussianDegreeWeight d)
  have hRv : R * v ≤ (ε : ℝ) := by
    dsimp only [R]
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ (gaussianDegreeWeight_pos d)).mpr
      (mul_le_mul_of_nonneg_left hvw ε.coe_nonneg)
  have hA₀ : Real.sqrt (4 * π * ((d + 1 : ℕ) : ℝ)) ≤ A * v := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 4 * π)]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    exact Real.sqrt_le_sqrt (by simp only [Nat.cast_add, Nat.cast_one]; linarith)
  have hA₁ : Real.sqrt (4 * π * (((d + 1 : ℕ) : ℝ) + 1)) ≤ A * v := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 4 * π)]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    exact Real.sqrt_le_sqrt (by simp only [Nat.cast_add, Nat.cast_one]; linarith)
  have harg : R * Real.sqrt (4 * π * ((d + 1 : ℕ) : ℝ)) ≤ (ε : ℝ) * A := by
    have h₀ := mul_le_mul_of_nonneg_left hA₀ hR0
    have h₁ := mul_le_mul_of_nonneg_right hRv (Real.sqrt_nonneg (4 * π))
    nlinarith only [h₀, h₁]
  have hg := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hR0 hR 2) Real.pi_pos.le)
  have hp := mul_le_mul hA₀ (Real.exp_le_exp.mpr harg) (Real.exp_pos _).le (by positivity)
  have hπ : π * R ≤ v * (π * (ε : ℝ)) := by
    have h₀ := mul_le_mul_of_nonneg_left hR Real.pi_pos.le
    have h₁ := le_mul_of_one_le_left (mul_nonneg Real.pi_pos.le ε.coe_nonneg) hv1
    exact h₀.trans h₁
  have hbody : Real.sqrt (4 * π * ((d + 1 : ℕ) : ℝ)) *
        Real.exp (R * Real.sqrt (4 * π * ((d + 1 : ℕ) : ℝ))) +
      Real.sqrt (4 * π * (((d + 1 : ℕ) : ℝ) + 1)) + π * R ≤
      v * (A * Real.exp ((ε : ℝ) * A) + A + π * (ε : ℝ)) := by
    nlinarith only [hp, hA₁, hπ]
  have hfull := mul_le_mul hg hbody (by positivity) (Real.exp_pos _).le
  unfold gaussianVerticalDefectSlope normalizedGaussianVerticalSlope
  rw [abs_of_nonneg ε.coe_nonneg]
  change Real.exp (π * R ^ 2) * _ ≤ v * (Real.exp (π * (ε : ℝ) ^ 2) * _)
  nlinarith only [hfull]

/-- The squared full slope grows at most as the degree weight, uniformly in coefficients. -/
theorem gaussianCoordinateVerticalSlope_degreeWeight_sq_le (d : ℕ) (ε : ℝ≥0) :
    gaussianCoordinateVerticalSlope d ((ε : ℝ) / gaussianDegreeWeight d) ^ 2 ≤
      (1 + 2 * Real.sqrt (4 * π)) * gaussianDegreeWeight d * gaussianNormalizedSlopeEnvelope ε ^ 2 := by
  let v := Real.sqrt ((d : ℝ) + 3)
  let A := Real.sqrt (4 * π)
  let C := gaussianStripSamplingFactor (d + 1) 1
  let R : ℝ≥0 := ⟨(ε : ℝ) / gaussianDegreeWeight d,
    div_nonneg ε.coe_nonneg (gaussianDegreeWeight_pos d).le⟩
  let F := Real.exp (π * (ε : ℝ) ^ 2) *
    (Real.exp ((ε : ℝ) * A) + (ε : ℝ) * A)
  have hv1 : 1 ≤ v := Real.one_le_sqrt.mpr (by linarith only [Nat.cast_nonneg (α := ℝ) d])
  have hv2 : v ^ 2 = (d : ℝ) + 3 := Real.sq_sqrt (by positivity)
  have hC : 0 ≤ C := gaussianStripSamplingFactor_nonneg _ _
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hF : 0 ≤ F := by positivity
  have hL := gaussianVerticalDefectSlope_degreeWeight_le d ε
  have hE : verticalPolynomialGaussianDefect d R + 1 ≤ F := by
    have ht := verticalPolynomialGaussianDefect_degreeWeight_le d ε
    unfold parabolicGaussianDefect at ht
    rw [abs_of_nonneg ε.coe_nonneg] at ht
    change verticalPolynomialGaussianDefect d R ≤ F - 1 at ht
    linarith only [ht]
  have hAdeg : Real.sqrt (4 * π * ((d : ℝ) + 1)) / (2 * π) ≤ A * v / (2 * π) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [Real.sqrt_mul (by positivity : 0 ≤ 4 * π)]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hA
  have hfirst := mul_le_mul (mul_le_mul_of_nonneg_left hL hC) hAdeg
    (by positivity) (mul_nonneg hC (mul_nonneg (Real.sqrt_nonneg _)
      (normalizedGaussianVerticalSlope_nonneg _)))
  have hsecond := mul_le_mul (gaussianStripSamplingFactor_mono 1 (Nat.le_succ d)) hE
    (add_nonneg (verticalPolynomialGaussianDefect_nonneg _ _) (by positivity)) hC
  change C * gaussianVerticalDefectSlope (d + 1) R *
      (Real.sqrt (4 * π * ((d : ℝ) + 1)) / (2 * π)) ≤
    C * (v * normalizedGaussianVerticalSlope ε) * (A * v / (2 * π)) at hfirst
  change gaussianStripSamplingFactor d 1 * (verticalPolynomialGaussianDefect d R + 1) ≤
    C * F at hsecond
  have hFscale : C * F ≤ C * (v ^ 2 * F) := by
    apply mul_le_mul_of_nonneg_left _ hC
    exact le_mul_of_one_le_left hF (by nlinarith only [hv1])
  have hT : gaussianCoordinateVerticalSlope d R ≤ C * ((d : ℝ) + 3) *
      gaussianNormalizedSlopeEnvelope ε := by
    unfold gaussianCoordinateVerticalSlope gaussianNormalizedSlopeEnvelope
    rw [abs_of_nonneg ε.coe_nonneg]
    change C * gaussianVerticalDefectSlope (d + 1) R * _ +
      gaussianStripSamplingFactor d 1 * (verticalPolynomialGaussianDefect d R + 1) ≤
      C * ((d : ℝ) + 3) * (normalizedGaussianVerticalSlope ε * (A / (2 * π)) + F)
    rw [← hv2]
    calc
      _ ≤ C * (v * normalizedGaussianVerticalSlope ε) * (A * v / (2 * π)) + C * F :=
        add_le_add hfirst hsecond
      _ ≤ C * (v * normalizedGaussianVerticalSlope ε) * (A * v / (2 * π)) + C * (v ^ 2 * F) :=
        add_le_add le_rfl hFscale
      _ = _ := by ring
  have hC2 : C ^ 2 ≤ (1 + 2 * A) * v := by
    dsimp only [C]
    rw [gaussianStripSamplingFactor, Real.sq_sqrt (by positivity)]
    simp only [NNReal.coe_one, Nat.cast_add, Nat.cast_one, mul_one]
    rw [show (d : ℝ) + 1 + 2 = (d : ℝ) + 3 by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 4 * π)]
    change 1 + 2 * (A * v) ≤ (1 + 2 * A) * v
    nlinarith only [hv1]
  have hs := pow_le_pow_left₀ (gaussianCoordinateVerticalSlope_nonneg d R) hT 2
  rw [mul_pow, mul_pow] at hs
  have hc := mul_le_mul_of_nonneg_right hC2
    (mul_nonneg (sq_nonneg ((d : ℝ) + 3)) (sq_nonneg (gaussianNormalizedSlopeEnvelope ε)))
  change gaussianCoordinateVerticalSlope d R ^ 2 ≤ _
  unfold gaussianDegreeWeight
  nlinarith only [hs, hc]

end GaloisForLFunctions
