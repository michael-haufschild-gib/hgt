import GaloisForLFunctions.RHTower.ConstrainedProlateWeilToeplitzSchur
import GaloisForLFunctions.RHTower.ConstrainedProlateTrueApertureMetric
import GaloisForLFunctions.RHTower.ThetaCuspSchwartzFourierXi

/-!
# The constrained-prolate true-aperture Xi moment metric

The true CCM aperture denominator is the Hilbert Gram of the summation-map images, not the
additive source Gram.  At the fixed-Hermite endpoint, the ground constrained contrast is an exact
scalar multiple of the existing theta-cusp seed, hence its logarithmic integer sum has Fourier
transform equal to the same scalar multiple of `XiC`.

This file formalizes that source-specific identification and the algebraic first two rows of the
fixed-Hermite Xi-square polynomial moment target.  For normalized formal moment parameters, its
two-by-two determinant reduces to

```text
512 / 199395 * (M₀ M₂ - M₁²).
```

It also inserts the candidate fixed-Hermite ground normalization into the already formalized
regular Weil--Toeplitz Schur coefficient.

No declaration asserts convergence of finite prolate aperture Grams to this metric.  That passage
requires the separate zeta-graph/PSWF rate isolated on the paper card.  No closed-Weil defect,
spectral-floor, or RH hypothesis is used here.
-/

open scoped BigOperators FourierTransform SchwartzMap

namespace RHTower

noncomputable section

/-! ## The exact limiting ground source -/

/-- Scalar relating the source-normalized limiting CCM ground contrast to `thetaCuspSeed`. -/
def constrainedProlateGroundHermiteXiScale : ℝ :=
  -(4 * Real.sqrt (Real.sqrt 2) / Real.sqrt 33)

/-- The normalized `h₀-h₄` Hermite-limit seed in physical coordinates. -/
def constrainedProlateGroundHermiteSeed (x : ℝ) : ℝ :=
  (Real.sqrt (Real.sqrt 2) * 8 * Real.pi / Real.sqrt 33) *
    x ^ 2 * (3 - 2 * Real.pi * x ^ 2) * Real.exp (-Real.pi * x ^ 2)

/-- The constrained ground Hermite seed is exactly the theta-cusp seed, with the source
normalization forced by the `8/11` contrast. -/
theorem constrainedProlateGroundHermiteSeed_eq_thetaCuspSeed (x : ℝ) :
    constrainedProlateGroundHermiteSeed x =
      constrainedProlateGroundHermiteXiScale * thetaCuspSeed x := by
  unfold constrainedProlateGroundHermiteSeed constrainedProlateGroundHermiteXiScale thetaCuspSeed
  ring

/-- One logarithmic integer-summation term of the limiting constrained ground source. -/
def constrainedProlateGroundHermiteSourceTerm (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (x / 2) *
    constrainedProlateGroundHermiteSeed ((n : ℝ) * Real.exp x)

theorem constrainedProlateGroundHermiteSourceTerm_eq (x : ℝ) (n : ℕ) :
    constrainedProlateGroundHermiteSourceTerm x n =
      constrainedProlateGroundHermiteXiScale * thetaCuspSourceTerm x n := by
  rw [constrainedProlateGroundHermiteSourceTerm, thetaCuspSourceTerm,
    constrainedProlateGroundHermiteSeed_eq_thetaCuspSeed]
  ring

theorem summable_constrainedProlateGroundHermiteSourceTerm (x : ℝ) :
    Summable (constrainedProlateGroundHermiteSourceTerm x) := by
  apply ((summable_thetaCuspSourceTerm x).mul_left
    constrainedProlateGroundHermiteXiScale).congr
  intro n
  exact (constrainedProlateGroundHermiteSourceTerm_eq x n).symm

/-- The full logarithmic integer sum of the limiting constrained ground Hermite seed. -/
def constrainedProlateGroundHermiteFullSource (x : ℝ) : ℝ :=
  ∑' n : ℕ, constrainedProlateGroundHermiteSourceTerm x n

/-- Exact source identification with the already constructed theta-cusp Schwartz source. -/
theorem constrainedProlateGroundHermiteFullSource_eq (x : ℝ) :
    constrainedProlateGroundHermiteFullSource x =
      constrainedProlateGroundHermiteXiScale * thetaCuspFullSource x := by
  rw [constrainedProlateGroundHermiteFullSource, thetaCuspFullSource]
  calc
    (∑' n : ℕ, constrainedProlateGroundHermiteSourceTerm x n) =
        ∑' n : ℕ, constrainedProlateGroundHermiteXiScale * thetaCuspSourceTerm x n :=
      tsum_congr (constrainedProlateGroundHermiteSourceTerm_eq x)
    _ = constrainedProlateGroundHermiteXiScale *
        ∑' n : ℕ, thetaCuspSourceTerm x n := tsum_mul_left

/-- The limiting constrained ground source as an actual complex Schwartz function. -/
def constrainedProlateGroundHermiteSchwartz : 𝓢(ℝ, ℂ) :=
  (constrainedProlateGroundHermiteXiScale : ℂ) • thetaCuspSchwartz

@[simp] theorem constrainedProlateGroundHermiteSchwartz_apply (x : ℝ) :
    constrainedProlateGroundHermiteSchwartz x =
      (constrainedProlateGroundHermiteFullSource x : ℂ) := by
  rw [constrainedProlateGroundHermiteSchwartz, constrainedProlateGroundHermiteFullSource_eq]
  simp [Complex.ofReal_mul]

/-- Exact Xi transform of the source-normalized limiting constrained ground vector. -/
theorem fourier_constrainedProlateGroundHermiteSchwartz_scaled (t : ℝ) :
    (𝓕 constrainedProlateGroundHermiteSchwartz) (t / (2 * Real.pi)) =
      (constrainedProlateGroundHermiteXiScale : ℂ) * XiC (t : ℂ) := by
  rw [constrainedProlateGroundHermiteSchwartz, FourierTransform.fourier_smul,
    SchwartzMap.smul_apply, fourier_thetaCuspSchwartz_scaled]
  rfl

/-! ## The first two Xi-square moment metric rows -/

/-- Squared constant polynomial `R₀²=16/33` in the source-orthonormal ground channel. -/
def constrainedProlateXiApertureR0Sq : ℝ := 16 / 33

/-- Squared leading coefficient of
`R₁(u)=sqrt(2/731115) * (401-44u)`. -/
def constrainedProlateXiApertureR1Sq : ℝ := 2 / 731115

def constrainedProlateXiApertureFirstPolynomialMoment (M0 M1 : ℝ) : ℝ :=
  401 * M0 - 44 * M1

def constrainedProlateXiApertureFirstPolynomialSqMoment
    (M0 M1 M2 : ℝ) : ℝ :=
  160801 * M0 - 35288 * M1 + 1936 * M2

/-- Ground entry of the fixed-Hermite Xi-moment target, with `M0` already normalized as on the
paper card. -/
def constrainedProlateXiApertureMetric00 (M0 : ℝ) : ℝ :=
  constrainedProlateXiApertureR0Sq * M0

/-- Adjacent entry of the candidate true aperture metric.  Independent source orientations change
only its sign and leave every determinant below unchanged. -/
def constrainedProlateXiApertureMetric01 (M0 M1 : ℝ) : ℝ :=
  Real.sqrt (constrainedProlateXiApertureR0Sq * constrainedProlateXiApertureR1Sq) *
    constrainedProlateXiApertureFirstPolynomialMoment M0 M1

/-- First excited diagonal entry of the candidate true aperture metric. -/
def constrainedProlateXiApertureMetric11 (M0 M1 M2 : ℝ) : ℝ :=
  constrainedProlateXiApertureR1Sq *
    constrainedProlateXiApertureFirstPolynomialSqMoment M0 M1 M2

/-- Determinant of the first two true-aperture Xi moment channels. -/
def constrainedProlateXiApertureMetricDet (M0 M1 M2 : ℝ) : ℝ :=
  constrainedProlateXiApertureMetric00 M0 *
      constrainedProlateXiApertureMetric11 M0 M1 M2 -
    constrainedProlateXiApertureMetric01 M0 M1 ^ 2

/-- Exact source-specific determinant reduction to the strict Xi-square Hankel variance. -/
theorem constrainedProlateXiApertureMetricDet_eq (M0 M1 M2 : ℝ) :
    constrainedProlateXiApertureMetricDet M0 M1 M2 =
      (512 / 199395 : ℝ) * (M0 * M2 - M1 ^ 2) := by
  have hsqrt :
      Real.sqrt
          (constrainedProlateXiApertureR0Sq * constrainedProlateXiApertureR1Sq) ^ 2 =
        constrainedProlateXiApertureR0Sq * constrainedProlateXiApertureR1Sq := by
    rw [Real.sq_sqrt]
    unfold constrainedProlateXiApertureR0Sq constrainedProlateXiApertureR1Sq
    positivity
  unfold constrainedProlateXiApertureMetricDet constrainedProlateXiApertureMetric00
    constrainedProlateXiApertureMetric01 constrainedProlateXiApertureMetric11
    constrainedProlateXiApertureFirstPolynomialMoment
    constrainedProlateXiApertureFirstPolynomialSqMoment
  rw [mul_pow, hsqrt]
  unfold constrainedProlateXiApertureR0Sq constrainedProlateXiApertureR1Sq
  ring

/-- A strict moment-variance hypothesis makes the symbolic first two target channels
nondegenerate. -/
theorem constrainedProlateXiApertureMetricDet_pos
    {M0 M1 M2 : ℝ} (hvariance : M1 ^ 2 < M0 * M2) :
    0 < constrainedProlateXiApertureMetricDet M0 M1 M2 := by
  rw [constrainedProlateXiApertureMetricDet_eq]
  exact mul_pos (by norm_num) (sub_pos.mpr hvariance)

theorem constrainedProlateXiApertureMetric00_pos
    {M0 : ℝ} (hM0 : 0 < M0) :
    0 < constrainedProlateXiApertureMetric00 M0 := by
  unfold constrainedProlateXiApertureMetric00 constrainedProlateXiApertureR0Sq
  positivity

/-! ## The true-metric regular Weil Schur coefficient -/

/-- The regular Weil--Toeplitz ground Schur coefficient after division by the candidate
fixed-Hermite target normalization `Gamma₀₀=(16/33)M₀`. -/
def constrainedProlateTrueApertureRegularSchurCoefficient (M0 : ℝ) : ℝ :=
  ((8 : ℝ) / 11) *
      (constrainedProlateWeilToeplitzD0 -
        constrainedProlateWeilToeplitzD1 ^ 2 / constrainedProlateWeilToeplitzD0) /
    constrainedProlateXiApertureMetric00 M0

theorem constrainedProlateTrueApertureRegularSchurCoefficient_eq
    {M0 : ℝ} (hM0 : M0 ≠ 0) :
    constrainedProlateTrueApertureRegularSchurCoefficient M0 =
      (3 / (2 * M0)) *
        (constrainedProlateWeilToeplitzD0 -
          constrainedProlateWeilToeplitzD1 ^ 2 /
            constrainedProlateWeilToeplitzD0) := by
  unfold constrainedProlateTrueApertureRegularSchurCoefficient
    constrainedProlateXiApertureMetric00 constrainedProlateXiApertureR0Sq
  field_simp [hM0, constrainedProlateWeilToeplitzD0_pos.ne']
  ring

/-- The Toeplitz half-floor survives the exact ground aperture normalization. -/
theorem constrainedProlateTrueApertureRegularSchurCoefficient_gt
    {M0 : ℝ} (hM0 : 0 < M0) :
    3 / (4 * M0) < constrainedProlateTrueApertureRegularSchurCoefficient M0 := by
  rw [constrainedProlateTrueApertureRegularSchurCoefficient_eq hM0.ne']
  calc
    3 / (4 * M0) = (3 / (2 * M0)) * ((1 : ℝ) / 2) := by
      field_simp
      ring
    _ < (3 / (2 * M0)) *
        (constrainedProlateWeilToeplitzD0 -
          constrainedProlateWeilToeplitzD1 ^ 2 /
            constrainedProlateWeilToeplitzD0) :=
      mul_lt_mul_of_pos_left
        constrainedProlateWeilToeplitzSchurCoefficient_gt_half (by positivity)

/-- Source-specific formal capstone: exact theta/Xi normalization, the symbolic two-channel
determinant under strict variance, and the positive target-normalized Schur coefficient. -/
theorem constrainedProlateApertureXiMetric_capstone
    {M0 M1 M2 : ℝ} (hM0 : 0 < M0) (hvariance : M1 ^ 2 < M0 * M2) :
    (∀ x : ℝ, constrainedProlateGroundHermiteSeed x =
      constrainedProlateGroundHermiteXiScale * thetaCuspSeed x) ∧
    (∀ t : ℝ, (𝓕 constrainedProlateGroundHermiteSchwartz) (t / (2 * Real.pi)) =
      (constrainedProlateGroundHermiteXiScale : ℂ) * XiC (t : ℂ)) ∧
    constrainedProlateXiApertureMetricDet M0 M1 M2 =
      (512 / 199395 : ℝ) * (M0 * M2 - M1 ^ 2) ∧
    0 < constrainedProlateXiApertureMetricDet M0 M1 M2 ∧
    3 / (4 * M0) < constrainedProlateTrueApertureRegularSchurCoefficient M0 := by
  exact ⟨constrainedProlateGroundHermiteSeed_eq_thetaCuspSeed,
    fourier_constrainedProlateGroundHermiteSchwartz_scaled,
    constrainedProlateXiApertureMetricDet_eq M0 M1 M2,
    constrainedProlateXiApertureMetricDet_pos hvariance,
    constrainedProlateTrueApertureRegularSchurCoefficient_gt hM0⟩

end

end RHTower
