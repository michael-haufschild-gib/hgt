import GaloisForLFunctions.RHTower.XiWardAbelAffineCompanionMultiplicitySeparator
import GaloisForLFunctions.RHTower.SlabMassSquareCertificate
import GaloisForLFunctions.HTGeometry.ExpRayL2

/-!
# Entire Gaussian covariance on one reflection-complete height fibre

The two-variable entire kernel

`1 - exp (n (z - w)^2)`

vanishes before scalarization on every diagonal multiplicity pair.  On an equal-ordinate fibre,
`z - w` is purely imaginary, so the kernel is the positive Gaussian saturation
`1 - exp (-n d^2)`.  Distinct transverse locations therefore receive unit charge as
`n -> infinity`, while diagonal copies continue to receive zero charge.

For a reflection-complete fibre, let `m0` be critical-line multiplicity and let `m i` be the
multiplicity at each positive transverse location (the reflected negative location has the same
multiplicity).  The saturated ordered-pair covariance is

`M^2 - m0^2 - 2 * sum_i (m i)^2`,

where `M = m0 + 2 * sum_i m i`.  Dividing by `M` makes the charge linear rather than quadratic.
The main inequality proves that this normalized covariance still dominates the complete
strict-right multiplicity `sum_i m i`, including arbitrary collisions and critical-line copies
in the same height fibre.

This is a finite algebraic/source-kernel theorem.  A height-dephased pole--Gamma--von-Mangoldt
realization and its quantitative trace bound are separate.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Entire two-variable kernel whose equal-ordinate restriction is Gaussian saturation. -/
def entireGaussianPairKernel (n : ℕ) (z w : ℂ) : ℂ :=
  1 - Complex.exp ((n : ℂ) * (z - w) ^ 2)

/-- Positive equal-ordinate restriction of the entire Gaussian pair kernel. -/
def gaussianPairSaturation (n : ℕ) (d : ℝ) : ℝ :=
  1 - Real.exp (-((n : ℝ) * d ^ 2))

theorem entireGaussianPairKernel_equalOrdinate
    (n : ℕ) (x y v : ℝ) :
    entireGaussianPairKernel n
        ((x : ℂ) + I * (y : ℂ))
        ((x : ℂ) + I * (v : ℂ)) =
      (gaussianPairSaturation n (y - v) : ℂ) := by
  rw [entireGaussianPairKernel, gaussianPairSaturation]
  have hsq :
      (((x : ℂ) + I * (y : ℂ)) - ((x : ℂ) + I * (v : ℂ))) ^ 2 =
        ((-((y - v) ^ 2) : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, pow_two]
  rw [hsq]
  push_cast
  congr 3
  ring

theorem gaussianPairSaturation_zero (n : ℕ) :
    gaussianPairSaturation n 0 = 0 := by
  simp [gaussianPairSaturation]

theorem gaussianPairSaturation_nonneg (n : ℕ) (d : ℝ) :
    0 ≤ gaussianPairSaturation n d := by
  rw [gaussianPairSaturation]
  have hexp : Real.exp (-((n : ℝ) * d ^ 2)) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    exact neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg d))
  linarith

theorem gaussianPairSaturation_le_one (n : ℕ) (d : ℝ) :
    gaussianPairSaturation n d ≤ 1 := by
  rw [gaussianPairSaturation]
  exact sub_le_self 1 (Real.exp_pos _).le

/-- Every nonzero transverse separation saturates to unit pair charge. -/
theorem tendsto_gaussianPairSaturation {d : ℝ} (hd : d ≠ 0) :
    Tendsto (fun n : ℕ => gaussianPairSaturation n d) atTop (nhds 1) := by
  have hd2 : 0 < d ^ 2 := sq_pos_of_ne_zero hd
  have hdecay :=
    (GaloisForLFunctions.HTGeometry.tendsto_exp_neg_mul_atTop_nhds_zero hd2).comp
      tendsto_natCast_atTop_atTop
  have hdecay' :
      Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) * d ^ 2))) atTop (nhds 0) := by
    convert hdecay using 1
    funext n
    congr 1
    ring
  simpa only [gaussianPairSaturation, sub_zero] using
    (tendsto_const_nhds.sub hdecay')

/-- Strict-right multiplicity in one reflection-complete height fibre. -/
def reflectionFibreStrictRightMass {ι : Type*}
    (s : Finset ι) (m : ι → ℕ) : ℝ :=
  ∑ i ∈ s, (m i : ℝ)

/-- Total multiplicity after adjoining reflection partners and critical-line multiplicity. -/
def reflectionFibreTotalMass {ι : Type*}
    (s : Finset ι) (m0 : ℕ) (m : ι → ℕ) : ℝ :=
  (m0 : ℝ) + 2 * reflectionFibreStrictRightMass s m

/-- Saturated ordered-pair Gaussian covariance.  The subtracted terms are precisely pairs at the
same transverse location, including every diagonal multiplicity pair. -/
def saturatedGaussianReflectionFibreCovariance {ι : Type*}
    (s : Finset ι) (m0 : ℕ) (m : ι → ℕ) : ℝ :=
  reflectionFibreTotalMass s m0 m ^ 2 - (m0 : ℝ) ^ 2 -
    2 * ∑ i ∈ s, (m i : ℝ) ^ 2

theorem saturatedGaussianReflectionFibreCovariance_eq {ι : Type*}
    (s : Finset ι) (m0 : ℕ) (m : ι → ℕ) :
    saturatedGaussianReflectionFibreCovariance s m0 m =
      4 * (m0 : ℝ) * reflectionFibreStrictRightMass s m +
        4 * reflectionFibreStrictRightMass s m ^ 2 -
          2 * ∑ i ∈ s, (m i : ℝ) ^ 2 := by
  rw [saturatedGaussianReflectionFibreCovariance,
    reflectionFibreTotalMass]
  ring

/-- Normalized saturated covariance retains at least one unit for every strict-right divisor
copy.  Extra critical-line multiplicity and distinct off-line positions only increase charge. -/
theorem totalMass_mul_strictRightMass_le_saturatedGaussianCovariance
    {ι : Type*} (s : Finset ι) (m0 : ℕ) (m : ι → ℕ) :
    reflectionFibreTotalMass s m0 m * reflectionFibreStrictRightMass s m ≤
      saturatedGaussianReflectionFibreCovariance s m0 m := by
  have hsq :
      (∑ i ∈ s, (m i : ℝ) ^ 2) ≤
        reflectionFibreStrictRightMass s m ^ 2 := by
    simpa only [reflectionFibreStrictRightMass] using
      SlabMassSquareCertificate.sum_sq_le_sq_sum s (fun i => (m i : ℝ))
        (fun i hi => Nat.cast_nonneg (m i))
  have hm0 : 0 ≤ (m0 : ℝ) := Nat.cast_nonneg m0
  have hR : 0 ≤ reflectionFibreStrictRightMass s m := by
    rw [reflectionFibreStrictRightMass]
    positivity
  rw [saturatedGaussianReflectionFibreCovariance_eq,
    reflectionFibreTotalMass]
  nlinarith

theorem strictRightMass_le_normalizedSaturatedGaussianCovariance
    {ι : Type*} (s : Finset ι) (m0 : ℕ) (m : ι → ℕ)
    (hM : 0 < reflectionFibreTotalMass s m0 m) :
    reflectionFibreStrictRightMass s m ≤
      saturatedGaussianReflectionFibreCovariance s m0 m /
        reflectionFibreTotalMass s m0 m := by
  rw [le_div_iff₀ hM]
  simpa [mul_comm] using
    totalMass_mul_strictRightMass_le_saturatedGaussianCovariance s m0 m

/-- Normalization also gives a sharp total-mass ceiling, so fibre collisions cannot create a
quadratic budget loss. -/
theorem normalizedSaturatedGaussianCovariance_le_totalMass
    {ι : Type*} (s : Finset ι) (m0 : ℕ) (m : ι → ℕ)
    (hM : 0 < reflectionFibreTotalMass s m0 m) :
    saturatedGaussianReflectionFibreCovariance s m0 m /
        reflectionFibreTotalMass s m0 m ≤
      reflectionFibreTotalMass s m0 m := by
  rw [div_le_iff₀ hM]
  rw [saturatedGaussianReflectionFibreCovariance]
  have hm0sq : 0 ≤ (m0 : ℝ) ^ 2 := sq_nonneg _
  have hsum : 0 ≤ ∑ i ∈ s, (m i : ℝ) ^ 2 := by positivity
  nlinarith

end

end RHTower
