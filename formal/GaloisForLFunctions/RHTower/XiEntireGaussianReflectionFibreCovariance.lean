import GaloisForLFunctions.RHTower.XiWardAbelAffineCompanionMultiplicitySeparator
import GaloisForLFunctions.RHTower.SlabMassSquareCertificate
import GaloisForLFunctions.RHTower.XiGuinandWeilRectanglePeeling
import GaloisForLFunctions.HTGeometry.ExpRayL2

/-!
# Entire Gaussian covariance on one reflection-complete height fibre

The two-variable entire kernel

`1 - exp (n (z - w)^(2 : ℕ))`

vanishes before scalarization on every diagonal multiplicity pair.  On an equal-ordinate fibre,
`z - w` is purely imaginary, so the kernel is the positive Gaussian saturation
`1 - exp (-n d^(2 : ℕ))`.  Distinct transverse locations therefore receive unit charge as
`n -> infinity`, while diagonal copies continue to receive zero charge.

For a reflection-complete fibre, let `m0` be critical-line multiplicity and let `m i` be the
multiplicity at each positive transverse location (the reflected negative location has the same
multiplicity).  The saturated ordered-pair covariance is

`M^(2 : ℕ) - m0^(2 : ℕ) - 2 * sum_i (m i)^(2 : ℕ)`,

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
  1 - Complex.exp ((n : ℂ) * (z - w) ^ (2 : ℕ))

/-- Positive equal-ordinate restriction of the entire Gaussian pair kernel. -/
def gaussianPairSaturation (n : ℕ) (d : ℝ) : ℝ :=
  1 - Real.exp (-((n : ℝ) * d ^ (2 : ℕ)))

theorem entireGaussianPairKernel_equalOrdinate
    (n : ℕ) (x y v : ℝ) :
    entireGaussianPairKernel n
        ((x : ℂ) + I * (y : ℂ))
        ((x : ℂ) + I * (v : ℂ)) =
      (gaussianPairSaturation n (y - v) : ℂ) := by
  rw [entireGaussianPairKernel, gaussianPairSaturation]
  have hsq :
      (((x : ℂ) + I * (y : ℂ)) - ((x : ℂ) + I * (v : ℂ))) ^ (2 : ℕ) =
        ((-((y - v) ^ (2 : ℕ)) : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, pow_two]
  rw [hsq]
  push_cast
  congr 3
  ring

/-- On the real axis the same entire kernel has the opposite sign: every nonzero real separation
produces `1 - exp (n d²)`.  This is the exact horizontal-edge amplification hidden by the positive
equal-ordinate restriction. -/
theorem entireGaussianPairKernel_realAxis (n : ℕ) (x y : ℝ) :
    entireGaussianPairKernel n (x : ℂ) (y : ℂ) =
      ((1 - Real.exp ((n : ℝ) * (x - y) ^ (2 : ℕ)) : ℝ) : ℂ) := by
  rw [entireGaussianPairKernel]
  have hsq : (((x : ℂ) - (y : ℂ)) ^ (2 : ℕ)) = (((x - y) ^ (2 : ℕ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hsq]
  push_cast
  rfl

/-- **Horizontal-edge obstruction.**  At every nonzero real separation the real part of the
Gaussian source test eventually lies below every prescribed negative threshold.  Consequently
the transverse saturation limit has no parameter-uniform pointwise majorant on a horizontal
contour edge; any quantitative source estimate must supply cancellation or replace this kernel. -/
theorem entireGaussianPairKernel_realAxis_eventually_re_lt
    {x y B : ℝ} (hxy : x ≠ y) :
    ∀ᶠ n : ℕ in atTop,
      (entireGaussianPairKernel n (x : ℂ) (y : ℂ)).re < -B := by
  have hd2 : 0 < (x - y) ^ (2 : ℕ) := sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)
  have hlin0 : Tendsto (fun n : ℕ => (x - y) ^ (2 : ℕ) * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hd2
  have hlin : Tendsto (fun n : ℕ => (n : ℝ) * (x - y) ^ (2 : ℕ)) atTop atTop := by
    convert hlin0 using 1
    funext n
    ring
  have hexp : Tendsto
      (fun n : ℕ => Real.exp ((n : ℝ) * (x - y) ^ (2 : ℕ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp hlin
  filter_upwards [hexp.eventually_gt_atTop (B + 1)] with n hn
  rw [entireGaussianPairKernel_realAxis]
  simp only [ofReal_re]
  linarith

theorem gaussianPairSaturation_zero (n : ℕ) :
    gaussianPairSaturation n 0 = 0 := by
  simp [gaussianPairSaturation]

theorem gaussianPairSaturation_nonneg (n : ℕ) (d : ℝ) :
    0 ≤ gaussianPairSaturation n d := by
  rw [gaussianPairSaturation]
  have hexp : Real.exp (-((n : ℝ) * d ^ (2 : ℕ))) ≤ 1 := by
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
  have hd2 : 0 < d ^ (2 : ℕ) := sq_pos_of_ne_zero hd
  have hdecay :=
    (GaloisForLFunctions.HTGeometry.tendsto_exp_neg_mul_atTop_nhds_zero hd2).comp
      tendsto_natCast_atTop_atTop
  have hdecay' :
      Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) * d ^ (2 : ℕ)))) atTop (nhds 0) := by
    convert hdecay using 1
    funext n
    congr 1
    ring
  simpa only [gaussianPairSaturation, sub_zero] using
    (tendsto_const_nhds.sub hdecay')

theorem analyticOnNhd_entireGaussianPairKernel_left (n : ℕ) (w : ℂ) :
    AnalyticOnNhd ℂ (fun z => entireGaussianPairKernel n z w) Set.univ := by
  unfold entireGaussianPairKernel
  exact analyticOnNhd_const.sub
    (analyticOnNhd_const.mul
      ((analyticOnNhd_id.sub analyticOnNhd_const).pow 2)).cexp

theorem analyticOnNhd_entireGaussianPairKernel_right (n : ℕ) (z : ℂ) :
    AnalyticOnNhd ℂ (fun w => entireGaussianPairKernel n z w) Set.univ := by
  unfold entireGaussianPairKernel
  exact analyticOnNhd_const.sub
    (analyticOnNhd_const.mul
      ((analyticOnNhd_const.sub analyticOnNhd_id).pow 2)).cexp

/-! ## Fixed-contour pole--Gamma--von-Mangoldt realization -/

/-- One normalized source contour with the entire Gaussian kernel as its fixed test.  Its
definition contains no zero set, divisor support, or interpolant. -/
def normalizedXiGaussianPairInnerSourceContour
    (z₁ z₂ : ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ *
    rectIntegral
      (fun z => entireGaussianPairKernel n z w *
        continuedPrimeArchSourceRelativeTrace z)
      z₁ z₂

/-- Nested source covariance formed entirely before divisor expansion. -/
def normalizedXiGaussianPairSourceCovariance
    (z₁ z₂ : ℂ) (n : ℕ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ *
    rectIntegral
      (fun w => normalizedXiGaussianPairInnerSourceContour z₁ z₂ n w *
        continuedPrimeArchSourceRelativeTrace w)
      z₁ z₂

/-- The inner fixed source contour lands on its exact multiplicity-weighted Gaussian row. -/
theorem normalizedXiGaussianPairInnerSourceContour_eq_zeroSum
    {z₁ z₂ : ℂ} (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ Set.uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ Set.uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ Set.uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ Set.uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I))
    (n : ℕ) (w : ℂ) :
    normalizedXiGaussianPairInnerSourceContour z₁ z₂ n w =
      ∑ z ∈ xiCClosedRectangleZeros z₁ z₂,
        ((analyticOrderAt XiC z).toNat : ℂ) * entireGaussianPairKernel n z w := by
  have hcontour :=
    rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_closedRectangleZeroSum
      (analyticOnNhd_entireGaussianPairKernel_left n w)
      hre him hbot htop hright hleft
  have hc : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact I_ne_zero
  rw [normalizedXiGaussianPairInnerSourceContour, hcontour,
    ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- **Pre-divisor Gaussian covariance law.**  The nested pole--Gamma--von-Mangoldt source
covariance equals the complete multiplicity-exact Gaussian zero-pair sum.  Both contours and the
entire kernel are fixed before the divisor appears; no Abel projector, exterior Cesaro selector,
or zero-dependent Lagrange interpolation is used. -/
theorem normalizedXiGaussianPairSourceCovariance_eq_zeroPairSum
    {z₁ z₂ : ℂ} (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ Set.uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ Set.uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ Set.uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ Set.uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I))
    (n : ℕ) :
    normalizedXiGaussianPairSourceCovariance z₁ z₂ n =
      ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        ((analyticOrderAt XiC w).toNat : ℂ) *
          ∑ z ∈ xiCClosedRectangleZeros z₁ z₂,
            ((analyticOrderAt XiC z).toNat : ℂ) *
              entireGaussianPairKernel n z w := by
  let S : Finset ℂ := xiCClosedRectangleZeros z₁ z₂
  let g : ℂ → ℂ := fun w =>
    ∑ z ∈ S, ((analyticOrderAt XiC z).toNat : ℂ) *
      entireGaussianPairKernel n z w
  have hg : AnalyticOnNhd ℂ g Set.univ := by
    dsimp only [g]
    exact Finset.analyticOnNhd_fun_sum S fun z _ =>
      analyticOnNhd_const.mul
        (analyticOnNhd_entireGaussianPairKernel_right n z)
  have hinner :
      (fun w => normalizedXiGaussianPairInnerSourceContour z₁ z₂ n w *
        continuedPrimeArchSourceRelativeTrace w) =
      fun w => g w * continuedPrimeArchSourceRelativeTrace w := by
    funext w
    rw [normalizedXiGaussianPairInnerSourceContour_eq_zeroSum
      hre him hbot htop hright hleft n w]
  have hcontour :=
    rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_closedRectangleZeroSum
      hg hre him hbot htop hright hleft
  have hc : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact I_ne_zero
  rw [normalizedXiGaussianPairSourceCovariance, hinner, hcontour,
    ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

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
  reflectionFibreTotalMass s m0 m ^ (2 : ℕ) - (m0 : ℝ) ^ (2 : ℕ) -
    2 * ∑ i ∈ s, (m i : ℝ) ^ (2 : ℕ)

theorem saturatedGaussianReflectionFibreCovariance_eq {ι : Type*}
    (s : Finset ι) (m0 : ℕ) (m : ι → ℕ) :
    saturatedGaussianReflectionFibreCovariance s m0 m =
      4 * (m0 : ℝ) * reflectionFibreStrictRightMass s m +
        4 * reflectionFibreStrictRightMass s m ^ (2 : ℕ) -
          2 * ∑ i ∈ s, (m i : ℝ) ^ (2 : ℕ) := by
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
      (∑ i ∈ s, (m i : ℝ) ^ (2 : ℕ)) ≤
        reflectionFibreStrictRightMass s m ^ (2 : ℕ) := by
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
  have hm0sq : 0 ≤ (m0 : ℝ) ^ (2 : ℕ) := sq_nonneg _
  have hsum : 0 ≤ ∑ i ∈ s, (m i : ℝ) ^ (2 : ℕ) := by positivity
  nlinarith

/-! ## Fixed-pole meromorphic survivor

The Gaussian pair kernel pays for transverse saturation by exponential growth on horizontal
source edges.  The rational kernel below retains the same diagonal-zero/equal-ordinate-positive
geometry, but decomposes into two Cauchy kernels with fixed real shifts.  Its extra poles are
therefore source data rather than selected Xi-divisor locations.
-/

/-- Rational pair kernel with fixed source poles at `z - w = ±eps`. -/
def meromorphicCauchyPairKernel (eps : ℝ) (z w : ℂ) : ℂ :=
  (z - w) ^ (2 : ℕ) / ((z - w) ^ (2 : ℕ) - (eps : ℂ) ^ (2 : ℕ))

/-- Positive equal-ordinate restriction of `meromorphicCauchyPairKernel`. -/
def cauchyPairSaturation (eps d : ℝ) : ℝ :=
  d ^ (2 : ℕ) / (d ^ (2 : ℕ) + eps ^ (2 : ℕ))

/-- Complementary fixed-pole kernel used as a shrinking diagonal projector. -/
def meromorphicCauchyDiagonalKernel (eps : ℝ) (z w : ℂ) : ℂ :=
  1 - meromorphicCauchyPairKernel eps z w

@[simp] theorem meromorphicCauchyDiagonalKernel_self (eps : ℝ) (z : ℂ) :
    meromorphicCauchyDiagonalKernel eps z z = 1 := by
  simp [meromorphicCauchyDiagonalKernel, meromorphicCauchyPairKernel]

theorem meromorphicCauchyPairKernel_self (eps : ℝ) (z : ℂ) :
    meromorphicCauchyPairKernel eps z z = 0 := by
  rw [meromorphicCauchyPairKernel]
  simp

theorem meromorphicCauchyPairKernel_equalOrdinate
    (eps x y v : ℝ) :
    meromorphicCauchyPairKernel eps
        ((x : ℂ) + I * (y : ℂ))
        ((x : ℂ) + I * (v : ℂ)) =
      (cauchyPairSaturation eps (y - v) : ℂ) := by
  rw [meromorphicCauchyPairKernel, cauchyPairSaturation]
  have hsq :
      (((x : ℂ) + I * (y : ℂ)) - ((x : ℂ) + I * (v : ℂ))) ^ (2 : ℕ) =
        ((-((y - v) ^ (2 : ℕ)) : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, pow_two]
  rw [hsq]
  have hreal :
      (-((y - v) ^ (2 : ℕ))) / (-((y - v) ^ (2 : ℕ)) - eps ^ (2 : ℕ)) =
        (y - v) ^ (2 : ℕ) / ((y - v) ^ (2 : ℕ) + eps ^ (2 : ℕ)) := by
    by_cases hden : (y - v) ^ (2 : ℕ) + eps ^ (2 : ℕ) = 0
    · have hnum : (y - v) ^ (2 : ℕ) = 0 := by
        nlinarith [sq_nonneg (y - v), sq_nonneg eps]
      have heps2 : eps ^ (2 : ℕ) = 0 := by
        nlinarith [sq_nonneg (y - v), sq_nonneg eps]
      simp [hnum, heps2]
    · have hdenNeg : -((y - v) ^ (2 : ℕ)) - eps ^ (2 : ℕ) ≠ 0 := by
        intro hz
        apply hden
        linarith
      field_simp [hden, hdenNeg]
      ring
  exact_mod_cast hreal

theorem cauchyPairSaturation_nonneg (eps d : ℝ) :
    0 ≤ cauchyPairSaturation eps d := by
  rw [cauchyPairSaturation]
  positivity

theorem cauchyPairSaturation_le_one (eps d : ℝ) :
    cauchyPairSaturation eps d ≤ 1 := by
  rw [cauchyPairSaturation]
  by_cases hden : d ^ (2 : ℕ) + eps ^ (2 : ℕ) = 0
  · rw [hden]
    simp
  · have hpos : 0 < d ^ (2 : ℕ) + eps ^ (2 : ℕ) :=
      lt_of_le_of_ne (by positivity) (Ne.symm hden)
    rw [div_le_one hpos]
    exact le_add_of_nonneg_right (sq_nonneg eps)

/-- At every fixed nonzero transverse displacement, shrinking fixed source shifts recover unit
pair charge. -/
theorem tendsto_cauchyPairSaturation {d : ℝ} (hd : d ≠ 0) :
    Tendsto (fun n : ℕ => cauchyPairSaturation (1 / ((n : ℝ) + 1)) d)
      atTop (nhds 1) := by
  have heps : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hden : Tendsto
      (fun n : ℕ => d ^ (2 : ℕ) + (1 / ((n : ℝ) + 1)) ^ (2 : ℕ))
      atTop (nhds (d ^ (2 : ℕ))) := by
    convert tendsto_const_nhds.add (heps.pow 2) using 1 <;> norm_num
  have hnum : Tendsto (fun _ : ℕ => d ^ (2 : ℕ)) atTop (nhds (d ^ (2 : ℕ))) :=
    tendsto_const_nhds
  have hdiv := hnum.div hden (pow_ne_zero 2 hd)
  change Tendsto
      (fun n : ℕ => d ^ (2 : ℕ) / (d ^ (2 : ℕ) + (1 / ((n : ℝ) + 1)) ^ (2 : ℕ)))
      atTop (nhds (d ^ (2 : ℕ) / d ^ (2 : ℕ))) at hdiv
  simpa [cauchyPairSaturation, hd] using hdiv

/-- Shrinking the fixed poles recovers unit charge at every pair of distinct complex points, not
only on the equal-ordinate slice. -/
theorem tendsto_meromorphicCauchyPairKernel
    {z w : ℂ} (hzw : z ≠ w) :
    Tendsto
      (fun n : ℕ => meromorphicCauchyPairKernel
        (1 / ((n : ℝ) + 1)) z w)
      atTop (nhds 1) := by
  have hepsR : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have heps : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))
      atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hepsR
  have hd : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have hden : Tendsto
      (fun n : ℕ => (z - w) ^ (2 : ℕ) -
        (((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) ^ (2 : ℕ))
      atTop (nhds ((z - w) ^ (2 : ℕ))) := by
    convert tendsto_const_nhds.sub (heps.pow 2) using 1 <;> norm_num
  have hnum : Tendsto (fun _ : ℕ => (z - w) ^ (2 : ℕ))
      atTop (nhds ((z - w) ^ (2 : ℕ))) := tendsto_const_nhds
  have hdiv := hnum.div hden (pow_ne_zero 2 hd)
  change Tendsto
      (fun n : ℕ => (z - w) ^ (2 : ℕ) /
        ((z - w) ^ (2 : ℕ) - (((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) ^ (2 : ℕ)))
      atTop (nhds ((z - w) ^ (2 : ℕ) / (z - w) ^ (2 : ℕ))) at hdiv
  simpa [meromorphicCauchyPairKernel, hd] using hdiv

theorem tendsto_meromorphicCauchyDiagonalKernel_of_ne
    {z w : ℂ} (hzw : z ≠ w) :
    Tendsto
      (fun n : ℕ => meromorphicCauchyDiagonalKernel
        (1 / ((n : ℝ) + 1)) z w)
      atTop (nhds 0) := by
  have hone : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds 1) :=
    tendsto_const_nhds
  simpa only [meromorphicCauchyDiagonalKernel, sub_self] using
    hone.sub (tendsto_meromorphicCauchyPairKernel hzw)

/-- Finite rational pair packet before the shrinking-shift limit. -/
def finiteMeromorphicCauchyPairCovariance {ι : Type*}
    (s : Finset ι) (z : ι → ℂ) (m : ι → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ s.product s,
    m p.1 * m p.2 * meromorphicCauchyPairKernel
      (1 / ((n : ℝ) + 1)) (z p.1) (z p.2)

/-- For a finite family of distinct support locations, fixed-pole saturation converges to the
complete ordered off-diagonal mass.  Multiplicity remains in the weights and no simplicity
assumption is made. -/
theorem tendsto_finiteMeromorphicCauchyPairCovariance
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (z : ι → ℂ) (m : ι → ℂ)
    (hz : Set.InjOn z s) :
    Tendsto (finiteMeromorphicCauchyPairCovariance s z m) atTop
      (nhds (∑ p ∈ s.product s,
        if p.1 = p.2 then 0 else m p.1 * m p.2)) := by
  change Tendsto
    (fun n : ℕ => ∑ p ∈ s.product s,
      m p.1 * m p.2 * meromorphicCauchyPairKernel
        (1 / ((n : ℝ) + 1)) (z p.1) (z p.2))
    atTop (nhds (∑ p ∈ s.product s,
      if p.1 = p.2 then 0 else m p.1 * m p.2))
  apply tendsto_finsetSum (s.product s)
  intro p hp
  rcases p with ⟨i, j⟩
  obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
  by_cases hdiag : i = j
  · subst j
    simp [meromorphicCauchyPairKernel_self]
  · have hzw : z i ≠ z j := fun h => hdiag (hz hp₁ hp₂ h)
    simpa [hdiag] using
      (tendsto_const_nhds.mul tendsto_const_nhds).mul
        (tendsto_meromorphicCauchyPairKernel hzw)

/-- Ordered off-diagonal mass is total mass squared minus the exact collision diagonal. -/
theorem finiteOrderedOffDiagonalMass_eq_totalSquare_sub_diagonal
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (m : ι → ℂ) :
    (∑ p ∈ s.product s,
        if p.1 = p.2 then 0 else m p.1 * m p.2) =
      (∑ i ∈ s, m i) ^ (2 : ℕ) - ∑ i ∈ s, m i ^ (2 : ℕ) := by
  have hrow (i : ι) (hi : i ∈ s) :
      (∑ j ∈ s, if i = j then 0 else m i * m j) =
        (∑ j ∈ s, m i * m j) - m i ^ (2 : ℕ) := by
    calc
      (∑ j ∈ s, if i = j then 0 else m i * m j) =
          ∑ j ∈ s, (m i * m j - if i = j then m i * m j else 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hij : i = j
            · simp [hij]
            · simp [hij]
      _ = (∑ j ∈ s, m i * m j) -
          ∑ j ∈ s, if i = j then m i * m j else 0 := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ j ∈ s, m i * m j) - m i ^ (2 : ℕ) := by
            rw [Finset.sum_ite_eq, if_pos hi]
            ring
  calc
    (∑ p ∈ s.product s,
        if p.1 = p.2 then 0 else m p.1 * m p.2) =
        ∑ i ∈ s, ∑ j ∈ s, if i = j then 0 else m i * m j :=
          Finset.sum_product s s _
    _ = ∑ i ∈ s, ((∑ j ∈ s, m i * m j) - m i ^ (2 : ℕ)) := by
          apply Finset.sum_congr rfl
          exact hrow
    _ = (∑ i ∈ s, ∑ j ∈ s, m i * m j) -
        ∑ i ∈ s, m i ^ (2 : ℕ) := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ i ∈ s, m i) ^ (2 : ℕ) - ∑ i ∈ s, m i ^ (2 : ℕ) := by
          rw [← Finset.sum_mul_sum]
          ring

theorem tendsto_finiteMeromorphicCauchyPairCovariance_totalSquare_sub_diagonal
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (z : ι → ℂ) (m : ι → ℂ)
    (hz : Set.InjOn z s) :
    Tendsto (finiteMeromorphicCauchyPairCovariance s z m) atTop
      (nhds ((∑ i ∈ s, m i) ^ (2 : ℕ) - ∑ i ∈ s, m i ^ (2 : ℕ))) := by
  rw [← finiteOrderedOffDiagonalMass_eq_totalSquare_sub_diagonal]
  exact tendsto_finiteMeromorphicCauchyPairCovariance s z m hz

/-- Fixed-pole resolvent decomposition.  This is the source-side replacement for a divisor
projector: both additional poles are prescribed before any Xi zero is selected. -/
theorem meromorphicCauchyPairKernel_eq_resolventDifference
    (eps : ℝ) (z w : ℂ)
    (hminus : z - w - (eps : ℂ) ≠ 0)
    (hplus : z - w + (eps : ℂ) ≠ 0) :
    meromorphicCauchyPairKernel eps z w =
      1 + (eps / 2 : ℂ) *
        ((z - w - (eps : ℂ))⁻¹ - (z - w + (eps : ℂ))⁻¹) := by
  rw [meromorphicCauchyPairKernel]
  have hden : (z - w) ^ (2 : ℕ) - (eps : ℂ) ^ (2 : ℕ) ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hplus hminus
  field_simp [hminus, hplus, hden]
  ring

theorem meromorphicCauchyPairKernel_realAxis (eps x y : ℝ) :
    meromorphicCauchyPairKernel eps (x : ℂ) (y : ℂ) =
      (((x - y) ^ (2 : ℕ) / ((x - y) ^ (2 : ℕ) - eps ^ (2 : ℕ)) : ℝ) : ℂ) := by
  rw [meromorphicCauchyPairKernel]
  push_cast
  rfl

/-- Unlike the entire Gaussian kernel, the rational survivor has no exponential real-axis
amplification: away from the diagonal it converges back to `1`. -/
theorem tendsto_meromorphicCauchyPairKernel_realAxis
    {x y : ℝ} (hxy : x ≠ y) :
    Tendsto
      (fun n : ℕ =>
        meromorphicCauchyPairKernel (1 / ((n : ℝ) + 1)) (x : ℂ) (y : ℂ))
      atTop (nhds 1) := by
  have heps : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hd : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hden : Tendsto
      (fun n : ℕ => (x - y) ^ (2 : ℕ) - (1 / ((n : ℝ) + 1)) ^ (2 : ℕ))
      atTop (nhds ((x - y) ^ (2 : ℕ))) := by
    convert tendsto_const_nhds.sub (heps.pow 2) using 1 <;> norm_num
  have hreal : Tendsto
      (fun n : ℕ => (x - y) ^ (2 : ℕ) /
        ((x - y) ^ (2 : ℕ) - (1 / ((n : ℝ) + 1)) ^ (2 : ℕ)))
      atTop (nhds 1) := by
    have hnum : Tendsto (fun _ : ℕ => (x - y) ^ (2 : ℕ))
        atTop (nhds ((x - y) ^ (2 : ℕ))) := tendsto_const_nhds
    have hdiv := hnum.div hden (pow_ne_zero 2 hd)
    change Tendsto
        (fun n : ℕ => (x - y) ^ (2 : ℕ) /
          ((x - y) ^ (2 : ℕ) - (1 / ((n : ℝ) + 1)) ^ (2 : ℕ)))
        atTop (nhds ((x - y) ^ (2 : ℕ) / (x - y) ^ (2 : ℕ))) at hdiv
    simpa [hd] using hdiv
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  change Tendsto
      (fun n : ℕ => (((x - y) ^ (2 : ℕ) /
        ((x - y) ^ (2 : ℕ) - (1 / ((n : ℝ) + 1)) ^ (2 : ℕ)) : ℝ) : ℂ))
      atTop (nhds (1 : ℂ)) at hcomplex
  simpa only [meromorphicCauchyPairKernel_realAxis, ofReal_one] using hcomplex

end

end RHTower
