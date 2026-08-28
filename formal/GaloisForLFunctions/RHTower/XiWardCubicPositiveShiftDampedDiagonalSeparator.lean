import GaloisForLFunctions.RHTower.XiWardCubicPositiveShiftAveragedMultiplicity

/-!
# Damped positive-shift diagonal separator

Positive displacement makes the bichamber cubic feature grow on the critical radial boundary.
The universal scalar damping `exp (-3 * eps * r)` is the least integer damping that returns every
right-strip displacement to the open radial-decay chamber.  After phase cancellation its radial
density is an exact square of two exponentials.

The scale-normalized critical density is `115 / 108`, while every fixed strict-right displacement
has normalized density tending to zero as `eps -> 0+`.  Its complement is therefore a new
source-formed candidate for separating diagonal multiplicity from positive real shifts.  This
module proves the exact radial calculation; the height-local pole--Gamma--von-Mangoldt ceiling is
still separate.
-/

open Complex Filter Topology Set MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Radial density obtained by multiplying the positive-shift bichamber product by the universal
joint damping `exp (-3 * eps * r)` and cancelling its ordinate phase. -/
def xiWardCubicPositiveShiftDampedRadialDensity
    (a eps r : ℝ) : ℝ :=
  r ^ 2 *
    (Real.exp (-((a + eps) * r)) -
      Real.exp (-((2 * a + eps / 2) * r))) ^ 2

/-- Simultaneous vertical translation contributes one common negative phase to left feature. -/
theorem xiWardCubicBichamberLeftFeature_verticalTranslate
    (s t : ℂ) (gamma r : ℝ) :
    xiWardCubicBichamberLeftFeature
        (s - I * (gamma : ℂ)) (t - I * (gamma : ℂ)) r =
      Complex.exp (-I * ((gamma * r : ℝ) : ℂ)) *
        xiWardCubicBichamberLeftFeature s t r := by
  unfold xiWardCubicBichamberLeftFeature
  have h0 :
      (s - I * (gamma : ℂ) - 1 / 2) * (r : ℂ) =
        (s - 1 / 2) * (r : ℂ) - I * ((gamma * r : ℝ) : ℂ) := by
    push_cast
    ring
  have h1 :
      ((3 * (s - I * (gamma : ℂ) - 1 / 2) -
          (t - I * (gamma : ℂ) - 1 / 2)) / 2) * (r : ℂ) =
        ((3 * (s - 1 / 2) - (t - 1 / 2)) / 2) * (r : ℂ) -
          I * ((gamma * r : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h0, h1]
  simp only [sub_eq_add_neg, Complex.exp_add]
  ring

/-- Simultaneous vertical translation contributes opposite common phase to right feature. -/
theorem xiWardCubicBichamberRightFeature_verticalTranslate
    (s t : ℂ) (gamma r : ℝ) :
    xiWardCubicBichamberRightFeature
        (s - I * (gamma : ℂ)) (t - I * (gamma : ℂ)) r =
      Complex.exp (I * ((gamma * r : ℝ) : ℂ)) *
        xiWardCubicBichamberRightFeature s t r := by
  unfold xiWardCubicBichamberRightFeature
  have h0 :
      -((t - I * (gamma : ℂ) - 1 / 2) * (r : ℂ)) =
        -((t - 1 / 2) * (r : ℂ)) + I * ((gamma * r : ℝ) : ℂ) := by
    push_cast
    ring
  have h1 :
      -(((3 * (t - I * (gamma : ℂ) - 1 / 2) -
          (s - I * (gamma : ℂ) - 1 / 2)) / 2) * (r : ℂ)) =
        -(((3 * (t - 1 / 2) - (s - 1 / 2)) / 2) * (r : ℂ)) +
          I * ((gamma * r : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h0, h1, Complex.exp_add, Complex.exp_add]
  ring

/-- Opposite vertical phases cancel in bichamber product. -/
theorem xiWardCubicBichamberFeatureProduct_verticalTranslate
    (s t : ℂ) (gamma r : ℝ) :
    xiWardCubicBichamberFeatureProduct
        (s - I * (gamma : ℂ)) (t - I * (gamma : ℂ)) r =
      xiWardCubicBichamberFeatureProduct s t r := by
  unfold xiWardCubicBichamberFeatureProduct
  rw [xiWardCubicBichamberLeftFeature_verticalTranslate,
    xiWardCubicBichamberRightFeature_verticalTranslate]
  have hphase :
      Complex.exp (-I * ((gamma * r : ℝ) : ℂ)) *
          Complex.exp (I * ((gamma * r : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero
    ring
  calc
    _ = (Complex.exp (-I * ((gamma * r : ℝ) : ℂ)) *
          Complex.exp (I * ((gamma * r : ℝ) : ℂ))) *
        (xiWardCubicBichamberLeftFeature s t r *
          xiWardCubicBichamberRightFeature s t r) := by ring
    _ = _ := by rw [hphase, one_mul]

/-- The scalar damped density is the actual bichamber weight on the zero-ordinate horizontal
slice.  Ordinate phases cancel, so the same density governs every ordinate. -/
theorem twoShiftDamping_mul_xiWardCubicBichamberLeftFeature_realSlice
    (a eps r : ℝ) :
    (Real.exp (-(2 * eps * r)) : ℂ) *
        xiWardCubicBichamberLeftFeature
          (1 - (((1 / 2 + a : ℝ) : ℂ)) + (eps : ℂ))
          (star (((1 / 2 + a : ℝ) : ℂ))) r =
      (r : ℂ) *
        ((Real.exp (-((a + eps) * r)) : ℂ) -
          (Real.exp (-((2 * a + eps / 2) * r)) : ℂ)) := by
  unfold xiWardCubicBichamberLeftFeature
  push_cast
  simp only [Complex.star_def, map_add, map_div₀, map_one, map_ofNat,
    Complex.conj_ofReal]
  norm_num
  ring_nf
  have h0 :
      Complex.exp (-(↑eps * ↑r * 2)) *
          Complex.exp (↑eps * ↑r - ↑r * ↑a) =
        Complex.exp (-(↑eps * ↑r) - ↑r * ↑a) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have h1 :
      Complex.exp (-(↑eps * ↑r * 2)) *
          Complex.exp (↑eps * ↑r * (3 / 2) - ↑r * ↑a * 2) =
        Complex.exp (↑eps * ↑r * (-1 / 2) - ↑r * ↑a * 2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = (↑r : ℂ) *
          (Complex.exp (-(↑eps * ↑r * 2)) *
            Complex.exp (↑eps * ↑r - ↑r * ↑a)) -
        (↑r : ℂ) *
          (Complex.exp (-(↑eps * ↑r * 2)) *
            Complex.exp (↑eps * ↑r * (3 / 2) - ↑r * ↑a * 2)) := by ring
    _ = _ := by rw [h0, h1]

theorem oneShiftDamping_mul_xiWardCubicBichamberRightFeature_realSlice
    (a eps r : ℝ) :
    (Real.exp (-(eps * r)) : ℂ) *
        xiWardCubicBichamberRightFeature
          (1 - (((1 / 2 + a : ℝ) : ℂ)) + (eps : ℂ))
          (star (((1 / 2 + a : ℝ) : ℂ))) r =
      (r : ℂ) *
        ((Real.exp (-((a + eps) * r)) : ℂ) -
          (Real.exp (-((2 * a + eps / 2) * r)) : ℂ)) := by
  unfold xiWardCubicBichamberRightFeature
  push_cast
  simp only [Complex.star_def, map_add, map_div₀, map_one, map_ofNat,
    Complex.conj_ofReal]
  norm_num
  ring_nf
  have h0 :
      Complex.exp (-(↑eps * ↑r)) * Complex.exp (-(↑r * ↑a)) =
        Complex.exp (-(↑eps * ↑r) - ↑r * ↑a) := by
    rw [← Complex.exp_add]
    congr 1
  have h1 :
      Complex.exp (-(↑eps * ↑r)) *
          Complex.exp (↑eps * ↑r * (1 / 2) - ↑r * ↑a * 2) =
        Complex.exp (↑eps * ↑r * (-1 / 2) - ↑r * ↑a * 2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = (↑r : ℂ) *
          (Complex.exp (-(↑eps * ↑r)) * Complex.exp (-(↑r * ↑a))) -
        (↑r : ℂ) *
          (Complex.exp (-(↑eps * ↑r)) *
            Complex.exp (↑eps * ↑r * (1 / 2) - ↑r * ↑a * 2)) := by ring
    _ = _ := by rw [h0, h1]

theorem ofReal_exp_mul_xiWardCubicPositiveShiftBichamberWeight_eq_density
    (a eps r : ℝ) :
    (Real.exp (-(3 * eps * r)) : ℂ) *
        xiWardCubicPositiveShiftBichamberWeight
          (((1 / 2 + a : ℝ) : ℂ)) eps r =
      (xiWardCubicPositiveShiftDampedRadialDensity a eps r : ℂ) := by
  have hdamp :
      (Real.exp (-(3 * eps * r)) : ℂ) =
        (Real.exp (-(2 * eps * r)) : ℂ) *
          (Real.exp (-(eps * r)) : ℂ) := by
    push_cast
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hdamp, xiWardCubicPositiveShiftBichamberWeight,
    xiWardCubicBichamberFeatureProduct]
  rw [show (1 - (((1 / 2 + a : ℝ) : ℂ)) + (eps : ℂ)) =
      1 - (((1 / 2 + a : ℝ) : ℂ)) + (eps : ℂ) by ring]
  rw [show
      ((Real.exp (-(2 * eps * r)) : ℂ) *
          (Real.exp (-(eps * r)) : ℂ)) *
          (xiWardCubicBichamberLeftFeature
            (1 - (((1 / 2 + a : ℝ) : ℂ)) + (eps : ℂ))
            (star (((1 / 2 + a : ℝ) : ℂ))) r *
          xiWardCubicBichamberRightFeature
            (1 - (((1 / 2 + a : ℝ) : ℂ)) + (eps : ℂ))
            (star (((1 / 2 + a : ℝ) : ℂ))) r) =
        ((Real.exp (-(2 * eps * r)) : ℂ) *
          xiWardCubicBichamberLeftFeature
            (1 - (((1 / 2 + a : ℝ) : ℂ)) + (eps : ℂ))
            (star (((1 / 2 + a : ℝ) : ℂ))) r) *
        ((Real.exp (-(eps * r)) : ℂ) *
          xiWardCubicBichamberRightFeature
            (1 - (((1 / 2 + a : ℝ) : ℂ)) + (eps : ℂ))
            (star (((1 / 2 + a : ℝ) : ℂ))) r) by ring]
  rw [twoShiftDamping_mul_xiWardCubicBichamberLeftFeature_realSlice,
    oneShiftDamping_mul_xiWardCubicBichamberRightFeature_realSlice]
  unfold xiWardCubicPositiveShiftDampedRadialDensity
  push_cast
  ring

/-- Actual damped bichamber weight at arbitrary ordinate equals the scalar radial density. -/
theorem ofReal_exp_mul_xiWardCubicPositiveShiftBichamberWeight_eq_density_general
    (a gamma eps r : ℝ) :
    (Real.exp (-(3 * eps * r)) : ℂ) *
        xiWardCubicPositiveShiftBichamberWeight
          (((1 / 2 + a : ℝ) : ℂ) + I * (gamma : ℂ)) eps r =
      (xiWardCubicPositiveShiftDampedRadialDensity a eps r : ℂ) := by
  have hs :
      1 - (((1 / 2 + a : ℝ) : ℂ) + I * (gamma : ℂ)) + (eps : ℂ) =
        (1 - (((1 / 2 + a : ℝ) : ℂ)) + (eps : ℂ)) - I * (gamma : ℂ) := by
    ring
  have ht :
      star ((((1 / 2 + a : ℝ) : ℂ) + I * (gamma : ℂ))) =
        (((1 / 2 + a : ℝ) : ℂ)) - I * (gamma : ℂ) := by
    simp
    ring
  rw [xiWardCubicPositiveShiftBichamberWeight, hs, ht,
    xiWardCubicBichamberFeatureProduct_verticalTranslate]
  convert ofReal_exp_mul_xiWardCubicPositiveShiftBichamberWeight_eq_density
    a eps r using 1
  all_goals simp [xiWardCubicPositiveShiftBichamberWeight]

/-- Dimensionless radial anomaly profile at horizontal ratio `x = a / eps`. -/
def xiWardCubicPositiveShiftDiagonalAnomalyProfile (x : ℝ) : ℝ :=
  2 / (2 * x + 2) ^ 3 -
    4 / (3 * x + 3 / 2) ^ 3 +
      2 / (4 * x + 1) ^ 3

/-- Cubic Laplace moment used by the damped separator. -/
theorem integral_Ioi_sq_mul_exp_neg_mul
    {c : ℝ} (hc : 0 < c) :
    (∫ r : ℝ in Ioi 0, r ^ 2 * Real.exp (-(c * r))) = 2 / c ^ 3 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (3 : ℝ)) (r := c) (by norm_num) hc
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two] at h
  have hgamma : Real.Gamma 3 = 2 := by
    rw [show (3 : ℝ) = (2 : ℕ) + 1 by norm_num,
      Real.Gamma_nat_eq_factorial]
    norm_num
  rw [hgamma] at h
  norm_num at h ⊢
  rw [h]
  field_simp [hc.ne']

theorem integrableOn_Ioi_sq_mul_exp_neg_mul
    {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun r : ℝ => r ^ 2 * Real.exp (-(c * r))) (Ioi 0) := by
  have hvalue := integral_Ioi_sq_mul_exp_neg_mul hc
  have hne : (∫ r : ℝ in Ioi 0,
      r ^ 2 * Real.exp (-(c * r))) ≠ 0 := by
    rw [hvalue]
    positivity
  exact Integrable.of_integral_ne_zero hne

/-- Exact three-Laplace-term radial integral. -/
theorem integral_xiWardCubicPositiveShiftDampedRadialDensity
    {a eps : ℝ} (ha : 0 ≤ a) (heps : 0 < eps) :
    (∫ r : ℝ in Ioi 0,
        xiWardCubicPositiveShiftDampedRadialDensity a eps r) =
      2 / (2 * a + 2 * eps) ^ 3 -
        4 / (3 * a + 3 * eps / 2) ^ 3 +
          2 / (4 * a + eps) ^ 3 := by
  have h0 : 0 < 2 * a + 2 * eps := by positivity
  have h1 : 0 < 3 * a + 3 * eps / 2 := by positivity
  have h2 : 0 < 4 * a + eps := by positivity
  have hf0 := integrableOn_Ioi_sq_mul_exp_neg_mul h0
  have hf1 := integrableOn_Ioi_sq_mul_exp_neg_mul h1
  have hf2 := integrableOn_Ioi_sq_mul_exp_neg_mul h2
  have hpoint :
      (fun r : ℝ => xiWardCubicPositiveShiftDampedRadialDensity a eps r) =
        fun r : ℝ =>
          (r ^ 2 * Real.exp (-((2 * a + 2 * eps) * r)) -
            r ^ 2 * Real.exp (-((3 * a + 3 * eps / 2) * r))) -
              r ^ 2 * Real.exp (-((3 * a + 3 * eps / 2) * r)) +
              r ^ 2 * Real.exp (-((4 * a + eps) * r)) := by
    funext r
    rw [xiWardCubicPositiveShiftDampedRadialDensity,
      show -((2 * a + 2 * eps) * r) =
          -((a + eps) * r) + -((a + eps) * r) by ring,
      show -((3 * a + 3 * eps / 2) * r) =
          -((a + eps) * r) + -((2 * a + eps / 2) * r) by ring,
      show -((4 * a + eps) * r) =
          -((2 * a + eps / 2) * r) + -((2 * a + eps / 2) * r) by ring]
    simp only [Real.exp_add]
    ring
  rw [hpoint]
  change
    (∫ r : ℝ in Ioi 0,
      (((fun t : ℝ => t ^ 2 * Real.exp (-((2 * a + 2 * eps) * t))) -
        (fun t : ℝ => t ^ 2 * Real.exp (-((3 * a + 3 * eps / 2) * t))) -
        (fun t : ℝ => t ^ 2 * Real.exp (-((3 * a + 3 * eps / 2) * t))) +
        (fun t : ℝ => t ^ 2 * Real.exp (-((4 * a + eps) * t)))) r)) = _
  simp only [Pi.add_apply, Pi.sub_apply]
  have hsum := MeasureTheory.integral_add ((hf0.sub hf1).sub hf1) hf2
  have hsubOuter := MeasureTheory.integral_sub (hf0.sub hf1) hf1
  have hsubInner := MeasureTheory.integral_sub hf0 hf1
  simp only [Pi.sub_apply] at hsum hsubOuter hsubInner
  rw [hsum, hsubOuter, hsubInner,
    integral_Ioi_sq_mul_exp_neg_mul h0,
    integral_Ioi_sq_mul_exp_neg_mul h1,
    integral_Ioi_sq_mul_exp_neg_mul h2]
  ring

/-- Scaling removes the displacement dimension and leaves the anomaly profile. -/
theorem eps_cube_mul_integral_xiWardCubicPositiveShiftDampedRadialDensity
    {a eps : ℝ} (ha : 0 ≤ a) (heps : 0 < eps) :
    eps ^ 3 *
        (∫ r : ℝ in Ioi 0,
          xiWardCubicPositiveShiftDampedRadialDensity a eps r) =
      xiWardCubicPositiveShiftDiagonalAnomalyProfile (a / eps) := by
  rw [integral_xiWardCubicPositiveShiftDampedRadialDensity ha heps]
  unfold xiWardCubicPositiveShiftDiagonalAnomalyProfile
  field_simp [heps.ne']

/-- Critical-line anomaly is exactly one cubic Hellinger quantum. -/
theorem xiWardCubicPositiveShiftDiagonalAnomalyProfile_zero :
    xiWardCubicPositiveShiftDiagonalAnomalyProfile 0 = 115 / 108 := by
  norm_num [xiWardCubicPositiveShiftDiagonalAnomalyProfile]

/-- Damped diagonal anomaly is nonnegative throughout right half of critical strip. -/
theorem xiWardCubicPositiveShiftDiagonalAnomalyProfile_nonneg
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ xiWardCubicPositiveShiftDiagonalAnomalyProfile x := by
  have hscale :=
    eps_cube_mul_integral_xiWardCubicPositiveShiftDampedRadialDensity
      hx (by norm_num : (0 : ℝ) < 1)
  norm_num at hscale
  rw [← hscale]
  exact integral_nonneg fun r => by
    unfold xiWardCubicPositiveShiftDampedRadialDensity
    positivity

/-- Critical value is the global maximum of the dimensionless anomaly profile. -/
theorem xiWardCubicPositiveShiftDiagonalAnomalyProfile_le_quantum
    {x : ℝ} (hx : 0 ≤ x) :
    xiWardCubicPositiveShiftDiagonalAnomalyProfile x ≤ 115 / 108 := by
  rw [← sub_nonneg]
  have hfactor :
      (115 / 108 : ℝ) - xiWardCubicPositiveShiftDiagonalAnomalyProfile x =
        x * (1905 + 22179 * x + 113969 * x ^ 2 + 344706 * x ^ 3 +
          677700 * x ^ 4 + 871240 * x ^ 5 + 695520 * x ^ 6 +
          309120 * x ^ 7 + 58880 * x ^ 8) /
            (108 * (x + 1) ^ 3 * (2 * x + 1) ^ 3 * (4 * x + 1) ^ 3) := by
    unfold xiWardCubicPositiveShiftDiagonalAnomalyProfile
    have h0 : x + 1 ≠ 0 := by positivity
    have h1 : 2 * x + 1 ≠ 0 := by positivity
    have h2 : 4 * x + 1 ≠ 0 := by positivity
    field_simp [h0, h1, h2]
    ring
  rw [hfactor]
  positivity

/-- At large depth-to-shift ratio, normalized diagonal leakage vanishes. -/
theorem tendsto_xiWardCubicPositiveShiftDiagonalAnomalyProfile_atTop :
    Tendsto xiWardCubicPositiveShiftDiagonalAnomalyProfile atTop (nhds 0) := by
  have h0 := tendsto_mul_add_inv_atTop_nhds_zero (2 : ℝ) 2 (by norm_num)
  have h1 := tendsto_mul_add_inv_atTop_nhds_zero (3 : ℝ) (3 / 2) (by norm_num)
  have h2 := tendsto_mul_add_inv_atTop_nhds_zero (4 : ℝ) 1 (by norm_num)
  have h0' : Tendsto (fun x : ℝ => 2 * ((2 * x + 2)⁻¹) ^ 3)
      atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul (h0.pow 3)) using 1
    all_goals norm_num
  have h1' : Tendsto (fun x : ℝ => 4 * ((3 * x + 3 / 2)⁻¹) ^ 3)
      atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul (h1.pow 3)) using 1
    all_goals norm_num
  have h2' : Tendsto (fun x : ℝ => 2 * ((4 * x + 1)⁻¹) ^ 3)
      atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul (h2.pow 3)) using 1
    all_goals norm_num
  have h := (h0'.sub h1').add h2'
  convert h using 1
  · funext x
    unfold xiWardCubicPositiveShiftDiagonalAnomalyProfile
    field_simp
  · norm_num

/-- Complementary profile: zero on diagonal, asymptotically one quantum off diagonal. -/
def xiWardCubicPositiveShiftDiagonalSeparatorProfile (x : ℝ) : ℝ :=
  115 / 108 - xiWardCubicPositiveShiftDiagonalAnomalyProfile x

theorem xiWardCubicPositiveShiftDiagonalSeparatorProfile_zero :
    xiWardCubicPositiveShiftDiagonalSeparatorProfile 0 = 0 := by
  rw [xiWardCubicPositiveShiftDiagonalSeparatorProfile,
    xiWardCubicPositiveShiftDiagonalAnomalyProfile_zero]
  ring

theorem xiWardCubicPositiveShiftDiagonalSeparatorProfile_nonneg
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ xiWardCubicPositiveShiftDiagonalSeparatorProfile x := by
  unfold xiWardCubicPositiveShiftDiagonalSeparatorProfile
  linarith [xiWardCubicPositiveShiftDiagonalAnomalyProfile_le_quantum hx]

theorem xiWardCubicPositiveShiftDiagonalSeparatorProfile_le_quantum
    {x : ℝ} (hx : 0 ≤ x) :
    xiWardCubicPositiveShiftDiagonalSeparatorProfile x ≤ 115 / 108 := by
  unfold xiWardCubicPositiveShiftDiagonalSeparatorProfile
  linarith [xiWardCubicPositiveShiftDiagonalAnomalyProfile_nonneg hx]

/-- Every fixed strict-right displacement receives one full quantum as source shift shrinks. -/
theorem tendsto_xiWardCubicPositiveShiftDiagonalSeparatorProfile_div_nhdsGT_zero
    {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun eps : ℝ =>
        xiWardCubicPositiveShiftDiagonalSeparatorProfile (a / eps))
      (𝓝[>] (0 : ℝ)) (nhds (115 / 108)) := by
  have hratio : Tendsto (fun eps : ℝ => a / eps)
      (𝓝[>] (0 : ℝ)) atTop := by
    have htop : Tendsto (fun eps : ℝ => eps⁻¹ * a)
        (𝓝[>] (0 : ℝ)) atTop :=
      tendsto_inv_nhdsGT_zero.atTop_mul_pos ha tendsto_const_nhds
    convert htop using 1
    funext eps
    ring
  have hanomaly :=
    tendsto_xiWardCubicPositiveShiftDiagonalAnomalyProfile_atTop.comp hratio
  change Tendsto
    (fun eps : ℝ =>
      xiWardCubicPositiveShiftDiagonalAnomalyProfile (a / eps))
    (𝓝[>] (0 : ℝ)) (nhds 0) at hanomaly
  simpa only [xiWardCubicPositiveShiftDiagonalSeparatorProfile, sub_zero] using
    (tendsto_const_nhds (x := (115 / 108 : ℝ))).sub hanomaly

/-- Finite height windows need no divisor-dependent shift: one common source shift converges to
one quantum for every strict-right copy in the window. -/
theorem tendsto_finset_xiWardCubicPositiveShiftDiagonalSeparatorProfile_div
    {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 < a i) :
    Tendsto
      (fun eps : ℝ => ∑ i ∈ S,
        xiWardCubicPositiveShiftDiagonalSeparatorProfile (a i / eps))
      (𝓝[>] (0 : ℝ))
      (nhds ((S.card : ℝ) * (115 / 108))) := by
  have hsum := tendsto_finsetSum S fun i hi =>
    tendsto_xiWardCubicPositiveShiftDiagonalSeparatorProfile_div_nhdsGT_zero
      (ha i hi)
  convert hsum using 1
  simp

/-- Unit-normalized source mask for coupling to an independent lattice/frame receiver. -/
def xiWardCubicPositiveShiftDiagonalMask (x : ℝ) : ℝ :=
  (108 / 115) * xiWardCubicPositiveShiftDiagonalSeparatorProfile x

theorem xiWardCubicPositiveShiftDiagonalMask_zero :
    xiWardCubicPositiveShiftDiagonalMask 0 = 0 := by
  rw [xiWardCubicPositiveShiftDiagonalMask,
    xiWardCubicPositiveShiftDiagonalSeparatorProfile_zero, mul_zero]

theorem xiWardCubicPositiveShiftDiagonalMask_nonneg
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ xiWardCubicPositiveShiftDiagonalMask x := by
  unfold xiWardCubicPositiveShiftDiagonalMask
  exact mul_nonneg (by norm_num)
    (xiWardCubicPositiveShiftDiagonalSeparatorProfile_nonneg hx)

theorem xiWardCubicPositiveShiftDiagonalMask_le_one
    {x : ℝ} (hx : 0 ≤ x) :
    xiWardCubicPositiveShiftDiagonalMask x ≤ 1 := by
  unfold xiWardCubicPositiveShiftDiagonalMask
  have h := xiWardCubicPositiveShiftDiagonalSeparatorProfile_le_quantum hx
  nlinarith

theorem tendsto_xiWardCubicPositiveShiftDiagonalMask_div_nhdsGT_zero
    {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun eps : ℝ => xiWardCubicPositiveShiftDiagonalMask (a / eps))
      (𝓝[>] (0 : ℝ)) (nhds 1) := by
  have h :=
    (tendsto_xiWardCubicPositiveShiftDiagonalSeparatorProfile_div_nhdsGT_zero
      ha).const_mul (108 / 115 : ℝ)
  convert h using 1 <;> norm_num [xiWardCubicPositiveShiftDiagonalMask]

/-- On every finite strict-right packet, one common pre-divisor shift recovers packet cardinality. -/
theorem tendsto_finset_xiWardCubicPositiveShiftDiagonalMask_div
    {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 < a i) :
    Tendsto
      (fun eps : ℝ => ∑ i ∈ S,
        xiWardCubicPositiveShiftDiagonalMask (a i / eps))
      (𝓝[>] (0 : ℝ)) (nhds (S.card : ℝ)) := by
  have hsum := tendsto_finsetSum S fun i hi =>
    tendsto_xiWardCubicPositiveShiftDiagonalMask_div_nhdsGT_zero (ha i hi)
  convert hsum using 1
  simp

/-- Exact critical-line radial leakage law. -/
theorem eps_cube_mul_integral_xiWardCubicPositiveShiftDampedRadialDensity_zero
    {eps : ℝ} (heps : 0 < eps) :
    eps ^ 3 *
        (∫ r : ℝ in Ioi 0,
          xiWardCubicPositiveShiftDampedRadialDensity 0 eps r) =
      115 / 108 := by
  rw [eps_cube_mul_integral_xiWardCubicPositiveShiftDampedRadialDensity
    (le_refl 0) heps, zero_div,
    xiWardCubicPositiveShiftDiagonalAnomalyProfile_zero]

end

end RHTower
