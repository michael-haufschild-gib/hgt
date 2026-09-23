import GaloisForLFunctions.RHTower.RadialPSWFExteriorPhase
import GaloisForLFunctions.HTGeometry.LiouvilleGreenAmplitude

/-!
# Monotonicity of the exterior radial Liouville speed

The exterior radial speed `S(σ, z) = √((z² − σ²)/(z² − 1))` decomposes exactly as

```text
S² = 1 + (1 − σ²)/(z² − 1),
```

which makes its behaviour transparent: for a turning parameter in the physical range `σ ≤ 1` the
correction term is nonnegative and decreasing in `z`, so `S` decreases monotonically to `1` as the
radius grows, and equals `1` identically when `σ = 1`.

Monotonicity is exactly the hypothesis the Liouville–Green invariants require.  Since `S' ≤ 0`
here, the momentum invariant `S²u² + u'²` is nonincreasing along the exterior ray and the
amplitude invariant `u² + u'²/S²` is nondecreasing — adiabatic bounds with no integration, valid
for arbitrarily fast oscillation.
-/

open Set GaloisForLFunctions

noncomputable section

namespace RHTower

/-! ## The exact decomposition -/

theorem radialPSWFExteriorSpeed_arg_nonneg {sigma z : ℝ} (hsigma : sigma ^ (2 : ℕ) ≤ 1) (hz : 1 < z) :
    0 ≤ (z ^ (2 : ℕ) - sigma ^ (2 : ℕ)) / (z ^ (2 : ℕ) - 1) := by
  have hden : 0 < z ^ (2 : ℕ) - 1 := by nlinarith
  have hnum : 0 ≤ z ^ (2 : ℕ) - sigma ^ (2 : ℕ) := by nlinarith
  exact div_nonneg hnum hden.le

/-- **The exterior speed squared, decomposed.**  The deviation from the free speed `1` is the
nonnegative, decreasing correction `(1 − σ²)/(z² − 1)`. -/
theorem radialPSWFExteriorSpeed_sq {sigma z : ℝ} (hsigma : sigma ^ (2 : ℕ) ≤ 1) (hz : 1 < z) :
    radialPSWFExteriorSpeed sigma z ^ (2 : ℕ) = 1 + (1 - sigma ^ (2 : ℕ)) / (z ^ (2 : ℕ) - 1) := by
  rw [radialPSWFExteriorSpeed, Real.sq_sqrt (radialPSWFExteriorSpeed_arg_nonneg hsigma hz)]
  have hden : z ^ (2 : ℕ) - 1 ≠ 0 := by nlinarith
  field_simp
  ring

theorem radialPSWFExteriorSpeed_pos {sigma z : ℝ} (hsigma : sigma ^ (2 : ℕ) ≤ 1) (hz : 1 < z) :
    0 < radialPSWFExteriorSpeed sigma z := by
  have hden : 0 < z ^ (2 : ℕ) - 1 := by nlinarith
  have hnum : 0 < z ^ (2 : ℕ) - sigma ^ (2 : ℕ) := by nlinarith
  rw [radialPSWFExteriorSpeed]
  exact Real.sqrt_pos.mpr (div_pos hnum hden)

/-! ## Monotonicity -/

/-- **The exterior speed is nonincreasing in the radius.**  Immediate from the decomposition: the
only `z`-dependence is through `(z² − 1)` in a denominator with a nonnegative numerator. -/
theorem antitoneOn_radialPSWFExteriorSpeed {sigma : ℝ} (hsigma : sigma ^ (2 : ℕ) ≤ 1) :
    AntitoneOn (radialPSWFExteriorSpeed sigma) (Ioi 1) := by
  intro a ha b hb hab
  have ha1 : (1 : ℝ) < a := ha
  have hb1 : (1 : ℝ) < b := hb
  have hda : 0 < a ^ (2 : ℕ) - 1 := by nlinarith
  have hdb : 0 < b ^ (2 : ℕ) - 1 := by nlinarith
  have hle : (b ^ (2 : ℕ) - sigma ^ (2 : ℕ)) / (b ^ (2 : ℕ) - 1) ≤ (a ^ (2 : ℕ) - sigma ^ (2 : ℕ)) / (a ^ (2 : ℕ) - 1) := by
    have hcorr : (1 - sigma ^ (2 : ℕ)) / (b ^ (2 : ℕ) - 1) ≤ (1 - sigma ^ (2 : ℕ)) / (a ^ (2 : ℕ) - 1) := by
      apply div_le_div_of_nonneg_left (by linarith) hda
      nlinarith
    have ea : (a ^ (2 : ℕ) - sigma ^ (2 : ℕ)) / (a ^ (2 : ℕ) - 1) = 1 + (1 - sigma ^ (2 : ℕ)) / (a ^ (2 : ℕ) - 1) := by
      field_simp
      ring
    have eb : (b ^ (2 : ℕ) - sigma ^ (2 : ℕ)) / (b ^ (2 : ℕ) - 1) = 1 + (1 - sigma ^ (2 : ℕ)) / (b ^ (2 : ℕ) - 1) := by
      field_simp
      ring
    rw [ea, eb]
    linarith
  exact Real.sqrt_le_sqrt hle

/-! ## The exact derivative -/

/-- **Exact derivative of the exterior radial speed.**  Negative throughout the physical range,
which is the sign hypothesis the Liouville–Green invariants consume. -/
theorem hasDerivAt_radialPSWFExteriorSpeed {sigma z : ℝ} (hsigma : sigma ^ (2 : ℕ) ≤ 1) (hz : 1 < z) :
    HasDerivAt (radialPSWFExteriorSpeed sigma)
      (z * (sigma ^ (2 : ℕ) - 1) / ((z ^ (2 : ℕ) - 1) ^ (2 : ℕ) * radialPSWFExteriorSpeed sigma z)) z := by
  have hden : z ^ (2 : ℕ) - 1 ≠ 0 := by nlinarith
  have hdpos : (0 : ℝ) < z ^ (2 : ℕ) - 1 := by nlinarith
  have hnum : (0 : ℝ) < z ^ (2 : ℕ) - sigma ^ (2 : ℕ) := by nlinarith
  have hSpos := radialPSWFExteriorSpeed_pos hsigma hz
  have hsq : HasDerivAt (fun y : ℝ => y ^ (2 : ℕ)) (2 * z) z := by
    simpa using! (hasDerivAt_id z).pow 2
  have hnum' : HasDerivAt (fun y : ℝ => y ^ (2 : ℕ) - sigma ^ (2 : ℕ)) (2 * z) z := hsq.sub_const _
  have hden' : HasDerivAt (fun y : ℝ => y ^ (2 : ℕ) - 1) (2 * z) z := hsq.sub_const _
  have hr : HasDerivAt (fun y : ℝ => (y ^ (2 : ℕ) - sigma ^ (2 : ℕ)) / (y ^ (2 : ℕ) - 1))
      ((2 * z * (z ^ (2 : ℕ) - 1) - (z ^ (2 : ℕ) - sigma ^ (2 : ℕ)) * (2 * z)) / (z ^ (2 : ℕ) - 1) ^ (2 : ℕ)) z :=
    hnum'.div hden' hden
  have hrne : (z ^ (2 : ℕ) - sigma ^ (2 : ℕ)) / (z ^ (2 : ℕ) - 1) ≠ 0 := ne_of_gt (div_pos hnum hdpos)
  have hcomp := (Real.hasDerivAt_sqrt hrne).comp z hr
  have hSval : Real.sqrt ((z ^ (2 : ℕ) - sigma ^ (2 : ℕ)) / (z ^ (2 : ℕ) - 1))
      = radialPSWFExteriorSpeed sigma z := rfl
  have key : z * (sigma ^ (2 : ℕ) - 1) / ((z ^ (2 : ℕ) - 1) ^ (2 : ℕ) * radialPSWFExteriorSpeed sigma z)
      = 1 / (2 * Real.sqrt ((z ^ (2 : ℕ) - sigma ^ (2 : ℕ)) / (z ^ (2 : ℕ) - 1)))
        * ((2 * z * (z ^ (2 : ℕ) - 1) - (z ^ (2 : ℕ) - sigma ^ (2 : ℕ)) * (2 * z)) / (z ^ (2 : ℕ) - 1) ^ (2 : ℕ)) := by
    rw [hSval]
    field_simp
    ring
  rw [key]
  exact hcomp

/-- The derivative is nonpositive: the speed decays. -/
theorem radialPSWFExteriorSpeed_deriv_nonpos {sigma z : ℝ} (hsigma : sigma ^ (2 : ℕ) ≤ 1) (hz : 1 < z) :
    z * (sigma ^ (2 : ℕ) - 1) / ((z ^ (2 : ℕ) - 1) ^ (2 : ℕ) * radialPSWFExteriorSpeed sigma z) ≤ 0 := by
  have hz0 : (0 : ℝ) < z := lt_trans zero_lt_one hz
  have hSpos := radialPSWFExteriorSpeed_pos hsigma hz
  have hden : (0 : ℝ) < (z ^ (2 : ℕ) - 1) ^ (2 : ℕ) * radialPSWFExteriorSpeed sigma z := by
    have h1 : (0 : ℝ) < z ^ (2 : ℕ) - 1 := by nlinarith
    positivity
  apply div_nonpos_of_nonpos_of_nonneg _ hden.le
  nlinarith

/-! ## The radial Liouville–Green invariants -/

/-- **The momentum invariant is nonincreasing along the exterior ray.**  Its derivative carries
the sign of the speed derivative, which is negative in the physical range. -/
theorem radial_lgMomentum_deriv_nonpos {sigma z : ℝ} (hsigma : sigma ^ (2 : ℕ) ≤ 1) (hz : 1 < z)
    (u : ℝ → ℝ) :
    2 * (z * (sigma ^ (2 : ℕ) - 1) / ((z ^ (2 : ℕ) - 1) ^ (2 : ℕ) * radialPSWFExteriorSpeed sigma z))
        * radialPSWFExteriorSpeed sigma z * u z ^ (2 : ℕ) ≤ 0 := by
  have hneg := radialPSWFExteriorSpeed_deriv_nonpos hsigma hz
  have hSpos := radialPSWFExteriorSpeed_pos hsigma hz
  have h2 : 2 * (z * (sigma ^ (2 : ℕ) - 1) / ((z ^ (2 : ℕ) - 1) ^ (2 : ℕ) * radialPSWFExteriorSpeed sigma z)) ≤ 0 :=
    by linarith
  have hrest : 0 ≤ radialPSWFExteriorSpeed sigma z * u z ^ (2 : ℕ) :=
    mul_nonneg hSpos.le (sq_nonneg _)
  calc 2 * (z * (sigma ^ (2 : ℕ) - 1) / ((z ^ (2 : ℕ) - 1) ^ (2 : ℕ) * radialPSWFExteriorSpeed sigma z))
        * radialPSWFExteriorSpeed sigma z * u z ^ (2 : ℕ)
      = (2 * (z * (sigma ^ (2 : ℕ) - 1) / ((z ^ (2 : ℕ) - 1) ^ (2 : ℕ) * radialPSWFExteriorSpeed sigma z)))
        * (radialPSWFExteriorSpeed sigma z * u z ^ (2 : ℕ)) := by ring
    _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h2 hrest

/-- **The Liouville–Green momentum invariant of the exterior radial equation, with its exact
derivative.**  Combined with `radial_lgMomentum_deriv_nonpos` this says `S²u² + u'²` is
nonincreasing in the radius. -/
theorem hasDerivAt_radial_lgMomentum {sigma z : ℝ} (hsigma : sigma ^ (2 : ℕ) ≤ 1) (hz : 1 < z)
    {u v : ℝ → ℝ} (hu : HasDerivAt u (v z) z)
    (hv : HasDerivAt v (-(radialPSWFExteriorSpeed sigma z ^ (2 : ℕ)) * u z) z) :
    HasDerivAt (lgMomentum (radialPSWFExteriorSpeed sigma) u v)
      (2 * (z * (sigma ^ (2 : ℕ) - 1) / ((z ^ (2 : ℕ) - 1) ^ (2 : ℕ) * radialPSWFExteriorSpeed sigma z))
        * radialPSWFExteriorSpeed sigma z * u z ^ (2 : ℕ)) z :=
  hasDerivAt_lgMomentum (hasDerivAt_radialPSWFExteriorSpeed hsigma hz) hu hv

/-- **The amplitude invariant is nondecreasing along the exterior ray**, with its exact
derivative. -/
theorem hasDerivAt_radial_lgAmplitude {sigma z : ℝ} (hsigma : sigma ^ (2 : ℕ) ≤ 1) (hz : 1 < z)
    {u v : ℝ → ℝ} (hu : HasDerivAt u (v z) z)
    (hv : HasDerivAt v (-(radialPSWFExteriorSpeed sigma z ^ (2 : ℕ)) * u z) z) :
    HasDerivAt (lgAmplitude (radialPSWFExteriorSpeed sigma) u v)
      (-(2 * (z * (sigma ^ (2 : ℕ) - 1) / ((z ^ (2 : ℕ) - 1) ^ (2 : ℕ) * radialPSWFExteriorSpeed sigma z))
        * v z ^ (2 : ℕ) / radialPSWFExteriorSpeed sigma z ^ (3 : ℕ))) z :=
  hasDerivAt_lgAmplitude (hasDerivAt_radialPSWFExteriorSpeed hsigma hz)
    (ne_of_gt (radialPSWFExteriorSpeed_pos hsigma hz)) hu hv

end RHTower

end
