import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring

/-!
# Weighted cylindrical viscous-flux cancellation

Proposition 8.4 of the supplied Navier--Stokes paper cancels two radial viscous
integrals by integration by parts.  Their weighted densities are in fact single
total derivatives.  This file records both flux factorizations, their exact
boundary formulas, and the compact-support endpoint corollaries used in (8.16).
It also records the first pressure-moment integration by parts used in Lemma 4.3.
-/

namespace GaloisForLFunctions.HTGeometry.NavierStokesViscousFluxCancellation

open MeasureTheory Set

noncomputable section

/-- `r²(v'' + r⁻¹v' - r⁻²v)` without division by `r`. -/
def azimuthalViscousDensity (v : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ 2 * deriv (deriv v) r + r * deriv v r - v r

/-- Boundary flux whose derivative is the weighted azimuthal viscous density. -/
def azimuthalViscousFlux (v : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ 2 * deriv v r - r * v r

/-- `r(v'' + r⁻¹v')` without division by `r`. -/
def axialViscousDensity (v : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * deriv (deriv v) r + deriv v r

/-- Boundary flux whose derivative is the weighted axial viscous density. -/
def axialViscousFlux (v : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * deriv v r

/-- Density in the pressure-moment integration by parts in Proposition 8.4. -/
def pressureMomentDensity (p : ℝ → ℝ) (r : ℝ) : ℝ :=
  2 * r * p r + r ^ 2 * deriv p r

def pressureMomentFlux (p : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ 2 * p r

/-- Pointwise azimuthal flux factorization used in Proposition 8.4. -/
theorem azimuthalViscousFlux_hasDerivAt {v : ℝ → ℝ} {r : ℝ}
    (hv : DifferentiableAt ℝ v r) (hv' : DifferentiableAt ℝ (deriv v) r) :
    HasDerivAt (azimuthalViscousFlux v) (azimuthalViscousDensity v r) r := by
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have h := (hsq.mul hv'.hasDerivAt).sub ((hasDerivAt_id r).mul hv.hasDerivAt)
  have hfun : (fun s : ℝ => s ^ 2) * deriv v - id * v = azimuthalViscousFlux v := by
    funext s
    simp [azimuthalViscousFlux]
  rw [← hfun]
  apply h.congr_deriv
  simp [azimuthalViscousDensity]
  ring

/-- Pointwise axial flux factorization used in Proposition 8.4. -/
theorem axialViscousFlux_hasDerivAt {v : ℝ → ℝ} {r : ℝ}
    (hv' : DifferentiableAt ℝ (deriv v) r) :
    HasDerivAt (axialViscousFlux v) (axialViscousDensity v r) r := by
  have h := (hasDerivAt_id r).mul hv'.hasDerivAt
  have hfun : id * deriv v = axialViscousFlux v := by
    funext s
    simp [axialViscousFlux]
  rw [← hfun]
  apply h.congr_deriv
  simp [axialViscousDensity]
  ring

/-- Flux factorization for the pressure moment used in equation (8.16). -/
theorem pressureMomentFlux_hasDerivAt {p : ℝ → ℝ} {r : ℝ}
    (hp : DifferentiableAt ℝ p r) :
    HasDerivAt (pressureMomentFlux p) (pressureMomentDensity p r) r := by
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have h := hsq.mul hp.hasDerivAt
  have hfun : (fun s : ℝ => s ^ 2) * p = pressureMomentFlux p := by
    funext s
    simp [pressureMomentFlux]
  rw [← hfun]
  apply h.congr_deriv
  simp [pressureMomentDensity]

theorem integral_azimuthalViscousDensity_eq_boundary {v : ℝ → ℝ} (a b : ℝ)
    (hv : Differentiable ℝ v) (hv' : Differentiable ℝ (deriv v))
    (hv'' : Continuous (deriv (deriv v))) :
    (∫ r in a..b, azimuthalViscousDensity v r) =
      azimuthalViscousFlux v b - azimuthalViscousFlux v a := by
  apply intervalIntegral.integral_deriv_eq_sub'
  · funext r
    exact (azimuthalViscousFlux_hasDerivAt (hv r) (hv' r)).deriv
  · intro r _
    exact (azimuthalViscousFlux_hasDerivAt (hv r) (hv' r)).differentiableAt
  · exact (((continuous_pow 2).mul hv''
      |>.add (continuous_id.mul hv'.continuous)).sub hv.continuous).continuousOn

/-- First radial viscous cancellation displayed in the proof of Proposition 8.4. -/
theorem integral_azimuthalViscousDensity_eq_zero {v : ℝ → ℝ} (a b : ℝ)
    (hv : Differentiable ℝ v) (hv' : Differentiable ℝ (deriv v))
    (hv'' : Continuous (deriv (deriv v)))
    (hva : v a = 0) (hvb : v b = 0) (hv'a : deriv v a = 0) (hv'b : deriv v b = 0) :
    (∫ r in a..b, azimuthalViscousDensity v r) = 0 := by
  rw [integral_azimuthalViscousDensity_eq_boundary a b hv hv' hv'']
  simp [azimuthalViscousFlux, hva, hvb, hv'a, hv'b]

theorem integral_axialViscousDensity_eq_boundary {v : ℝ → ℝ} (a b : ℝ)
    (hv' : Differentiable ℝ (deriv v)) (hv'' : Continuous (deriv (deriv v))) :
    (∫ r in a..b, axialViscousDensity v r) =
      axialViscousFlux v b - axialViscousFlux v a := by
  apply intervalIntegral.integral_deriv_eq_sub'
  · funext r
    exact (axialViscousFlux_hasDerivAt (hv' r)).deriv
  · intro r _
    exact (axialViscousFlux_hasDerivAt (hv' r)).differentiableAt
  · exact ((continuous_id.mul hv'').add hv'.continuous).continuousOn

/-- Second radial viscous cancellation displayed in the proof of Proposition 8.4. -/
theorem integral_axialViscousDensity_eq_zero {v : ℝ → ℝ} (a b : ℝ)
    (hv' : Differentiable ℝ (deriv v)) (hv'' : Continuous (deriv (deriv v)))
    (hv'a : deriv v a = 0) (hv'b : deriv v b = 0) :
    (∫ r in a..b, axialViscousDensity v r) = 0 := by
  rw [integral_axialViscousDensity_eq_boundary a b hv' hv'']
  simp [axialViscousFlux, hv'a, hv'b]

theorem integral_pressureMomentDensity_eq_boundary {p : ℝ → ℝ} (a b : ℝ)
    (hp : Differentiable ℝ p) (hp' : Continuous (deriv p)) :
    (∫ r in a..b, pressureMomentDensity p r) =
      pressureMomentFlux p b - pressureMomentFlux p a := by
  apply intervalIntegral.integral_deriv_eq_sub'
  · funext r
    exact (pressureMomentFlux_hasDerivAt (hp r)).deriv
  · intro r _
    exact (pressureMomentFlux_hasDerivAt (hp r)).differentiableAt
  · exact (((continuous_const.mul continuous_id).mul hp.continuous).add
      ((continuous_pow 2).mul hp')).continuousOn

/-- Integrated pressure-moment identity appearing in the proof of Proposition 8.4. -/
theorem pressureMoment_integral_identity {p : ℝ → ℝ} (a b : ℝ)
    (hp : Differentiable ℝ p) (hp' : Continuous (deriv p)) :
    2 * (∫ r in a..b, r * p r) + (∫ r in a..b, r ^ 2 * deriv p r) =
      pressureMomentFlux p b - pressureMomentFlux p a := by
  have h := integral_pressureMomentDensity_eq_boundary a b hp hp'
  have hdensity : pressureMomentDensity p =
      fun r => 2 * (r * p r) + r ^ 2 * deriv p r := by
    funext r
    simp [pressureMomentDensity, mul_assoc]
  rw [hdensity] at h
  change (∫ r in a..b, 2 * (r * p r) + r ^ 2 * deriv p r) = _ at h
  have hfirst : IntervalIntegrable (fun r : ℝ => 2 * (r * p r)) volume a b :=
    (continuous_const.mul (continuous_id.mul hp.continuous)).intervalIntegrable a b
  have hsecond : IntervalIntegrable (fun r : ℝ => r ^ 2 * deriv p r) volume a b :=
    ((continuous_pow 2).mul hp').intervalIntegrable a b
  have hsplit := intervalIntegral.integral_add (f := fun r => 2 * (r * p r))
    (g := fun r => r ^ 2 * deriv p r) hfirst hsecond
  rw [hsplit, intervalIntegral.integral_const_mul] at h
  exact h

/-- Compact-support form of the pressure-moment relation used to derive (8.16). -/
theorem pressureMoment_integral_eq_neg_half {p : ℝ → ℝ} (a b : ℝ)
    (hp : Differentiable ℝ p) (hp' : Continuous (deriv p))
    (hpa : p a = 0) (hpb : p b = 0) :
    (∫ r in a..b, r * p r) =
      -(1 / 2 : ℝ) * ∫ r in a..b, r ^ 2 * deriv p r := by
  have h := pressureMoment_integral_identity a b hp hp'
  simp [pressureMomentFlux, hpa, hpb] at h
  linarith

/-- Linear radial pressure flux used in Lemma 4.3. -/
def linearPressureFlux (p : ℝ → ℝ) (r : ℝ) : ℝ := r * p r

theorem linearPressureFlux_hasDerivAt {p : ℝ → ℝ} {r : ℝ}
    (hp : DifferentiableAt ℝ p r) :
    HasDerivAt (linearPressureFlux p) (p r + r * deriv p r) r := by
  have h := (hasDerivAt_id r).mul hp.hasDerivAt
  have hfun : id * p = linearPressureFlux p := by
    funext s
    rfl
  rw [← hfun]
  simpa using h

/-- Integration by parts for the first radial pressure moment. -/
theorem pressure_firstMoment_integral_identity {p : ℝ → ℝ} (a b : ℝ)
    (hp : Differentiable ℝ p) (hp' : Continuous (deriv p)) :
    (∫ r in a..b, p r) + (∫ r in a..b, r * deriv p r) =
      linearPressureFlux p b - linearPressureFlux p a := by
  rw [← intervalIntegral.integral_add]
  apply intervalIntegral.integral_deriv_eq_sub'
  · funext r
    exact (linearPressureFlux_hasDerivAt (hp r)).deriv
  · intro r _
    exact (linearPressureFlux_hasDerivAt (hp r)).differentiableAt
  · exact (hp.continuous.add (continuous_id.mul hp')).continuousOn
  · exact hp.continuous.intervalIntegrable a b
  · exact (continuous_id.mul hp').intervalIntegrable a b

/-- Pressure integration identity in the proof of Lemma 4.3. -/
theorem pressure_cumulativeMoment_identity {p E : ℝ → ℝ} (X : ℝ)
    (hp : Differentiable ℝ p) (hp' : Continuous (deriv p))
    (hcentrifugal : ∀ r, r * deriv p r = E r ^ 2 / 2) :
    (∫ r in (0 : ℝ)..X, p r) =
      X * p X - ∫ r in (0 : ℝ)..X, E r ^ 2 / 2 := by
  have h := pressure_firstMoment_integral_identity 0 X hp hp'
  simp only [linearPressureFlux, zero_mul, sub_zero] at h
  have hreplace :
      (∫ r in (0 : ℝ)..X, r * deriv p r) =
        ∫ r in (0 : ℝ)..X, E r ^ 2 / 2 := by
    apply intervalIntegral.integral_congr
    intro r _
    exact hcentrifugal r
  rw [hreplace] at h
  linarith

end

end GaloisForLFunctions.HTGeometry.NavierStokesViscousFluxCancellation
