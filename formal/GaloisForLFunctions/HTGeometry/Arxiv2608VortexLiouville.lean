import GaloisForLFunctions.RHTower.BesselNormalForm
import GaloisForLFunctions.RHTower.BesselJZeroEnvelope

/-!
# Vortex Liouville transform from arXiv:2608.28167

The paper removes the cylindrical first derivative by writing `psi(r,T) = u(r,T) / sqrt(r)`.
This module certifies the resulting `ell^(2 : ℕ) - 1/4` centrifugal coefficient, its radial norm-density
invariance, and the exact order-zero linear mode already present in the corpus.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Positive frequency, preventing the scaled Bessel argument from crossing its singular endpoint. -/
abbrev VortexPositiveFrequency := Set.Ioi (0 : ℝ)

/-- Positive cylindrical radius. -/
abbrev VortexPositiveRadius := Set.Ioi (0 : ℝ)

/-- Coefficient produced by the cylindrical Liouville substitution in equation (9). -/
def vortexCentrifugalCoefficient (ell : ℤ) : ℝ :=
  (ell : ℝ) ^ (2 : ℕ) - 1 / 4

@[simp] theorem vortexCentrifugalCoefficient_zero :
    vortexCentrifugalCoefficient 0 = -1 / 4 := by
  norm_num [vortexCentrifugalCoefficient]

@[simp] theorem vortexCentrifugalCoefficient_one :
    vortexCentrifugalCoefficient 1 = 3 / 4 := by
  norm_num [vortexCentrifugalCoefficient]

@[simp] theorem vortexCentrifugalCoefficient_neg (ell : ℤ) :
    vortexCentrifugalCoefficient (-ell) = vortexCentrifugalCoefficient ell := by
  simp [vortexCentrifugalCoefficient]

/-- Value jet for `psi = u / sqrt(r)`. -/
def vortexLiouvilleValue (r u : ℝ) : ℝ :=
  u / Real.sqrt r

/-- First radial jet induced by `psi = u / sqrt(r)`. -/
def vortexLiouvilleFirst (r u u₁ : ℝ) : ℝ :=
  u₁ / Real.sqrt r - u / (2 * r * Real.sqrt r)

/-- Second radial jet induced by `psi = u / sqrt(r)`. -/
def vortexLiouvilleSecond (r u u₁ u₂ : ℝ) : ℝ :=
  u₂ / Real.sqrt r - u₁ / (r * Real.sqrt r) +
    3 * u / (4 * r ^ (2 : ℕ) * Real.sqrt r)

/-- Cylindrical radial operator before the Liouville substitution. -/
def vortexCylindricalRadialResidual
    (ell : ℤ) (r psi psi₁ psi₂ : ℝ) : ℝ :=
  psi₂ + psi₁ / r - (ell : ℝ) ^ (2 : ℕ) / r ^ (2 : ℕ) * psi

/-- Radial operator after the Liouville substitution. -/
def vortexLiouvilleRadialResidual
    (ell : ℤ) (r u u₂ : ℝ) : ℝ :=
  u₂ - vortexCentrifugalCoefficient ell / r ^ (2 : ℕ) * u

/-- Equation (9), as an exact jet identity: the cylindrical operator is conjugate to the
Schrodinger-form operator with coefficient `ell^(2 : ℕ) - 1/4`. -/
theorem vortex_liouville_radial_identity
    (ell : ℤ) (r : VortexPositiveRadius) (u u₁ u₂ : ℝ) :
    vortexCylindricalRadialResidual ell r
        (vortexLiouvilleValue r u)
        (vortexLiouvilleFirst r u u₁)
        (vortexLiouvilleSecond r u u₁ u₂) =
      vortexLiouvilleRadialResidual ell r u u₂ / Real.sqrt r := by
  have hr : (0 : ℝ) < r := r.property
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hr
  have hs : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hr
  simp only [vortexCylindricalRadialResidual, vortexLiouvilleValue,
    vortexLiouvilleFirst, vortexLiouvilleSecond, vortexLiouvilleRadialResidual,
    vortexCentrifugalCoefficient]
  field_simp [hr0, ne_of_gt hs]
  ring

/-- Pointwise version of the norm identity in equation (10): multiplication by the cylindrical
Jacobian `r` exactly cancels division by `sqrt(r)`. -/
theorem vortex_liouville_norm_density (r : VortexPositiveRadius) (u : ℂ) :
    ‖u / (Real.sqrt (r : ℝ) : ℂ)‖ ^ (2 : ℕ) * (r : ℝ) = ‖u‖ ^ (2 : ℕ) := by
  have hr : (0 : ℝ) < r := r.property
  have hs : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hr
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, div_pow]
  field_simp [ne_of_gt hs]
  nlinarith [Real.sq_sqrt hr.le]

/-- Radial integral form of equation (10), valid whether the integrals are finite or not. -/
theorem vortex_liouville_radial_norm_integral (u : ℝ → ℂ) :
    (∫ r : ℝ in Set.Ioi 0,
        ‖u r / (Real.sqrt r : ℂ)‖ ^ (2 : ℕ) * r) =
      ∫ r : ℝ in Set.Ioi 0, ‖u r‖ ^ (2 : ℕ) := by
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  exact vortex_liouville_norm_density ⟨r, hr⟩ (u r)

/-- Full two-dimensional norm equality in equation (10), obtained without integrability side
conditions because both extended integral conventions see the same pointwise density. -/
theorem vortex_liouville_spatiotemporal_norm_integral (u : ℝ → ℝ → ℂ) :
    (∫ T : ℝ, ∫ r : ℝ in Set.Ioi 0,
        ‖u T r / (Real.sqrt r : ℂ)‖ ^ (2 : ℕ) * r) =
      ∫ T : ℝ, ∫ r : ℝ in Set.Ioi 0, ‖u T r‖ ^ (2 : ℕ) := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with T
  exact vortex_liouville_radial_norm_integral (u T)

/-! ## Full stationary nonlinear equation -/

/-- Squared-Bessel guide `V(r) = gamma J_0(r)^(2 : ℕ)` from equations (4) and (6). -/
def vortexBesselWaveguide (gamma r : ℝ) : ℝ :=
  gamma * GaloisForLFunctions.RHTower.besselJ0 r ^ (2 : ℕ)

@[simp] theorem vortexBesselWaveguide_zero (gamma : ℝ) :
    vortexBesselWaveguide gamma 0 = gamma := by
  simp [vortexBesselWaveguide, GaloisForLFunctions.RHTower.besselJ0]

/-- A nonnegative guide depth produces a pointwise potential between zero and its depth. -/
theorem vortexBesselWaveguide_mem_Icc
    (gamma : Set.Ici (0 : ℝ)) (r : ℝ) :
    vortexBesselWaveguide gamma r ∈ Set.Icc 0 (gamma : ℝ) := by
  have hJ := GaloisForLFunctions.RHTower.abs_besselJ0_le_one r
  have hJsq : GaloisForLFunctions.RHTower.besselJ0 r ^ (2 : ℕ) ≤ 1 := by
    have hprod : 0 ≤
        (1 - |GaloisForLFunctions.RHTower.besselJ0 r|) *
          (1 + |GaloisForLFunctions.RHTower.besselJ0 r|) :=
      mul_nonneg (sub_nonneg.mpr hJ) (by positivity)
    nlinarith [sq_abs (GaloisForLFunctions.RHTower.besselJ0 r)]
  constructor
  · exact mul_nonneg gamma.property (sq_nonneg _)
  · exact mul_le_of_le_one_right gamma.property hJsq

/-- Stationary cylindrical residual in equation (8), including temporal and cubic terms. -/
def vortexStationaryResidual
    (ell : ℤ) (beta potential r psi psiᵣ psiᵣᵣ psiTT : ℝ) : ℝ :=
  -beta * psi + psiTT + vortexCylindricalRadialResidual ell r psi psiᵣ psiᵣᵣ +
    (potential + psi ^ (2 : ℕ)) * psi

/-- Transformed stationary residual in equation (9). -/
def vortexLiouvilleStationaryResidual
    (ell : ℤ) (beta potential r u uᵣᵣ uTT : ℝ) : ℝ :=
  uTT + vortexLiouvilleRadialResidual ell r u uᵣᵣ +
    (potential - beta + u ^ (2 : ℕ) / r) * u

/-- Equations (8)--(9) as a full exact identity, including cubic scaling `psi^(3 : ℕ) -> u^(3 : ℕ)/r`. -/
theorem vortex_liouville_stationary_identity
    (ell : ℤ) (beta potential : ℝ) (r : VortexPositiveRadius)
    (u uᵣ uᵣᵣ uTT : ℝ) :
    Real.sqrt (r : ℝ) *
        vortexStationaryResidual ell beta potential r
          (vortexLiouvilleValue r u)
          (vortexLiouvilleFirst r u uᵣ)
          (vortexLiouvilleSecond r u uᵣ uᵣᵣ)
          (uTT / Real.sqrt r) =
      vortexLiouvilleStationaryResidual ell beta potential r u uᵣᵣ uTT := by
  have hr : (0 : ℝ) < r := r.property
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hr
  have hs : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hr
  simp only [vortexStationaryResidual, vortexLiouvilleStationaryResidual,
    vortexCylindricalRadialResidual, vortexLiouvilleRadialResidual,
    vortexLiouvilleValue, vortexLiouvilleFirst, vortexLiouvilleSecond,
    vortexCentrifugalCoefficient]
  field_simp [hr0, ne_of_gt hs]
  rw [Real.sq_sqrt hr.le]
  ring

/-! ## Exact corpus mode for the linear order-zero specialization -/

/-- Scaled order-zero vortex mode `sqrt(eta r) J_0(eta r)`. -/
def vortexLinearJ0Mode (eta : VortexPositiveFrequency) (r : ℝ) : ℝ :=
  GaloisForLFunctions.RHTower.besselNormalForm ((eta : ℝ) * r)

def vortexLinearJ0ModeDeriv (eta : VortexPositiveFrequency) (r : ℝ) : ℝ :=
  GaloisForLFunctions.RHTower.besselNormalFormDeriv ((eta : ℝ) * r) * (eta : ℝ)

def vortexLinearJ0ModeSecond (eta : VortexPositiveFrequency) (r : ℝ) : ℝ :=
  (eta : ℝ) ^ (2 : ℕ) * GaloisForLFunctions.RHTower.besselNormalFormSecond ((eta : ℝ) * r)

theorem hasDerivAt_vortexLinearJ0Mode
    (eta : VortexPositiveFrequency) (r : VortexPositiveRadius) :
    HasDerivAt (vortexLinearJ0Mode eta) (vortexLinearJ0ModeDeriv eta r) r := by
  have harg : 0 < (eta : ℝ) * (r : ℝ) := mul_pos eta.property r.property
  have hinner : HasDerivAt (fun x : ℝ => (eta : ℝ) * x) (eta : ℝ) r := by
    simpa using (hasDerivAt_id (r : ℝ)).const_mul (eta : ℝ)
  exact (GaloisForLFunctions.RHTower.hasDerivAt_besselNormalForm harg).comp (r : ℝ) hinner

theorem hasDerivAt_vortexLinearJ0ModeDeriv
    (eta : VortexPositiveFrequency) (r : VortexPositiveRadius) :
    HasDerivAt (vortexLinearJ0ModeDeriv eta) (vortexLinearJ0ModeSecond eta r) r := by
  have harg : 0 < (eta : ℝ) * (r : ℝ) := mul_pos eta.property r.property
  have hinner : HasDerivAt (fun x : ℝ => (eta : ℝ) * x) (eta : ℝ) r := by
    simpa using (hasDerivAt_id (r : ℝ)).const_mul (eta : ℝ)
  have h := (GaloisForLFunctions.RHTower.hasDerivAt_besselNormalFormDeriv harg).comp
    (r : ℝ) hinner
  have h' := h.mul_const (eta : ℝ)
  have hval : GaloisForLFunctions.RHTower.besselNormalFormSecond
        ((eta : ℝ) * (r : ℝ)) * (eta : ℝ) * (eta : ℝ) =
      vortexLinearJ0ModeSecond eta r := by
    rw [vortexLinearJ0ModeSecond]
    ring
  rw [hval] at h'
  exact h'

/-- Linear stationary residual obtained from equation (9) after freezing the temporal direction and
removing nonlinear and guiding terms. -/
def vortexLinearStationaryResidual
    (ell : ℤ) (waveSq r value second : ℝ) : ℝ :=
  second + (waveSq - vortexCentrifugalCoefficient ell / r ^ (2 : ℕ)) * value

/-- Existing corpus normal form solves every positive-frequency, order-zero linear specialization
of the vortex equation exactly. -/
theorem vortexLinearJ0Mode_residual_zero
    (eta : VortexPositiveFrequency) (r : VortexPositiveRadius) :
    vortexLinearStationaryResidual 0 ((eta : ℝ) ^ (2 : ℕ)) r
      (vortexLinearJ0Mode eta r) (vortexLinearJ0ModeSecond eta r) = 0 := by
  have harg : 0 < (eta : ℝ) * (r : ℝ) := mul_pos eta.property r.property
  have hode := GaloisForLFunctions.RHTower.besselNormalForm_ode harg
  have heta : (eta : ℝ) ≠ 0 := ne_of_gt eta.property
  have hr : (r : ℝ) ≠ 0 := ne_of_gt r.property
  simp only [vortexLinearStationaryResidual, vortexCentrifugalCoefficient_zero,
    vortexLinearJ0Mode, vortexLinearJ0ModeSecond]
  calc
    (eta : ℝ) ^ (2 : ℕ) * GaloisForLFunctions.RHTower.besselNormalFormSecond
          ((eta : ℝ) * (r : ℝ)) +
        ((eta : ℝ) ^ (2 : ℕ) - (-1 / 4) / (r : ℝ) ^ (2 : ℕ)) *
          GaloisForLFunctions.RHTower.besselNormalForm ((eta : ℝ) * (r : ℝ)) =
      (eta : ℝ) ^ (2 : ℕ) *
        (GaloisForLFunctions.RHTower.besselNormalFormSecond ((eta : ℝ) * (r : ℝ)) +
          (1 + 1 / (4 * ((eta : ℝ) * (r : ℝ)) ^ (2 : ℕ))) *
            GaloisForLFunctions.RHTower.besselNormalForm ((eta : ℝ) * (r : ℝ))) := by
        field_simp [heta, hr]
        ring
    _ = 0 := by rw [hode, mul_zero]

end GaloisForLFunctions.HTGeometry
