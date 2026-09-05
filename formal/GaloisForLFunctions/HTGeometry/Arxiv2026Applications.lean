import GaloisForLFunctions.HTGeometry.Arxiv2608AnisotropicBessel
import GaloisForLFunctions.HTGeometry.Arxiv2608ExprelFilon
import GaloisForLFunctions.HTGeometry.Arxiv2608FilonBesselSeries
import GaloisForLFunctions.HTGeometry.Arxiv2608VortexLiouville
import GaloisForLFunctions.HTGeometry.Arxiv2607FaradayFloquet

/-!
# Cross-paper applications from four 2026 arXiv papers

This module records theorem-level intersections between the four source papers and the existing
corpus.  The main new bridge is the order-one Liouville normal form: the `J₁` equation exposed by
the anisotropic-beam paper supplies exact dipolar radial modes for both the optical-vortex and
Faraday--Rayleigh--Taylor equations.
-/

noncomputable section

open MeasureTheory
open scoped Interval

namespace GaloisForLFunctions.HTGeometry

/-! ## Shared order-zero Bessel kernel -/

/-- The squared-Bessel vortex guide is the square of the isotropic anisotropic-beam radial mode. -/
theorem vortexWaveguide_eq_squared_escobarMode (gamma r : ℝ) :
    vortexBesselWaveguide gamma r = gamma * escobarIsotropicRadialMode 1 r ^ 2 := by
  simp [vortexBesselWaveguide, escobarIsotropicRadialMode]

/-- The order-zero vortex Liouville mode is the half-density lift of the beam radial mode. -/
theorem vortexLinearJ0Mode_eq_liouville_escobarMode
    (eta : VortexPositiveFrequency) (r : ℝ) :
    vortexLinearJ0Mode eta r =
      Real.sqrt ((eta : ℝ) * r) * escobarIsotropicRadialMode eta r := by
  rfl

/-- The Filon `J₀` series is simultaneously an exact series for the beam/Faraday radial kernel. -/
theorem escobarFaradayRadialMode_series (b u : ℝ) :
    ((escobarIsotropicRadialMode b u : ℝ) : ℂ) =
      ∑' k : ℕ, (-1 : ℂ) ^ k * ((b * u : ℝ) : ℂ) ^ (2 * k) /
        ((4 : ℂ) ^ k * ((k.factorial : ℂ) ^ 2)) := by
  exact filonBesselKernel_series b u

/-- Integer anisotropies from the beam paper select exactly the arbitrary-order Filon/Poincare
Bessel carrier already present in the corpus. -/
def escobarIntegerOrderMode (n : ℕ) (eta r : ℝ) : ℝ :=
  besselJ n (eta * r)

theorem escobarIntegerOrderMode_series (n : ℕ) (eta r : ℝ) :
    escobarIntegerOrderMode n eta r =
      ∑' j : ℕ, (-1 : ℝ) ^ j * (eta * r / 2) ^ (2 * j + n) /
        ((j.factorial : ℝ) * ((j + n).factorial : ℝ)) := by
  exact filonIntegerOrderBesselKernel_series n eta r

@[simp] theorem escobarIntegerOrderMode_axis_succ (n : ℕ) (eta : ℝ) :
    escobarIntegerOrderMode (n + 1) eta 0 = 0 := by
  simp [escobarIntegerOrderMode]

/-- At order zero, the arbitrary-order series mode is exactly the integral `J₀` beam mode. -/
theorem escobarIntegerOrderMode_zero_eq_isotropic (eta r : ℝ) :
    escobarIntegerOrderMode 0 eta r = escobarIsotropicRadialMode eta r := by
  exact poincareBesselJ_zero_eq_corpusBesselJ0 (eta * r)

/-! ## Faraday radial modes imported from the anisotropic-beam analysis -/

/-- Radial Bessel residual for azimuthal mode `m` in the cylindrical Faraday separation. -/
def faradayRadialBesselResidual
    (m : ℤ) (beta r value first second : ℝ) : ℝ :=
  second + first / r + (beta ^ 2 - (m : ℝ) ^ 2 / r ^ 2) * value

/-- Radial equation is homogeneous: any constant normalization preserves an exact mode. -/
theorem faradayRadialBesselResidual_const_mul
    (m : ℤ) (beta r value first second scale : ℝ) :
    faradayRadialBesselResidual m beta r
        (scale * value) (scale * first) (scale * second) =
      scale * faradayRadialBesselResidual m beta r value first second := by
  simp only [faradayRadialBesselResidual]
  ring

/-- Axisymmetric Faraday radial modes are exactly the anisotropic paper's `lambda = 0` modes. -/
theorem faradayAxisymmetricJ0_radial_residual_zero
    (eta : EscobarPositiveFrequency) (r : PositiveRadius) :
    faradayRadialBesselResidual 0 eta r
      (escobarIsotropicRadialMode eta r)
      (escobarIsotropicRadialModeDeriv eta r)
      (escobarIsotropicRadialModeSecond eta r) = 0 := by
  have h := escobarIsotropicRadialMode_residual_zero 0 (eta : ℝ) r
  simpa [faradayRadialBesselResidual, escobarRadialResidual, escobarBetaSq,
    escobarZeroAnisotropy] using h

/-- Dipolar Faraday radial modes are the exact order-one modes constructed at `lambda = 2/3`. -/
theorem faradayDipolarJ1_radial_residual_zero
    (eta : EscobarPositiveFrequency) (r : PositiveRadius) :
    faradayRadialBesselResidual 1 eta r
      (escobarOrderOneMode eta r)
      (escobarOrderOneModeDeriv eta r)
      (escobarOrderOneModeSecond eta r) = 0 := by
  simpa [faradayRadialBesselResidual, escobarBesselRadialResidual] using
    escobarOrderOneMode_bessel_residual_zero eta r

/-- Paper's boundary-normalized axisymmetric profile, expressed without a partial denominator. -/
def faradayNormalizedJ0Mode
    (eta xi : EscobarPositiveFrequency) (r : ℝ) : ℝ :=
  (GaloisForLFunctions.RHTower.besselJ0 ((eta : ℝ) / (xi : ℝ)))⁻¹ *
    escobarIsotropicRadialMode eta r

def faradayNormalizedJ0ModeDeriv
    (eta xi : EscobarPositiveFrequency) (r : ℝ) : ℝ :=
  (GaloisForLFunctions.RHTower.besselJ0 ((eta : ℝ) / (xi : ℝ)))⁻¹ *
    escobarIsotropicRadialModeDeriv eta r

def faradayNormalizedJ0ModeSecond
    (eta xi : EscobarPositiveFrequency) (r : ℝ) : ℝ :=
  (GaloisForLFunctions.RHTower.besselJ0 ((eta : ℝ) / (xi : ℝ)))⁻¹ *
    escobarIsotropicRadialModeSecond eta r

/-- Boundary normalization preserves the exact axisymmetric Faraday radial equation. -/
theorem faradayNormalizedJ0Mode_radial_residual_zero
    (eta xi : EscobarPositiveFrequency) (r : PositiveRadius) :
    faradayRadialBesselResidual 0 eta r
      (faradayNormalizedJ0Mode eta xi r)
      (faradayNormalizedJ0ModeDeriv eta xi r)
      (faradayNormalizedJ0ModeSecond eta xi r) = 0 := by
  rw [faradayNormalizedJ0Mode, faradayNormalizedJ0ModeDeriv,
    faradayNormalizedJ0ModeSecond, faradayRadialBesselResidual_const_mul,
    faradayAxisymmetricJ0_radial_residual_zero, mul_zero]

/-- Paper's boundary-normalized dipolar profile. -/
def faradayNormalizedJ1Mode
    (eta xi : EscobarPositiveFrequency) (r : ℝ) : ℝ :=
  (GaloisForLFunctions.RHTower.besselJ1 ((eta : ℝ) / (xi : ℝ)))⁻¹ *
    escobarOrderOneMode eta r

def faradayNormalizedJ1ModeDeriv
    (eta xi : EscobarPositiveFrequency) (r : ℝ) : ℝ :=
  (GaloisForLFunctions.RHTower.besselJ1 ((eta : ℝ) / (xi : ℝ)))⁻¹ *
    escobarOrderOneModeDeriv eta r

def faradayNormalizedJ1ModeSecond
    (eta xi : EscobarPositiveFrequency) (r : ℝ) : ℝ :=
  (GaloisForLFunctions.RHTower.besselJ1 ((eta : ℝ) / (xi : ℝ)))⁻¹ *
    escobarOrderOneModeSecond eta r

/-- Boundary normalization preserves the exact dipolar Faraday radial equation. -/
theorem faradayNormalizedJ1Mode_radial_residual_zero
    (eta xi : EscobarPositiveFrequency) (r : PositiveRadius) :
    faradayRadialBesselResidual 1 eta r
      (faradayNormalizedJ1Mode eta xi r)
      (faradayNormalizedJ1ModeDeriv eta xi r)
      (faradayNormalizedJ1ModeSecond eta xi r) = 0 := by
  rw [faradayNormalizedJ1Mode, faradayNormalizedJ1ModeDeriv,
    faradayNormalizedJ1ModeSecond, faradayRadialBesselResidual_const_mul,
    faradayDipolarJ1_radial_residual_zero, mul_zero]

/-! ## Order-one Liouville normal form for the vortex equation -/

/-- Half-density normal form `sqrt(u) J₁(u)`. -/
def besselJ1NormalForm (u : ℝ) : ℝ :=
  Real.sqrt u * GaloisForLFunctions.RHTower.besselJ1 u

def besselJ1NormalFormDeriv (u : ℝ) : ℝ :=
  GaloisForLFunctions.RHTower.besselJ1 u / (2 * Real.sqrt u) +
    Real.sqrt u * besselJ1Deriv u

def besselJ1NormalFormSecond (u : ℝ) : ℝ :=
  -(GaloisForLFunctions.RHTower.besselJ1 u / (4 * u * Real.sqrt u)) +
    besselJ1Deriv u / Real.sqrt u + Real.sqrt u * besselJ1SecondDeriv u

theorem hasDerivAt_besselJ1NormalForm (u : PositiveRadius) :
    HasDerivAt besselJ1NormalForm (besselJ1NormalFormDeriv u) u := by
  have hu : 0 < (u : ℝ) := u.property
  have hne : (u : ℝ) ≠ 0 := ne_of_gt hu
  have hsq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt u)) u :=
    Real.hasDerivAt_sqrt hne
  have h := hsq.mul (hasDerivAt_besselJ1_certified u)
  have hval :
      1 / (2 * Real.sqrt u) * GaloisForLFunctions.RHTower.besselJ1 u +
          Real.sqrt u * besselJ1Deriv u = besselJ1NormalFormDeriv u := by
    rw [besselJ1NormalFormDeriv]
    ring
  rw [hval] at h
  exact h

theorem hasDerivAt_besselJ1NormalFormDeriv (u : PositiveRadius) :
    HasDerivAt besselJ1NormalFormDeriv (besselJ1NormalFormSecond u) u := by
  have hu : 0 < (u : ℝ) := u.property
  have hne : (u : ℝ) ≠ 0 := ne_of_gt hu
  have hs : 0 < Real.sqrt (u : ℝ) := Real.sqrt_pos.mpr hu
  have hsq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt u)) u :=
    Real.hasDerivAt_sqrt hne
  have hden : HasDerivAt (fun v : ℝ => 2 * Real.sqrt v)
      (2 * (1 / (2 * Real.sqrt u))) u := hsq.const_mul 2
  have hdenne : 2 * Real.sqrt u ≠ 0 := by positivity
  have h1 : HasDerivAt
      (fun v : ℝ => GaloisForLFunctions.RHTower.besselJ1 v / (2 * Real.sqrt v))
      ((besselJ1Deriv u * (2 * Real.sqrt u) -
          GaloisForLFunctions.RHTower.besselJ1 u * (2 * (1 / (2 * Real.sqrt u)))) /
        (2 * Real.sqrt u) ^ 2) u :=
    (hasDerivAt_besselJ1_certified u).div hden hdenne
  have h2 : HasDerivAt
      (fun v : ℝ => Real.sqrt v * besselJ1Deriv v)
      (1 / (2 * Real.sqrt u) * besselJ1Deriv u +
        Real.sqrt u * besselJ1SecondDeriv u) u :=
    hsq.mul (hasDerivAt_besselJ1Deriv u)
  have h := h1.add h2
  have hss : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu.le
  have hval :
      (besselJ1Deriv u * (2 * Real.sqrt u) -
          GaloisForLFunctions.RHTower.besselJ1 u * (2 * (1 / (2 * Real.sqrt u)))) /
          (2 * Real.sqrt u) ^ 2 +
        (1 / (2 * Real.sqrt u) * besselJ1Deriv u +
          Real.sqrt u * besselJ1SecondDeriv u) = besselJ1NormalFormSecond u := by
    rw [besselJ1NormalFormSecond]
    field_simp
    linear_combination (4 * GaloisForLFunctions.RHTower.besselJ1 u) * hss
  rw [hval] at h
  exact h

/-- Order-one Bessel equation in Schrodinger normal form, with centrifugal coefficient `3/4`. -/
theorem besselJ1NormalForm_ode (u : PositiveRadius) :
    besselJ1NormalFormSecond u + (1 - 3 / (4 * u ^ 2)) * besselJ1NormalForm u = 0 := by
  have hu : 0 < (u : ℝ) := u.property
  have hne : (u : ℝ) ≠ 0 := ne_of_gt hu
  have hs : 0 < Real.sqrt (u : ℝ) := Real.sqrt_pos.mpr hu
  have hss : Real.sqrt (u : ℝ) * Real.sqrt (u : ℝ) = (u : ℝ) :=
    Real.mul_self_sqrt hu.le
  have hode := besselJ1_ode u
  have hJ2 : besselJ1SecondDeriv u =
      -(besselJ1Deriv u / u) -
        (1 - 1 / u ^ 2) * GaloisForLFunctions.RHTower.besselJ1 u := by
    linarith [hode]
  rw [besselJ1NormalFormSecond, besselJ1NormalForm, hJ2]
  field_simp
  linear_combination
    (GaloisForLFunctions.RHTower.besselJ1 u - 4 * u * besselJ1Deriv u) * hss

/-- Scaled dipolar vortex mode `sqrt(eta r) J₁(eta r)`. -/
def vortexLinearJ1Mode (eta : VortexPositiveFrequency) (r : ℝ) : ℝ :=
  besselJ1NormalForm ((eta : ℝ) * r)

def vortexLinearJ1ModeDeriv (eta : VortexPositiveFrequency) (r : ℝ) : ℝ :=
  besselJ1NormalFormDeriv ((eta : ℝ) * r) * (eta : ℝ)

def vortexLinearJ1ModeSecond (eta : VortexPositiveFrequency) (r : ℝ) : ℝ :=
  (eta : ℝ) ^ 2 * besselJ1NormalFormSecond ((eta : ℝ) * r)

theorem hasDerivAt_vortexLinearJ1Mode
    (eta : VortexPositiveFrequency) (r : VortexPositiveRadius) :
    HasDerivAt (vortexLinearJ1Mode eta) (vortexLinearJ1ModeDeriv eta r) r := by
  have harg : 0 < (eta : ℝ) * (r : ℝ) := mul_pos eta.property r.property
  have hinner : HasDerivAt (fun x : ℝ => (eta : ℝ) * x) (eta : ℝ) r := by
    simpa using (hasDerivAt_id (r : ℝ)).const_mul (eta : ℝ)
  exact (hasDerivAt_besselJ1NormalForm
    (⟨(eta : ℝ) * (r : ℝ), harg⟩ : PositiveRadius)).comp (r : ℝ) hinner

theorem hasDerivAt_vortexLinearJ1ModeDeriv
    (eta : VortexPositiveFrequency) (r : VortexPositiveRadius) :
    HasDerivAt (vortexLinearJ1ModeDeriv eta) (vortexLinearJ1ModeSecond eta r) r := by
  have harg : 0 < (eta : ℝ) * (r : ℝ) := mul_pos eta.property r.property
  have hinner : HasDerivAt (fun x : ℝ => (eta : ℝ) * x) (eta : ℝ) r := by
    simpa using (hasDerivAt_id (r : ℝ)).const_mul (eta : ℝ)
  have h := (hasDerivAt_besselJ1NormalFormDeriv
    (⟨(eta : ℝ) * (r : ℝ), harg⟩ : PositiveRadius)).comp (r : ℝ) hinner
  have h' := h.mul_const (eta : ℝ)
  have hval :
      besselJ1NormalFormSecond ((eta : ℝ) * (r : ℝ)) * (eta : ℝ) * (eta : ℝ) =
        vortexLinearJ1ModeSecond eta r := by
    rw [vortexLinearJ1ModeSecond]
    ring
  rw [hval] at h'
  exact h'

/-- The dipolar optical-vortex equation now has a certified exact positive-frequency mode. -/
theorem vortexLinearJ1Mode_residual_zero
    (eta : VortexPositiveFrequency) (r : VortexPositiveRadius) :
    vortexLinearStationaryResidual 1 ((eta : ℝ) ^ 2) r
      (vortexLinearJ1Mode eta r) (vortexLinearJ1ModeSecond eta r) = 0 := by
  have harg : 0 < (eta : ℝ) * (r : ℝ) := mul_pos eta.property r.property
  have hode := besselJ1NormalForm_ode
    (⟨(eta : ℝ) * (r : ℝ), harg⟩ : PositiveRadius)
  have heta : (eta : ℝ) ≠ 0 := ne_of_gt eta.property
  have hr : (r : ℝ) ≠ 0 := ne_of_gt r.property
  simp only [vortexLinearStationaryResidual, vortexCentrifugalCoefficient_one,
    vortexLinearJ1Mode, vortexLinearJ1ModeSecond]
  calc
    (eta : ℝ) ^ 2 * besselJ1NormalFormSecond ((eta : ℝ) * (r : ℝ)) +
        ((eta : ℝ) ^ 2 - 3 / 4 / (r : ℝ) ^ 2) *
          besselJ1NormalForm ((eta : ℝ) * (r : ℝ)) =
      (eta : ℝ) ^ 2 *
        (besselJ1NormalFormSecond ((eta : ℝ) * (r : ℝ)) +
          (1 - 3 / (4 * ((eta : ℝ) * (r : ℝ)) ^ 2)) *
            besselJ1NormalForm ((eta : ℝ) * (r : ℝ))) := by
        field_simp [heta, hr]
    _ = 0 := by rw [hode, mul_zero]

/-- Half-density shift identifies the anisotropic order-one square with vortex coefficient `3/4`. -/
theorem escobarOrderOne_sq_eq_vortexDipolar_shift :
    escobarAxisymmetricOrder escobarTwoThirdAnisotropy ^ 2 =
      vortexCentrifugalCoefficient 1 + 1 / 4 := by
  norm_num

/-! ## Fourier/Floquet intersections -/

/-- CGC angular selection certifies diagonal matching of a Faraday azimuthal mode and its dual. -/
theorem cgcFaradayAngularDiagonal (m : ℤ) :
    (∫ theta : ℝ in 0..2 * Real.pi,
      Complex.exp ((((m + -m : ℤ) : ℂ) * Complex.I) * (theta : ℂ))) =
        (2 * Real.pi : ℝ) := by
  simp

/-- Positive period packaged for the corpus finite-window kernel. -/
def faradayPositivePeriod (D : FaradayFloquetData) : Set.Ioi (0 : ℝ) :=
  ⟨D.period, D.period_pos⟩

/-- One-period averaging of a Floquet growth mode is the CGC `exprel` evaluated at log radius. -/
theorem faradayFloquetWindow_eq_cgcExprel (D : FaradayFloquetData) :
    forwardModeAverage (faradayPositivePeriod D)
        ((faradayFloquetGrowthRate D : ℝ) : ℂ) =
      cgcExprel ((Real.log D.multiplierRadius : ℝ) : ℂ) := by
  have harg :
      (((D.period : ℝ) : ℂ) * ((faradayFloquetGrowthRate D : ℝ) : ℂ)) =
        ((Real.log D.multiplierRadius : ℝ) : ℂ) := by
    norm_cast
    rw [faradayFloquetGrowthRate]
    field_simp [ne_of_gt D.period_pos]
  calc
    forwardModeAverage (faradayPositivePeriod D)
        ((faradayFloquetGrowthRate D : ℝ) : ℂ) =
      cgcExprel ((((faradayPositivePeriod D : Set.Ioi (0 : ℝ)) : ℝ) : ℂ) *
        ((faradayFloquetGrowthRate D : ℝ) : ℂ)) :=
          (cgcExprel_eq_forwardModeAverage (faradayPositivePeriod D)
            ((faradayFloquetGrowthRate D : ℝ) : ℂ)).symm
    _ = cgcExprel ((Real.log D.multiplierRadius : ℝ) : ℂ) := by
      rw [faradayPositivePeriod, harg]

/-- Canonical neutral Floquet datum, avoiding a separate neutrality hypothesis. -/
def neutralFaradayFloquetData (period : Set.Ioi (0 : ℝ)) : FaradayFloquetData where
  period := period
  period_pos := period.property
  multiplierRadius := 1
  multiplierRadius_pos := by norm_num

@[simp] theorem neutralFaradayFloquetGrowthRate (period : Set.Ioi (0 : ℝ)) :
    faradayFloquetGrowthRate (neutralFaradayFloquetData period) = 0 := by
  simp [faradayFloquetGrowthRate, neutralFaradayFloquetData]

/-- A neutral Floquet mode has unit normalized period average under the shared `exprel` kernel. -/
theorem neutralFaradayFloquetWindow (period : Set.Ioi (0 : ℝ)) :
    forwardModeAverage (faradayPositivePeriod (neutralFaradayFloquetData period)) 0 = 1 := by
  have h := faradayFloquetWindow_eq_cgcExprel (neutralFaradayFloquetData period)
  rw [neutralFaradayFloquetGrowthRate] at h
  simpa [neutralFaradayFloquetData] using h

end GaloisForLFunctions.HTGeometry
