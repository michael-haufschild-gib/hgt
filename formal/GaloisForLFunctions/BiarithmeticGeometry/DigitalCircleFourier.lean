import GaloisForLFunctions.RHTower.FractionalPartZeta
import GaloisForLFunctions.RHTower.BurnolCoPoissonBerezinFaithful
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

/-!
# Fourier coefficients of digital circle profiles

The fractional-part Mellin identity holds throughout the open critical strip. Logarithmic
substitution and integrable periodization read its zeta quotient on every frequency progression.
-/

noncomputable section
open Complex Real MeasureTheory Set Filter Topology FourierTransform
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The logarithmic seed at an arbitrary strip exponent. -/
def digitalLogSeed (γ y : ℝ) : ℂ :=
  ((Int.fract (Real.exp y) : ℝ) : ℂ) * (Real.exp (-γ * y) : ℂ)

/-- The Mellin abscissa read by the Fourier normalization. -/
def digitalAbscissa (γ ξ : ℝ) : ℂ := (γ : ℂ) + (2 * Real.pi * ξ : ℝ) * Complex.I

theorem digitalAbscissa_re (γ ξ : ℝ) : (digitalAbscissa γ ξ).re = γ := by
  simp only [digitalAbscissa, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero]

private theorem digitalLogSeed_exp_substitution (γ y : ℝ) :
    digitalLogSeed γ y = Real.exp y •
      (((Int.fract (Real.exp y) : ℝ) : ℂ) * (Real.exp y : ℂ) ^ (-((γ : ℂ) + 1))) := by
  have hne : (Real.exp y : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos y).ne'
  have hlog : Complex.log (Real.exp y : ℂ) = (y : ℂ) := by
    rw [← Complex.ofReal_log (Real.exp_pos y).le, Real.log_exp]
  rw [digitalLogSeed, Complex.cpow_def_of_ne_zero hne, hlog, Complex.real_smul]
  rw [Complex.ofReal_exp, Complex.ofReal_exp]
  calc
    _ = ((Int.fract (Real.exp y) : ℝ) : ℂ) *
        Complex.exp ((y : ℂ) + (y : ℂ) * (-((γ : ℂ) + 1))) := by
      congr 2
      push_cast
      ring
    _ = _ := by rw [Complex.exp_add]; ring

/-- The full strip supplies an integrable logarithmic seed. -/
theorem integrable_digitalLogSeed (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    Integrable (digitalLogSeed γ) := by
  have hbase : IntegrableOn
      (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-((γ : ℂ) + 1))) (Ioi 0) :=
    integrableOn_Ioi_zero_fract_cpow hγ0 hγ1
  rw [integrableOn_Ioi_iff_integrable_exp_smul] at hbase
  exact (integrable_congr (Filter.Eventually.of_forall fun y =>
    (digitalLogSeed_exp_substitution γ y).symm)).mp hbase

/-- The seed Fourier transform is the zeta Mellin quotient on its strip line. -/
theorem fourier_digitalLogSeed (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (ξ : ℝ) :
    𝓕 (digitalLogSeed γ) ξ = -(riemannZeta (digitalAbscissa γ ξ) / digitalAbscissa γ ξ) := by
  have hw0 : 0 < (digitalAbscissa γ ξ).re := by rwa [digitalAbscissa_re]
  have hw1 : (digitalAbscissa γ ξ).re < 1 := by rwa [digitalAbscissa_re]
  rw [Real.fourier_eq, ← integral_Ioi_zero_fract_cpow hw0 hw1,
    integral_Ioi_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with y
  have hne : (Real.exp y : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos y).ne'
  have hlog : Complex.log (Real.exp y : ℂ) = (y : ℂ) := by
    rw [← Complex.ofReal_log (Real.exp_pos y).le, Real.log_exp]
  have hcpow : (Real.exp y : ℂ) ^ (-(digitalAbscissa γ ξ + 1)) =
      Complex.exp ((y : ℂ) * (-(digitalAbscissa γ ξ + 1))) := by
    rw [Complex.cpow_def_of_ne_zero hne, hlog]
  have hinner : (inner ℝ y ξ : ℝ) = y * ξ := inner_apply y ξ
  have hkey : Complex.exp ((2 * Real.pi * -(y * ξ) : ℝ) * Complex.I) *
      (Real.exp (-γ * y) : ℂ) =
      (Real.exp y : ℂ) * Complex.exp ((y : ℂ) * (-(digitalAbscissa γ ξ + 1))) := by
    rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [digitalAbscissa]
    push_cast
    ring
  rw [hcpow, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, digitalLogSeed,
    Complex.real_smul, hinner]
  calc
    _ = ((Int.fract (Real.exp y) : ℝ) : ℂ) *
        (Complex.exp ((2 * Real.pi * -(y * ξ) : ℝ) * Complex.I) *
          (Real.exp (-γ * y) : ℂ)) := by ring
    _ = _ := by rw [hkey]; ring

/-- Periodization at circumference `L`, with the ordinary topological-sum convention. -/
def digitalCircleProfile (γ L y : ℝ) : ℂ :=
  l1PeriodizationAtScale (digitalLogSeed γ) L y

/-- The circle reads the complete vertical progression without a nonvanishing premise. -/
theorem fourierCoeff_digitalCircleProfile (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (L : ℝ) (hL : 0 < L) (m : ℤ) :
    fourierCoeffOn hL (digitalCircleProfile γ L) m =
      (1 / L) • (-(riemannZeta (digitalAbscissa γ ((1 / L) * m)) /
        digitalAbscissa γ ((1 / L) * m))) := by
  unfold digitalCircleProfile
  rw [fourierCoeffOn_l1PeriodizationAtScale
    (integrable_digitalLogSeed γ hγ0 hγ1), fourier_digitalLogSeed γ hγ0 hγ1]

end GaloisForLFunctions.BiarithmeticGeometry
