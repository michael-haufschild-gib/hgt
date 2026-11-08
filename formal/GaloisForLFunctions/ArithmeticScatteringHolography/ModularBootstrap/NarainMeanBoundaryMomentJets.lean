import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanMomentJets
import GaloisForLFunctions.RHTower.StripSourceHardyTransfer

/-!
# Physical moments at every Mellin boundary frequency

Every imaginary-axis Mellin jet equals an absolutely convergent oscillatory physical moment, with the exact Mellin power and Fourier normalization.
-/

open Complex RHTower MeasureTheory Set
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- All complex jets on the Mellin boundary are absolutely convergent oscillatory clock moments. -/
theorem iteratedDeriv_narainMellinMean_imaginary_eq_clock_moment
    (Y Z : Height) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (narainMellinMean Y Z) ((t : ℂ) * I) =
      ∫ L : ℝ, Complex.exp (-((t : ℂ) * I * (L : ℂ))) *
        ((-L : ℝ) : ℂ) ^ n * narainMeanClockSchwartz Y Z L := by
  have hmoment (m : ℕ) : Integrable (fun L : ℝ => L ^ m • narainMeanClockSchwartz Y Z L) := by
    apply ((narainMeanClockSchwartz Y Z).integrable_pow_mul volume m).mono'
      ((continuous_id.pow m).smul (narainMeanClockSchwartz Y Z).continuous).aestronglyMeasurable
    filter_upwards [] with L
    simp only [norm_smul, norm_pow, le_refl]
  have hd := congrFun (Real.iteratedDeriv_fourier (N := ⊤)
    (fun m _ => hmoment m) (n := n) le_top) (t / (2 * Real.pi))
  rw [fourier_narainMeanClockSchwartz, iteratedDeriv_narainMeanBoundaryFrequency,
    fourier_real_eq_integral_exp] at hd
  have ha : (2 * (Real.pi : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have harg : (2 * (Real.pi : ℂ) * I) * ((t / (2 * Real.pi) : ℝ) : ℂ) = (t : ℂ) * I := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [harg] at hd
  apply mul_left_cancel₀ (pow_ne_zero n ha)
  calc
    _ = ∫ L : ℝ, Complex.exp (-(2 * (Real.pi : ℂ) * I * (L : ℂ) *
          ((t / (2 * Real.pi) : ℝ) : ℂ))) *
          ((-2 * (Real.pi : ℂ) * I * (L : ℂ)) ^ n • narainMeanClockSchwartz Y Z L) := hd
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with L
      have he : -(2 * (Real.pi : ℂ) * I * (L : ℂ) *
          ((t / (2 * Real.pi) : ℝ) : ℂ)) = -((t : ℂ) * I * (L : ℂ)) := by
        push_cast
        field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
        <;> ring
      rw [he, smul_eq_mul, show -2 * (Real.pi : ℂ) * I * (L : ℂ) =
        (2 * (Real.pi : ℂ) * I) * ((-L : ℝ) : ℂ) by push_cast; ring, mul_pow]
      ring

/-- The literal physical moment density at an arbitrary imaginary Mellin frequency. -/
def narainMeanBoundaryMomentDensity (Y Z : Height) (n : ℕ) (t y : ℝ) : ℂ :=
  (y : ℂ) ^ ((t : ℂ) * I) * narainMeanMomentDensity Y Z n y

/-- The logarithmic Jacobian retains the oscillatory frequency factor. -/
theorem exp_smul_narainMeanBoundaryMomentDensity (Y Z : Height) (n : ℕ) (t u : ℝ) :
    Real.exp u • narainMeanBoundaryMomentDensity Y Z n t (Real.exp u) =
      Complex.exp ((t : ℂ) * I * (u : ℂ)) * (u : ℂ) ^ n *
        narainMeanClockSchwartz Y Z (-u) := by
  have hp : (Real.exp u : ℂ) ^ ((t : ℂ) * I) =
      Complex.exp ((t : ℂ) * I * (u : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
      ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
    congr 1
    ring
  rw [narainMeanBoundaryMomentDensity, hp]
  rw [show Real.exp u •
      (Complex.exp ((t : ℂ) * I * (u : ℂ)) * narainMeanMomentDensity Y Z n (Real.exp u)) =
      Complex.exp ((t : ℂ) * I * (u : ℂ)) *
        (Real.exp u • narainMeanMomentDensity Y Z n (Real.exp u)) by
      simp only [Complex.real_smul]; ring]
  rw [exp_smul_narainMeanMomentDensity]
  ring

/-- Every boundary-frequency physical moment converges absolutely. -/
theorem integrableOn_narainMeanBoundaryMomentDensity (Y Z : Height) (n : ℕ) (t : ℝ) :
    IntegrableOn (narainMeanBoundaryMomentDensity Y Z n t) (Ioi (0 : ℝ)) := by
  rw [integrableOn_Ioi_iff_integrable_exp_smul]
  have hbase := ((narainMeanClockSchwartz Y Z).integrable_pow_mul volume n)
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hbase
  simp only [Function.comp_apply, norm_neg] at hneg
  apply hneg.mono'
  · simp_rw [exp_smul_narainMeanBoundaryMomentDensity]
    exact (by fun_prop : Continuous (fun u : ℝ =>
      Complex.exp ((t : ℂ) * I * (u : ℂ)) * (u : ℂ) ^ n *
        narainMeanClockSchwartz Y Z (-u))).aestronglyMeasurable
  · filter_upwards [] with u
    rw [exp_smul_narainMeanBoundaryMomentDensity, norm_mul, norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, zero_sub, mul_one, sub_zero,
      zero_add, add_zero, neg_zero, Real.exp_zero, one_mul, norm_pow, Complex.norm_real, le_refl]

/-- All physical logarithmic moments on the Mellin boundary equal the actual complex jets. -/
theorem integral_narainMeanBoundaryMomentDensity_eq_jet
    (Y Z : Height) (n : ℕ) (t : ℝ) :
    (∫ y in Ioi (0 : ℝ), narainMeanBoundaryMomentDensity Y Z n t y) =
      iteratedDeriv n (narainMellinMean Y Z) ((t : ℂ) * I) := by
  rw [integral_Ioi_eq_integral_exp_smul]
  simp_rw [exp_smul_narainMeanBoundaryMomentDensity]
  rw [iteratedDeriv_narainMellinMean_imaginary_eq_clock_moment]
  have h := integral_neg_eq_self (fun u : ℝ =>
    Complex.exp ((t : ℂ) * I * (u : ℂ)) * (u : ℂ) ^ n * narainMeanClockSchwartz Y Z (-u)) volume
  simpa only [neg_neg, Complex.ofReal_neg, mul_neg] using h.symm

/-- On the positive axis the moment density has the literal combined Mellin power. -/
theorem narainMeanBoundaryMomentDensity_eq (Y Z : Height) (n : ℕ) (t : ℝ) {y : ℝ}
    (hy : 0 < y) :
    narainMeanBoundaryMomentDensity Y Z n t y =
      (y : ℂ) ^ ((-3 / 2 : ℂ) + (t : ℂ) * I) * (Real.log y : ℂ) ^ n *
        ((y : ℂ) * narainScalarHeatAverage Y Z y +
          (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z) := by
  unfold narainMeanBoundaryMomentDensity narainMeanMomentDensity
  have hpower : (y : ℂ) ^ ((t : ℂ) * I) * (y : ℂ) ^ (-3 / 2 : ℂ) =
      (y : ℂ) ^ ((-3 / 2 : ℂ) + (t : ℂ) * I) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne')]
    congr 1
    ring
  calc
    _ = ((y : ℂ) ^ ((t : ℂ) * I) * (y : ℂ) ^ (-3 / 2 : ℂ)) *
        (Real.log y : ℂ) ^ n *
        ((y : ℂ) * narainScalarHeatAverage Y Z y +
          (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z) := by ring
    _ = _ := by rw [hpower]

/-- The literal physical boundary moment is absolutely convergent at every frequency and order. -/
theorem integrableOn_narainScalarHeatAverage_boundary_moment (Y Z : Height) (n : ℕ) (t : ℝ) :
    IntegrableOn (fun y : ℝ =>
      (y : ℂ) ^ ((-3 / 2 : ℂ) + (t : ℂ) * I) * (Real.log y : ℂ) ^ n *
        ((y : ℂ) * narainScalarHeatAverage Y Z y +
          (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z)) (Ioi 0) := by
  exact (integrableOn_narainMeanBoundaryMomentDensity Y Z n t).congr_fun
    (fun y hy => narainMeanBoundaryMomentDensity_eq Y Z n t hy) measurableSet_Ioi

/-- The literal physical Mellin boundary and every logarithmic moment equal the exact complex jets. -/
theorem integral_narainScalarHeatAverage_boundary_moment (Y Z : Height) (n : ℕ) (t : ℝ) :
    (∫ y in Ioi (0 : ℝ),
      (y : ℂ) ^ ((-3 / 2 : ℂ) + (t : ℂ) * I) * (Real.log y : ℂ) ^ n *
        ((y : ℂ) * narainScalarHeatAverage Y Z y +
          (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z)) =
      iteratedDeriv n (narainMellinMean Y Z) ((t : ℂ) * I) := by
  calc
    _ = ∫ y in Ioi (0 : ℝ), narainMeanBoundaryMomentDensity Y Z n t y :=
      setIntegral_congr_fun measurableSet_Ioi
        (fun y hy => (narainMeanBoundaryMomentDensity_eq Y Z n t hy).symm)
    _ = _ := integral_narainMeanBoundaryMomentDensity_eq_jet Y Z n t

#print axioms iteratedDeriv_narainMellinMean_imaginary_eq_clock_moment
#print axioms exp_smul_narainMeanBoundaryMomentDensity
#print axioms integrableOn_narainMeanBoundaryMomentDensity
#print axioms integral_narainMeanBoundaryMomentDensity_eq_jet
#print axioms integrableOn_narainScalarHeatAverage_boundary_moment
#print axioms integral_narainScalarHeatAverage_boundary_moment
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
