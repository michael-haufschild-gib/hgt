import GaloisForLFunctions.SelbergClass.OrdinaryExponentialSeries
import GaloisForLFunctions.RHTower.HeatMultiplierFourier

/-!
# Fourier extraction of Selberg coefficients

Absolute convergence on the line at one permits termwise integration of the
ordinary exponential series over its imaginary period.
-/

noncomputable section
open Complex Filter Topology Set MeasureTheory
open RHTower

namespace GaloisForLFunctions.SelbergClass

/-- Integration over one imaginary period extracts a single Dirichlet coefficient. -/
theorem integral_ordinaryExponentialSeries_mul_exp (F : ExtendedSelbergClass) (n : ℕ) :
    (∫ t in (-Real.pi)..Real.pi,
      ordinaryExponentialSeries F (1 + (t : ℂ) * I) *
        Complex.exp ((n : ℂ) * (1 + (t : ℂ) * I))) =
      2 * (Real.pi : ℂ) * F.coeff n := by
  classical
  let B : ℕ → ℂ := fun m => F.coeff m * Complex.exp ((n : ℂ) - (m : ℂ))
  let T : ℕ → ℝ → ℂ := fun m t =>
    B m * Complex.exp (I * (((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * (t : ℂ))
  have hterm : ∀ (m : ℕ) (t : ℝ), ordinaryExponentialTerm F (1 + (t : ℂ) * I) m *
      Complex.exp ((n : ℂ) * (1 + (t : ℂ) * I)) = T m t := by
    intro m t
    dsimp [ordinaryExponentialTerm, T, B]
    rw [mul_assoc, ← Complex.exp_add, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hnorm : ∀ m t, ‖T m t‖ = Real.exp (n : ℝ) * ‖ordinaryExponentialTerm F 1 m‖ := by
    intro m t
    dsimp only [T]
    rw [norm_mul, norm_exp_I_mul_real, mul_one]
    simp only [B, ordinaryExponentialTerm, norm_mul, Complex.norm_exp,
      Complex.sub_re, Complex.natCast_re, mul_one, Complex.neg_re]
    rw [Real.exp_sub, Real.exp_neg]
    ring
  have hcont : ∀ m, Continuous (T m) := by intro m; dsimp [T]; fun_prop
  have hint : ∀ m, IntegrableOn (T m) (Ioc (-Real.pi) Real.pi) :=
    fun m => (hcont m).integrableOn_Ioc
  have hvol : volume.real (Ioc (-Real.pi) Real.pi) = 2 * Real.pi := by
    rw [MeasureTheory.measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hnormint : ∀ m, (∫ t in Ioc (-Real.pi) Real.pi, ‖T m t‖) =
      (2 * Real.pi * Real.exp (n : ℝ)) * ‖ordinaryExponentialTerm F 1 m‖ := by
    intro m
    simp_rw [hnorm]
    rw [setIntegral_const, smul_eq_mul, hvol]
    ring
  have hsum : Summable (fun m => ∫ t in Ioc (-Real.pi) Real.pi, ‖T m t‖) := by
    simp_rw [hnormint]
    exact (summable_ordinaryExponentialTerm F (by norm_num : 0 < (1 : ℂ).re)).norm.mul_left _
  have hswap := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Ioc (-Real.pi) Real.pi)) hint hsum
  have hpt : ∀ t : ℝ, ordinaryExponentialSeries F (1 + (t : ℂ) * I) *
      Complex.exp ((n : ℂ) * (1 + (t : ℂ) * I)) = ∑' m, T m t := by
    intro t
    rw [ordinaryExponentialSeries, ← tsum_mul_right]
    exact tsum_congr fun m => hterm m t
  have hTint : ∀ m, (∫ t in Ioc (-Real.pi) Real.pi, T m t) =
      B m * (if (n : ℤ) - (m : ℤ) = 0 then (2 * (Real.pi : ℂ)) else 0) := by
    intro m
    dsimp [T]
    rw [integral_const_mul, setIntegral_exp_int_mul]
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  simp_rw [hpt]
  rw [← hswap]
  simp_rw [hTint]
  rw [tsum_eq_single n (fun m hm => by
    rw [if_neg (by omega : (n : ℤ) - (m : ℤ) ≠ 0), mul_zero])]
  simp only [sub_self, if_true, B, Complex.exp_zero, mul_one]
  ring

end GaloisForLFunctions.SelbergClass
