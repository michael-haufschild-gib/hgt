import Mathlib

/-!
# Mellin transform and moments of the standard Gaussian

The Mellin transform of `e^{-π t²}` on the multiplicative half-line is half the real Gamma
factor,

`∫₀^∞ t^{z-1} e^{-π t²} dt = Γ_ℝ(z)/2 = π^{-z/2} Γ(z/2) / 2`   (`Re z > 0`),

obtained from the Gamma integral by the multiplicative substitutions `t ↦ π t` and `t ↦ t²`.
Specializing to real exponents gives the ray moments

`∫₀^∞ t² e^{-π t²} dt = 1/(4π)`,   `∫₀^∞ t⁴ e^{-π t²} dt = 3/(8π²)`.
-/

open Complex Filter Topology MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- The standard Gaussian on the ray, valued in `ℂ`. -/
noncomputable def gaussianKernel (t : ℝ) : ℂ := ((Real.exp (-Real.pi * t ^ 2) : ℝ) : ℂ)

theorem norm_gaussianKernel (t : ℝ) : ‖gaussianKernel t‖ = Real.exp (-Real.pi * t ^ 2) := by
  rw [gaussianKernel, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem norm_gaussianKernel_eq :
    (fun t : ℝ => ‖gaussianKernel t‖) = fun t : ℝ => Real.exp (-Real.pi * t ^ 2) :=
  funext norm_gaussianKernel

theorem continuous_gaussianKernel : Continuous gaussianKernel := by
  unfold gaussianKernel
  fun_prop

/-- The Mellin transform only sees the ray, so two functions agreeing there have the same
transform. -/
theorem mellin_congr_Ioi {f g : ℝ → ℂ} (h : ∀ t ∈ Ioi (0 : ℝ), f t = g t) (s : ℂ) :
    mellin f s = mellin g s := by
  simp only [mellin]
  exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => by rw [h t ht])

/-- Mellin transform of `e^{-x}` is the Gamma function. -/
theorem mellin_exp_neg {z : ℂ} (hz : 0 < z.re) :
    mellin (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) z = Complex.Gamma z := by
  have h := congrFun Complex.GammaIntegral_eq_mellin z
  rw [← h]
  exact (Complex.Gamma_eq_integral hz).symm

/-- Mellin transform of `e^{-π x}`. -/
theorem mellin_exp_neg_pi_mul {z : ℂ} (hz : 0 < z.re) :
    mellin (fun x : ℝ => ((Real.exp (-(Real.pi * x)) : ℝ) : ℂ)) z
      = (Real.pi : ℂ) ^ (-z) * Complex.Gamma z := by
  have h := mellin_comp_mul_left (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) z Real.pi_pos
  rw [mellin_exp_neg hz] at h
  simpa [smul_eq_mul] using h

/-- **Gaussian Mellin transform.** -/
theorem mellin_gaussianKernel {z : ℂ} (hz : 0 < z.re) :
    mellin gaussianKernel z = Complex.Gammaℝ z / 2 := by
  have hz2 : 0 < (z / (2 : ℝ)).re := by
    rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num]
    simpa using by linarith [hz]
  have hrpow := mellin_comp_rpow
    (fun x : ℝ => ((Real.exp (-(Real.pi * x)) : ℝ) : ℂ)) z 2
  have hcongr : mellin gaussianKernel z
      = mellin (fun t : ℝ => ((Real.exp (-(Real.pi * t ^ (2 : ℝ))) : ℝ) : ℂ)) z := by
    refine mellin_congr_Ioi (fun t ht => ?_) z
    have hrp : t ^ (2 : ℝ) = t ^ (2 : ℕ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [gaussianKernel, hrp]
    norm_num
  rw [hcongr, hrpow, mellin_exp_neg_pi_mul hz2, Complex.Gammaℝ_def]
  rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num]
  rw [show |(2 : ℝ)|⁻¹ = (2 : ℝ)⁻¹ by norm_num]
  rw [Complex.real_smul]
  rw [show (-(z / 2)) = (-z / 2) by ring]
  push_cast
  ring

theorem mellinConvergent_gaussianKernel {z : ℂ} (hz : 0 < z.re) :
    MellinConvergent gaussianKernel z := by
  refine mellinConvergent_of_isBigO_rpow_exp (a := 1) (b := 0) one_pos
    (continuous_gaussianKernel.continuousOn.locallyIntegrableOn measurableSet_Ioi) ?_ ?_ (by simpa)
  · rw [← Asymptotics.isBigO_norm_left, norm_gaussianKernel_eq]
    have heq : (fun t : ℝ => Real.exp (-1 * t)) = fun t : ℝ => Real.exp (-t) := by
      funext t
      ring_nf
    rw [heq]
    exact (exp_neg_mul_sq_isLittleO_exp_neg Real.pi_pos).isBigO
  · rw [← Asymptotics.isBigO_norm_left, norm_gaussianKernel_eq]
    refine Asymptotics.isBigO_of_le _ (fun x => ?_)
    have hx : x ^ (-0 : ℝ) = 1 := by simp
    rw [hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_one, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x, Real.pi_pos])

/-- Real-exponent form of the Gaussian ray moment. -/
theorem integral_Ioi_rpow_mul_gaussian {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), t ^ (a - 1) * Real.exp (-Real.pi * t ^ 2))
      = Real.pi ^ (-a / 2) * Real.Gamma (a / 2) / 2 := by
  have hz : 0 < ((a : ℂ)).re := by simpa using ha
  have h := mellin_gaussianKernel hz
  rw [mellin] at h
  have hleft : (∫ t in Ioi (0 : ℝ), (((t ^ (a - 1) * Real.exp (-Real.pi * t ^ 2) : ℝ)) : ℂ))
      = Complex.Gammaℝ (a : ℂ) / 2 := by
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    rw [gaussianKernel, smul_eq_mul, Complex.ofReal_mul]
    congr 1
    rw [Complex.ofReal_cpow ht0]
    push_cast
    ring_nf
  have hcast : (∫ t in Ioi (0 : ℝ), (((t ^ (a - 1) * Real.exp (-Real.pi * t ^ 2) : ℝ)) : ℂ))
      = ((∫ t in Ioi (0 : ℝ), t ^ (a - 1) * Real.exp (-Real.pi * t ^ 2) : ℝ) : ℂ) :=
    integral_ofReal
  rw [hcast] at hleft
  have hright : Complex.Gammaℝ (a : ℂ) / 2
      = ((Real.pi ^ (-a / 2) * Real.Gamma (a / 2) / 2 : ℝ) : ℂ) := by
    rw [Complex.Gammaℝ_def,
      show ((a : ℂ)) / 2 = (((a / 2 : ℝ)) : ℂ) from by push_cast; ring,
      show (-(a : ℂ)) / 2 = (((-a / 2 : ℝ)) : ℂ) from by push_cast; ring,
      Complex.Gamma_ofReal, ← Complex.ofReal_cpow Real.pi_pos.le]
    push_cast
    ring
  rw [hright] at hleft
  exact_mod_cast hleft

theorem Gamma_three_halves : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
  have h := Real.Gamma_nat_add_half 1
  norm_num at h
  exact h

theorem Gamma_five_halves : Real.Gamma (5 / 2) = 3 * Real.sqrt Real.pi / 4 := by
  have h := Real.Gamma_nat_add_half 2
  norm_num at h
  rw [h]

theorem integral_Ioi_sq_gaussian :
    (∫ t in Ioi (0 : ℝ), t ^ 2 * Real.exp (-Real.pi * t ^ 2)) = 1 / (4 * Real.pi) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h := integral_Ioi_rpow_mul_gaussian (a := 3) (by norm_num)
  have hcongr : (∫ t in Ioi (0 : ℝ), t ^ ((3 : ℝ) - 1) * Real.exp (-Real.pi * t ^ 2))
      = ∫ t in Ioi (0 : ℝ), t ^ 2 * Real.exp (-Real.pi * t ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have hrp : t ^ ((3 : ℝ) - 1) = t ^ (2 : ℕ) := by
      rw [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hrp]
  rw [hcongr] at h
  have hcomb : Real.pi ^ (-3 / 2 : ℝ) * Real.pi ^ (1 / 2 : ℝ) = Real.pi⁻¹ := by
    rw [← Real.rpow_add hpi, show (-3 / 2 + 1 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  rw [h, Gamma_three_halves, Real.sqrt_eq_rpow,
    show Real.pi ^ (-3 / 2 : ℝ) * (Real.pi ^ (1 / 2 : ℝ) / 2) / 2
      = (Real.pi ^ (-3 / 2 : ℝ) * Real.pi ^ (1 / 2 : ℝ)) / 4 from by ring, hcomb]
  field_simp

theorem integral_Ioi_pow_four_gaussian :
    (∫ t in Ioi (0 : ℝ), t ^ 4 * Real.exp (-Real.pi * t ^ 2)) = 3 / (8 * Real.pi ^ 2) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h := integral_Ioi_rpow_mul_gaussian (a := 5) (by norm_num)
  have hcongr : (∫ t in Ioi (0 : ℝ), t ^ ((5 : ℝ) - 1) * Real.exp (-Real.pi * t ^ 2))
      = ∫ t in Ioi (0 : ℝ), t ^ 4 * Real.exp (-Real.pi * t ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have hrp : t ^ ((5 : ℝ) - 1) = t ^ (4 : ℕ) := by
      rw [show (5 : ℝ) - 1 = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hrp]
  rw [hcongr] at h
  have hcomb : Real.pi ^ (-5 / 2 : ℝ) * Real.pi ^ (1 / 2 : ℝ) = (Real.pi ^ 2)⁻¹ := by
    have hsum : Real.pi ^ (-5 / 2 : ℝ) * Real.pi ^ (1 / 2 : ℝ) = Real.pi ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hpi]
      norm_num
    rw [hsum, Real.rpow_neg hpi.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast]
  rw [h, Gamma_five_halves, Real.sqrt_eq_rpow,
    show Real.pi ^ (-5 / 2 : ℝ) * (3 * Real.pi ^ (1 / 2 : ℝ) / 4) / 2
      = 3 * (Real.pi ^ (-5 / 2 : ℝ) * Real.pi ^ (1 / 2 : ℝ)) / 8 from by ring, hcomb]
  field_simp

end GaloisForLFunctions.HTGeometry
