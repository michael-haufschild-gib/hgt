import GaloisForLFunctions.RHTower.AsymmetricHeatDoubleSum
import GaloisForLFunctions.HTGeometry.GammaDigammaMixedJetMatroidUniversalityLaw

/-!
# Reflected bi-heat Gamma coefficient

The singular--singular branch product in the reflected bi-heat expansion carries a Gamma pair.
Euler reflection fixes its value at the symmetric regulator to `π`; differentiating the two
opposite half-shifts gives exactly the reflected digamma anomaly.
-/

open Complex

namespace RHTower

/-- Gamma coefficient of the singular--singular reflected branch product.  The affine expression
is the symmetric regulator `epsilon ↦ -epsilon / 2`. -/
noncomputable def reflectedGammaCoefficient (z epsilon : ℂ) : ℂ :=
  Complex.Gamma ((1 - z) + epsilon * (-(1 / 2))) *
    Complex.Gamma (z + epsilon * (-(1 / 2))) *
    Complex.sin (Real.pi * z)

/-- Euler reflection makes the regulator-zero coefficient universal. -/
theorem reflectedGammaCoefficient_zero (P : ReflectedBiHeatRegulator) :
    reflectedGammaCoefficient P.z 0 = Real.pi := by
  rw [reflectedGammaCoefficient]
  norm_num
  have hsin : Complex.sin (Real.pi * P.z) ≠ 0 := by
    intro h
    have href := Complex.Gamma_mul_Gamma_one_sub P.z
    rw [h, div_zero] at href
    have hz0 : Complex.Gamma P.z ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro m hm
      have hre := congrArg Complex.re hm
      norm_num at hre
      linarith [P.z_re_pos]
    have h1z0 : Complex.Gamma (1 - P.z) ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro m hm
      have hre := congrArg Complex.re hm
      norm_num at hre
      linarith [P.z_re_lt_one]
    exact mul_ne_zero hz0 h1z0 href
  have href := Complex.Gamma_mul_Gamma_one_sub P.z
  rw [mul_comm (Complex.Gamma (1 - P.z)) (Complex.Gamma P.z), href]
  field_simp

/-- First regulator derivative of the reflected Gamma coefficient.  It is exactly `-π/2` times
the reflected digamma sum, i.e. the archimedean finite-part anomaly coefficient. -/
theorem deriv_reflectedGammaCoefficient_zero (P : ReflectedBiHeatRegulator) :
    deriv (reflectedGammaCoefficient P.z) 0 =
      -((Real.pi : ℂ) / 2) *
        (Complex.digamma (1 - P.z) + Complex.digamma P.z) := by
  have hzoff : ∀ m : ℕ, P.z ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    linarith [P.z_re_pos]
  have h1zoff : ∀ m : ℕ, 1 - P.z ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    linarith [P.z_re_lt_one]
  have hzderiv : deriv Complex.Gamma P.z =
      Complex.Gamma P.z * Complex.digamma P.z := by
    have h := congrFun GaloisForLFunctions.gamma_iteratedDeriv_one_eq_mul_digamma P.z
    simpa [iteratedDeriv_one] using h
  have h1zderiv : deriv Complex.Gamma (1 - P.z) =
      Complex.Gamma (1 - P.z) * Complex.digamma (1 - P.z) := by
    have h :=
      congrFun GaloisForLFunctions.gamma_iteratedDeriv_one_eq_mul_digamma (1 - P.z)
    simpa [iteratedDeriv_one] using h
  have hzGamma : HasDerivAt Complex.Gamma
      (Complex.Gamma P.z * Complex.digamma P.z) P.z := by
    have h :=
      (GaloisForLFunctions.analyticAt_Gamma P.z hzoff).differentiableAt.hasDerivAt
    rwa [hzderiv] at h
  have h1zGamma : HasDerivAt Complex.Gamma
      (Complex.Gamma (1 - P.z) * Complex.digamma (1 - P.z)) (1 - P.z) := by
    have h :=
      (GaloisForLFunctions.analyticAt_Gamma (1 - P.z) h1zoff).differentiableAt.hasDerivAt
    rwa [h1zderiv] at h
  have hzinner :=
    ((((hasDerivAt_id (0 : ℂ)).mul_const (-(1 / 2 : ℂ))).const_add P.z).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ : ℂ => by rfl)).congr_deriv
        (show (1 : ℂ) * (-(1 / 2)) = -(1 / 2) by ring)
  have h1zinner :=
    ((((hasDerivAt_id (0 : ℂ)).mul_const (-(1 / 2 : ℂ))).const_add
      (1 - P.z)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ : ℂ => by rfl)).congr_deriv
        (show (1 : ℂ) * (-(1 / 2)) = -(1 / 2) by ring)
  have hzcomp : HasDerivAt
      (fun epsilon : ℂ => Complex.Gamma (P.z + epsilon * (-(1 / 2))))
      ((Complex.Gamma P.z * Complex.digamma P.z) * (-(1 / 2))) 0 := by
    have hzGamma0 : HasDerivAt Complex.Gamma
        (Complex.Gamma P.z * Complex.digamma P.z) (P.z + 0 * (-(1 / 2))) := by
      simpa using hzGamma
    exact hzGamma0.comp 0 hzinner
  have h1zcomp : HasDerivAt
      (fun epsilon : ℂ => Complex.Gamma ((1 - P.z) + epsilon * (-(1 / 2))))
      ((Complex.Gamma (1 - P.z) * Complex.digamma (1 - P.z)) * (-(1 / 2))) 0 := by
    have h1zGamma0 : HasDerivAt Complex.Gamma
        (Complex.Gamma (1 - P.z) * Complex.digamma (1 - P.z))
        ((1 - P.z) + 0 * (-(1 / 2))) := by
      simpa using h1zGamma
    exact h1zGamma0.comp 0 h1zinner
  have hraw := (h1zcomp.mul hzcomp).mul_const
    (Complex.sin (Real.pi * P.z))
  have hraw' := hraw.deriv
  change deriv (reflectedGammaCoefficient P.z) 0 = _ at hraw'
  simp only [zero_mul, add_zero] at hraw'
  have hG0 := reflectedGammaCoefficient_zero P
  norm_num [reflectedGammaCoefficient] at hG0
  have hderiv :
      ((Complex.Gamma (1 - P.z) * Complex.digamma (1 - P.z) * (-(1 / 2)) *
          Complex.Gamma P.z + Complex.Gamma (1 - P.z) *
            (Complex.Gamma P.z * Complex.digamma P.z * (-(1 / 2)))) *
        Complex.sin (Real.pi * P.z)) =
      -((Real.pi : ℂ) / 2) *
        (Complex.digamma (1 - P.z) + Complex.digamma P.z) := by
    calc
      _ = -(Complex.Gamma (1 - P.z) * Complex.Gamma P.z *
            Complex.sin (Real.pi * P.z) / 2) *
          (Complex.digamma (1 - P.z) + Complex.digamma P.z) := by ring
      _ = _ := by rw [hG0]
  exact hraw'.trans hderiv

/-- Analytic unit obtained by filling the pole of `Gamma(epsilon / 2)`. -/
noncomputable def gammaHalfPoleUnit (epsilon : ℂ) : ℂ :=
  2 * Complex.Gamma (1 + epsilon / 2)

theorem gammaHalfPoleUnit_zero : gammaHalfPoleUnit 0 = 2 := by
  simp [gammaHalfPoleUnit, Complex.Gamma_one]

/-- Away from the pole, the analytic unit is exactly `epsilon * Gamma(epsilon / 2)`. -/
theorem gammaHalfPoleUnit_eq_mul_Gamma {epsilon : ℂ} (hepsilon : epsilon ≠ 0) :
    gammaHalfPoleUnit epsilon = epsilon * Complex.Gamma (epsilon / 2) := by
  have hhalf : epsilon / 2 ≠ 0 := div_ne_zero hepsilon (by norm_num)
  rw [gammaHalfPoleUnit, show 1 + epsilon / 2 = epsilon / 2 + 1 by ring,
    Complex.Gamma_add_one (epsilon / 2) hhalf]
  ring

/-- The filled half-Gamma pole has first derivative `-EulerGamma`. -/
theorem deriv_gammaHalfPoleUnit_zero :
    deriv gammaHalfPoleUnit 0 = -(Real.eulerMascheroniConstant : ℂ) := by
  have hoff : ∀ m : ℕ, (1 : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hGderiv : deriv Complex.Gamma 1 =
      Complex.Gamma 1 * Complex.digamma 1 := by
    have h := congrFun GaloisForLFunctions.gamma_iteratedDeriv_one_eq_mul_digamma 1
    simpa [iteratedDeriv_one] using h
  have hGamma : HasDerivAt Complex.Gamma
      (Complex.Gamma 1 * Complex.digamma 1) 1 := by
    have h :=
      (GaloisForLFunctions.analyticAt_Gamma 1 hoff).differentiableAt.hasDerivAt
    rwa [hGderiv] at h
  have hinner := ((hasDerivAt_id (0 : ℂ)).div_const 2).const_add 1
  have hGamma0 : HasDerivAt Complex.Gamma
      (Complex.Gamma 1 * Complex.digamma 1) (1 + 0 / 2) := by
    simpa using hGamma
  have hraw := (hGamma0.comp 0 hinner).const_mul 2
  have hderiv := hraw.deriv
  change deriv gammaHalfPoleUnit 0 = _ at hderiv
  simp [Complex.Gamma_one, Complex.digamma_one] at hderiv
  exact hderiv.trans (by ring_nf)

/-- Complex Gaussian moment scale in the regulator variable. -/
noncomputable def reflectedGaussianScale (P : ReflectedBiHeatRegulator) (epsilon : ℂ) : ℂ :=
  Complex.exp (((epsilon - 1) / 2) * (Real.log (4 * Real.pi * P.x) : ℂ))

theorem reflectedGaussianScale_zero (P : ReflectedBiHeatRegulator) :
    reflectedGaussianScale P 0 =
      Complex.exp (-(Real.log (4 * Real.pi * P.x) : ℂ) / 2) := by
  rw [reflectedGaussianScale]
  congr 1
  ring

theorem deriv_reflectedGaussianScale_zero (P : ReflectedBiHeatRegulator) :
    deriv (reflectedGaussianScale P) 0 =
      Complex.exp (-(Real.log (4 * Real.pi * P.x) : ℂ) / 2) *
        ((Real.log (4 * Real.pi * P.x) : ℂ) / 2) := by
  let L : ℂ := Real.log (4 * Real.pi * P.x)
  have hinner := (((hasDerivAt_id (0 : ℂ)).sub_const 1).div_const 2).mul_const L
  have hraw := hinner.cexp
  have hderiv := hraw.deriv
  change deriv (reflectedGaussianScale P) 0 = _ at hderiv
  dsimp [reflectedGaussianScale, L] at hderiv ⊢
  exact hderiv.trans (by ring_nf)

theorem differentiableAt_reflectedGammaCoefficient_zero (P : ReflectedBiHeatRegulator) :
    DifferentiableAt ℂ (reflectedGammaCoefficient P.z) 0 := by
  have hzoff : ∀ m : ℕ, P.z ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    linarith [P.z_re_pos]
  have h1zoff : ∀ m : ℕ, 1 - P.z ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    linarith [P.z_re_lt_one]
  have hz := (GaloisForLFunctions.analyticAt_Gamma P.z hzoff).differentiableAt
  have h1z :=
    (GaloisForLFunctions.analyticAt_Gamma (1 - P.z) h1zoff).differentiableAt
  have hz0 : DifferentiableAt ℂ Complex.Gamma (P.z + 0 * (-(1 / 2))) := by
    simpa using hz
  have h1z0 : DifferentiableAt ℂ Complex.Gamma ((1 - P.z) + 0 * (-(1 / 2))) := by
    simpa using h1z
  change DifferentiableAt ℂ (fun epsilon : ℂ =>
    Complex.Gamma ((1 - P.z) + epsilon * (-(1 / 2))) *
      Complex.Gamma (P.z + epsilon * (-(1 / 2))) * Complex.sin (Real.pi * P.z)) 0
  exact ((h1z0.comp 0 (by fun_prop)).mul (hz0.comp 0 (by fun_prop))).mul_const _

theorem differentiableAt_gammaHalfPoleUnit_zero :
    DifferentiableAt ℂ gammaHalfPoleUnit 0 := by
  have hoff : ∀ m : ℕ, (1 : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hG := (GaloisForLFunctions.analyticAt_Gamma 1 hoff).differentiableAt
  have hG0 : DifferentiableAt ℂ Complex.Gamma (1 + 0 / 2) := by
    simpa using hG
  change DifferentiableAt ℂ (fun epsilon : ℂ => 2 * Complex.Gamma (1 + epsilon / 2)) 0
  exact (hG0.comp 0 (by fun_prop)).const_mul 2

theorem differentiableAt_reflectedGaussianScale_zero (P : ReflectedBiHeatRegulator) :
    DifferentiableAt ℂ (reflectedGaussianScale P) 0 := by
  change DifferentiableAt ℂ (fun epsilon : ℂ =>
    Complex.exp (((epsilon - 1) / 2) * (Real.log (4 * Real.pi * P.x) : ℂ))) 0
  fun_prop

/-- Pole-filled singular--singular Gaussian moment.  Away from zero this is epsilon times the
paper's product of `(5)` and `(6)`. -/
noncomputable def reflectedSingularPoleUnit
    (P : ReflectedBiHeatRegulator) (epsilon : ℂ) : ℂ :=
  reflectedGammaCoefficient P.z epsilon * reflectedGaussianScale P epsilon *
    gammaHalfPoleUnit epsilon * ((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹

theorem reflectedSingularPoleUnit_zero (P : ReflectedBiHeatRegulator) :
    reflectedSingularPoleUnit P 0 =
      (2 * (Real.pi : ℂ)) *
        Complex.exp (-(Real.log (4 * Real.pi * P.x) : ℂ) / 2) *
        ((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹ := by
  rw [reflectedSingularPoleUnit, reflectedGammaCoefficient_zero,
    reflectedGaussianScale_zero, gammaHalfPoleUnit_zero]
  ring

/-- The pole-filled moment has exact residue `x⁻¹ᐟ²`. -/
theorem reflectedSingularPoleUnit_zero_eq_inv_sqrt (P : ReflectedBiHeatRegulator) :
    reflectedSingularPoleUnit P 0 = ((Real.sqrt P.x)⁻¹ : ℂ) := by
  rw [reflectedSingularPoleUnit_zero]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hy : 0 < 4 * Real.pi * P.x :=
    mul_pos (mul_pos (by norm_num) hpi) P.x_pos
  have hsqrtpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 hpi
  have hsqrty : 0 < Real.sqrt (4 * Real.pi * P.x) := Real.sqrt_pos.2 hy
  have hexp : Complex.exp (-(Real.log (4 * Real.pi * P.x) : ℂ) / 2) =
      ((Real.sqrt (4 * Real.pi * P.x))⁻¹ : ℝ) := by
    rw [show -(Real.log (4 * Real.pi * P.x) : ℂ) / 2 =
      ((-Real.log (4 * Real.pi * P.x) / 2 : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_exp]
    congr 1
    rw [show -Real.log (4 * Real.pi * P.x) / 2 =
      -(Real.log (4 * Real.pi * P.x) / 2) by ring, Real.exp_neg]
    congr 1
    rw [show Real.log (4 * Real.pi * P.x) / 2 =
      Real.log (Real.sqrt (4 * Real.pi * P.x)) by
      rw [Real.log_sqrt hy.le]]
    rw [Real.exp_log hsqrty]
  rw [hexp]
  have hsqrt4 : Real.sqrt (4 * Real.pi * P.x) =
      2 * Real.sqrt Real.pi * Real.sqrt P.x := by
    rw [show 4 * Real.pi * P.x = 4 * (Real.pi * P.x) by ring,
      Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)),
      Real.sqrt_mul hpi.le]
    norm_num
    ring
  have hsqrtx : 0 < Real.sqrt P.x := Real.sqrt_pos.2 P.x_pos
  have hreal :
      2 * Real.pi * (Real.sqrt (4 * Real.pi * P.x))⁻¹ *
          (Real.sqrt Real.pi)⁻¹ = (Real.sqrt P.x)⁻¹ := by
    rw [hsqrt4]
    field_simp [hsqrtpi.ne', hsqrtx.ne']
    nlinarith [Real.sq_sqrt hpi.le]
  exact_mod_cast hreal

/-- Exact finite-part coefficient: the derivative of the pole-filled unit is one half of its
residue times the logarithmic/digamma anomaly bracket. -/
theorem deriv_reflectedSingularPoleUnit_zero (P : ReflectedBiHeatRegulator) :
    deriv (reflectedSingularPoleUnit P) 0 =
      reflectedSingularPoleUnit P 0 *
        (((Real.log (4 * Real.pi * P.x) : ℂ) -
          (Real.eulerMascheroniConstant : ℂ) -
          (Complex.digamma (1 - P.z) + Complex.digamma P.z)) / 2) := by
  have hG := differentiableAt_reflectedGammaCoefficient_zero P
  have hS := differentiableAt_reflectedGaussianScale_zero P
  have hU := differentiableAt_gammaHalfPoleUnit_zero
  have hC : DifferentiableAt ℂ
      (fun _ : ℂ => ((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹) 0 :=
    differentiableAt_const _
  change deriv
      ((reflectedGammaCoefficient P.z * reflectedGaussianScale P * gammaHalfPoleUnit) *
        (fun _ : ℂ => ((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹)) 0 =
    (reflectedGammaCoefficient P.z 0 * reflectedGaussianScale P 0 *
        gammaHalfPoleUnit 0 * ((Real.sqrt Real.pi : ℝ) : ℂ)⁻¹) * _
  rw [deriv_mul (hG.mul hS |>.mul hU) hC,
    deriv_const, mul_zero, add_zero,
    deriv_mul (hG.mul hS) hU,
    deriv_mul hG hS,
    deriv_reflectedGammaCoefficient_zero,
    deriv_reflectedGaussianScale_zero,
    deriv_gammaHalfPoleUnit_zero,
    reflectedGammaCoefficient_zero,
    reflectedGaussianScale_zero,
    gammaHalfPoleUnit_zero]
  simp only [Pi.mul_apply]
  rw [reflectedGammaCoefficient_zero, reflectedGaussianScale_zero]
  ring

/-- Paper formula `(7)`: exact finite part of the singular--singular Gaussian moment. -/
theorem deriv_reflectedSingularPoleUnit_zero_eq_anomaly
    (P : ReflectedBiHeatRegulator) :
    deriv (reflectedSingularPoleUnit P) 0 =
      (1 / (2 * Real.sqrt P.x) : ℂ) *
        ((Real.log (4 * Real.pi * P.x) : ℂ) -
          (Real.eulerMascheroniConstant : ℂ) -
          Complex.digamma P.z - Complex.digamma (1 - P.z)) := by
  rw [deriv_reflectedSingularPoleUnit_zero,
    reflectedSingularPoleUnit_zero_eq_inv_sqrt]
  have hsqrtx : (Real.sqrt P.x : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 P.x_pos).ne'
  field_simp
  ring

end RHTower
