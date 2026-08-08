import GaloisForLFunctions.RHTower.RouteRBurnolThetaSameFiberOrientation
import GaloisForLFunctions.RHTower.RouteRBurnolXiPrimeTwoCompletionMultiplier
import GaloisForLFunctions.RHTower.ZetaCarrier

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace RHTower

open HedenmalmThetaSource

def burnolFixedAtomCompletedMellin (w : ℂ) : ℂ :=
  soninMellinEvaluation w
    (((coPoissonSubWindowSonin (c := (1 / 2 : ℝ)) (d := 1)
      (by norm_num) (by norm_num) :
        soninExtendedSpace (subWindowAperture (1 / 2) 1)) : evenSubspace) : SoninL2)

theorem burnolFixedAtomCompletedMellin_eq
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    burnolFixedAtomCompletedMellin w =
      Complex.Gammaℝ w * ((2 : ℂ) ^ w - 1) * (riemannZeta w / w) := by
  rw [burnolFixedAtomCompletedMellin,
    soninMellinEvaluation_coPoissonSubWindowSonin
      (c := (1 / 2 : ℝ)) (d := 1) (by norm_num) (by norm_num) hw0 hw1,
    show (((1 : ℝ) : ℂ)) = (1 : ℂ) by norm_num,
    Complex.one_cpow, half_cpow_neg_eq_two_cpow,
    mellinCompletionFactor, Complex.Gammaℝ_def]
  ring

theorem burnolXiCompletionMultiplier_mul_fixedAtomMellin
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    burnolXiCompletionMultiplier w * burnolFixedAtomCompletedMellin w = xi w := by
  have hwne0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw0
    linarith
  have hwne1 : w ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hw1
    linarith
  have hG : Complex.Gammaℝ w ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hw0
  rw [burnolXiCompletionMultiplier, burnolFixedAtomCompletedMellin_eq hw0 hw1,
    xi_eq_archFactor_mul_zeta hwne0 hwne1 hG, archFactor]
  field_simp [two_cpow_sub_one_ne_zero hw0, hwne0]

theorem differentiableAt_burnolFixedAtomCompletedMellin
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    DifferentiableAt ℂ burnolFixedAtomCompletedMellin w := by
  have hwne0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw0
    linarith
  have hwne1 : w ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hw1
    linarith
  have hlocal : burnolFixedAtomCompletedMellin =ᶠ[𝓝 w]
      fun z => Complex.Gammaℝ z * ((2 : ℂ) ^ z - 1) * (riemannZeta z / z) := by
    have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hopen.mem_nhds ⟨hw0, hw1⟩] with z hz
    exact burnolFixedAtomCompletedMellin_eq hz.1 hz.2
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ z) w :=
    differentiableAt_id.const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
  have hformula : DifferentiableAt ℂ
      (fun z => Complex.Gammaℝ z * ((2 : ℂ) ^ z - 1) * (riemannZeta z / z)) w :=
    (((Gammaℝ_analyticAt (Complex.Gammaℝ_ne_zero_of_re_pos hw0)).differentiableAt.mul
      (hpow.sub (differentiableAt_const (c := (1 : ℂ))))).mul
      ((differentiableAt_riemannZeta hwne1).div differentiableAt_id hwne0))
  exact hformula.congr_of_eventuallyEq hlocal

theorem burnolFixedAtomCompletedMellin_eq_zero_of_xi_eq_zero
    {rho : ℂ} (hrho0 : 0 < rho.re) (hrho1 : rho.re < 1)
    (hxi : xi rho = 0) :
    burnolFixedAtomCompletedMellin rho = 0 := by
  have hM := burnolXiCompletionMultiplier_ne_zero hrho0 hrho1
  have hfactor := burnolXiCompletionMultiplier_mul_fixedAtomMellin hrho0 hrho1
  rw [hxi] at hfactor
  exact (mul_eq_zero.mp hfactor).resolve_left hM

theorem burnolXiCompletionMultiplier_mul_dslope_fixedAtomMellin
    {rho s : ℂ}
    (hrho0 : 0 < rho.re) (hrho1 : rho.re < 1)
    (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hxi : xi rho = 0) :
    burnolXiCompletionMultiplier s *
        dslope burnolFixedAtomCompletedMellin rho s =
      dslope xi rho s := by
  have hF : burnolFixedAtomCompletedMellin rho = 0 :=
    burnolFixedAtomCompletedMellin_eq_zero_of_xi_eq_zero hrho0 hrho1 hxi
  rcases eq_or_ne s rho with rfl | hsr
  · rw [dslope_same, dslope_same]
    have hlocal :
        (fun z => burnolXiCompletionMultiplier z * burnolFixedAtomCompletedMellin z)
          =ᶠ[𝓝 s] xi := by
      have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
        (isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt Complex.continuous_re continuous_const)
      filter_upwards [hopen.mem_nhds ⟨hs0, hs1⟩] with z hz
      exact burnolXiCompletionMultiplier_mul_fixedAtomMellin hz.1 hz.2
    rw [← hlocal.deriv_eq,
      deriv_fun_mul (differentiableAt_burnolXiCompletionMultiplier hrho0 hrho1)
        (differentiableAt_burnolFixedAtomCompletedMellin hrho0 hrho1), hF, mul_zero, zero_add]
  · rw [dslope_of_ne _ hsr, dslope_of_ne _ hsr,
      slope_def_field, slope_def_field, hF, hxi, sub_zero, sub_zero,
      ← burnolXiCompletionMultiplier_mul_fixedAtomMellin hs0 hs1]
    field_simp [sub_ne_zero.mpr hsr]

theorem criticalAffine_xiSpectralPointSupport (rho : XiDivisorSupport) :
    (1 / 2 : ℂ) + xiSpectralPointSupport rho * Complex.I = (rho : ℂ) := by
  rw [xiSpectralPointSupport]
  have hI : Complex.I * (-Complex.I) = (1 : ℂ) := by
    rw [mul_neg, Complex.I_mul_I, neg_neg]
  calc
    (1 / 2 : ℂ) + (((rho : ℂ) - 1 / 2) * (-Complex.I)) * Complex.I =
        1 / 2 + ((rho : ℂ) - 1 / 2) * (Complex.I * (-Complex.I)) := by ring
    _ = (rho : ℂ) := by rw [hI]; ring

theorem dslope_XiC_eq_I_mul_dslope_xi_affine
    (a z : ℂ) :
    dslope XiC a z = Complex.I *
      dslope xi ((1 / 2 : ℂ) + a * Complex.I)
        ((1 / 2 : ℂ) + z * Complex.I) := by
  rcases eq_or_ne z a with rfl | hza
  · rw [dslope_same, dslope_same, deriv_XiC_eq_deriv_xi_mul_I]
    ring
  · have hga : (1 / 2 : ℂ) + z * Complex.I ≠
        (1 / 2 : ℂ) + a * Complex.I := by
      intro h
      apply hza
      have hmul : (z - a) * Complex.I = 0 := by linear_combination h
      exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right Complex.I_ne_zero)
    rw [dslope_of_ne _ hza, dslope_of_ne _ hga,
      slope_def_field, slope_def_field]
    rw [show XiC = xi ∘ (fun u : ℂ => (1 / 2 : ℂ) + u * Complex.I) by rfl]
    simp only [Function.comp_apply]
    rw [show (1 / 2 : ℂ) + z * Complex.I - (1 / 2 + a * Complex.I) =
      (z - a) * Complex.I by ring]
    field_simp [hza, hga, Complex.I_ne_zero]

theorem completedXiFirstDividedFunction_eq_completionMultiplier_mul_burnolDslope
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) (x : ℝ) :
    completedXiFirstDividedFunction rho x =
      Complex.I * burnolXiCompletionMultiplier (criticalLineArgument x) *
        dslope burnolFixedAtomCompletedMellin (rho : ℂ) (criticalLineArgument x) := by
  have hrho0 : 0 < (rho : ℂ).re := by linarith
  have hrho1 : (rho : ℂ).re < 1 := xiDivisor_re_lt_one_of_half_lt rho h
  have hs0 : 0 < (criticalLineArgument x).re := by
    rw [criticalLineArgument_re]
    norm_num
  have hs1 : (criticalLineArgument x).re < 1 := by
    rw [criticalLineArgument_re]
    norm_num
  have hxi : xi (rho : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support rho
  have hhand := burnolXiCompletionMultiplier_mul_dslope_fixedAtomMellin
    hrho0 hrho1 hs0 hs1 hxi
  have hcenter := dslope_XiC_eq_I_mul_dslope_xi_affine
    (xiSpectralPointSupport rho) (x : ℂ)
  rw [criticalAffine_xiSpectralPointSupport] at hcenter
  have hcrit : (1 / 2 : ℂ) + (x : ℂ) * Complex.I = criticalLineArgument x := by
    rw [criticalLineArgument]
    ring
  rw [hcrit] at hcenter
  change dslope XiC (xiSpectralPointSupport rho) (x : ℂ) = _
  rw [hcenter, ← hhand]
  ring

/-- Pointwise completed density of the fixed Burnol zero-divided source. -/
def burnolFixedAtomCompletedDividedDensity
    (rho : XiDivisorSupport) (x : ℝ) : ℝ :=
  ‖burnolXiCompletionMultiplier (criticalLineArgument x) *
      dslope burnolFixedAtomCompletedMellin (rho : ℂ)
        (criticalLineArgument x)‖ ^ 2

/-- The coefficient-faithful prime-two completion has exactly the genuine completed-Xi
first-divided energy. -/
theorem integral_burnolFixedAtomCompletedDividedDensity_eq_norm_sq
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    (∫ x : ℝ, burnolFixedAtomCompletedDividedDensity rho x) =
      ‖completedXiFirstDividedL2 rho‖ ^ 2 := by
  rw [GaloisForLFunctions.RHTower.lp_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [completedXiFirstDividedL2_ae rho] with x hx
  rw [hx, completedXiFirstDividedFunction_eq_completionMultiplier_mul_burnolDslope rho h x]
  simp only [burnolFixedAtomCompletedDividedDensity, norm_mul, Complex.norm_I, one_mul]

/-- The completed Burnol divided density is nonzero on every actual Xi fibre. -/
theorem integral_burnolFixedAtomCompletedDividedDensity_pos
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    0 < ∫ x : ℝ, burnolFixedAtomCompletedDividedDensity rho x := by
  rw [integral_burnolFixedAtomCompletedDividedDensity_eq_norm_sq rho h]
  exact sq_pos_of_pos (norm_pos_iff.mpr (completedXiFirstDividedL2_ne_zero rho))

/-- Exact Green boundary law after prime-two completion: compact theta flux is centered
displacement times the coefficient-faithful completed Burnol divided energy. -/
theorem thetaXiRankTwoBoundaryFlux_eq_burnolFixedAtomCompletedDividedDensity
    (q : XiZeroCopy) (h : 1 / 2 < (q.1 : ℂ).re) :
    Real.pi * thetaSource.mass * thetaXiRankTwoBoundaryFlux q =
      (xiSpectralPoint q).im *
        ∫ x : ℝ, burnolFixedAtomCompletedDividedDensity q.1 x := by
  rw [thetaXiRankTwoBoundaryFlux_completedXi_sameFiber,
    integral_burnolFixedAtomCompletedDividedDensity_eq_norm_sq q.1 h]

end RHTower
