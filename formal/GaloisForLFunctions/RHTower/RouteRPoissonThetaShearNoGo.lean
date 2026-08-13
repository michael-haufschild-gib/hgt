import GaloisForLFunctions.RHTower.CCMRationalArchimedeanSchwartzPoisson
import GaloisForLFunctions.RHTower.CCMRationalAdelicMoritaTraceFormula
import GaloisForLFunctions.RHTower.CCMRationalAdelicPrimeIsotropyObserverFreedom
import GaloisForLFunctions.RHTower.CCMRationalAdelicBruhatSchwartzSpace
import GaloisForLFunctions.RHTower.DeningerGaussianEndpointCore
import GaloisForLFunctions.HTGeometry.HermiteFourierEigen

/-!
# Route R: endpoint-corrected Poisson theta shear survives

This file closes the Gaussian/Poisson escape in the prepolar Route R audit on the actual
rational-adelic Bruhat tensor core.  The explicit archimedean Schwartz function

`g₁ - 4 g₂ + 3 g₃`,  where `gᵣ(x) = exp (-π (r x)²)`,

has both Meyer endpoint modes equal to zero.  Nevertheless every nonzero integer lattice value
is positive, hence its lattice theta trace is nonzero.  Tensoring with the characteristic
function of the integral finite adeles gives a nonzero genuine adelic source vector in the
simultaneous endpoint kernel.  Every rational scaling of that vector remains nonzero and remains
in the endpoint kernel.

Thus endpoint cancellation, rational scaling covariance, and Poisson summation do not by
themselves provide the independent singular Cartier annihilation required by Route R.  This is a
literal source counterexample, not an abstract finite-dimensional surrogate.  No Xi zero, RH,
critical-line premise, physical landing, or choice of polar completion occurs.
-/

open Complex Real Set MeasureTheory
open scoped SchwartzMap FourierTransform TensorProduct

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Explicit endpoint-corrected archimedean theta-shear witness. -/
def routeRPoissonThetaShearArchimedean : CCMRationalArchimedeanSchwartz :=
  gaussianSchwartz - (4 : ℂ) •
      ccmRationalArchimedeanDilation gaussianSchwartz 2 (by norm_num) +
    (3 : ℂ) • ccmRationalArchimedeanDilation gaussianSchwartz 3 (by norm_num)

theorem routeRPoissonThetaShearArchimedean_apply (x : ℝ) :
    routeRPoissonThetaShearArchimedean x =
      ((Real.exp (-Real.pi * x ^ 2) -
        4 * Real.exp (-Real.pi * (2 * x) ^ 2) +
        3 * Real.exp (-Real.pi * (3 * x) ^ 2) : ℝ) : ℂ) := by
  simp [routeRPoissonThetaShearArchimedean,
    ccmRationalArchimedeanDilation_apply, gaussianSchwartz_apply, gaussReal]

/-- First Meyer endpoint vanishes exactly. -/
theorem routeRPoissonThetaShearArchimedean_zero :
    routeRPoissonThetaShearArchimedean 0 = 0 := by
  rw [routeRPoissonThetaShearArchimedean_apply]
  norm_num

/-- Fourier/total-mass Meyer endpoint vanishes exactly. -/
theorem fourier_routeRPoissonThetaShearArchimedean_zero :
    FourierTransform.fourier routeRPoissonThetaShearArchimedean 0 = 0 := by
  rw [routeRPoissonThetaShearArchimedean]
  simp only [sub_eq_add_neg, FourierTransform.fourier_add,
    FourierTransform.fourier_neg, FourierTransform.fourier_smul,
    add_apply, neg_apply, smul_apply]
  rw [fourier_gaussianSchwartz]
  rw [fourier_ccmRationalArchimedeanDilation gaussianSchwartz
      (by norm_num : (0 : ℝ) < 2) 0,
    fourier_ccmRationalArchimedeanDilation gaussianSchwartz
      (by norm_num : (0 : ℝ) < 3) 0,
    fourier_gaussianSchwartz]
  simp
  ring

private theorem routeR_exp_neg_pi_lt_half : Real.exp (-Real.pi) < 1 / 2 := by
  have he : Real.pi + 1 < Real.exp Real.pi :=
    Real.add_one_lt_exp Real.pi_ne_zero
  have hfour : (4 : ℝ) < Real.exp Real.pi := by
    linarith [Real.pi_gt_three]
  rw [Real.exp_neg]
  have hpos : 0 < Real.exp Real.pi := Real.exp_pos _
  rw [inv_lt_iff_one_lt_mul₀ hpos]
  nlinarith

/-- Every nonzero integer lattice coefficient of the witness is strictly positive. -/
theorem routeRPoissonThetaShearArchimedean_int_pos_of_ne_zero
    {n : ℤ} (hn : n ≠ 0) :
    0 < (routeRPoissonThetaShearArchimedean (n : ℝ)).re := by
  rw [routeRPoissonThetaShearArchimedean_apply]
  simp only [ofReal_re]
  let y := Real.exp (-Real.pi * (n : ℝ) ^ 2)
  have hypos : 0 < y := Real.exp_pos _
  have habs : (1 : ℝ) ≤ |(n : ℝ)| := by
    exact_mod_cast Int.one_le_abs hn
  have hx2 : 1 ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_abs (n : ℝ)]
  have hyle : y ≤ Real.exp (-Real.pi) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hyhalf : y < 1 / 2 := lt_of_le_of_lt hyle routeR_exp_neg_pi_lt_half
  have h2 : Real.exp (-Real.pi * (2 * (n : ℝ)) ^ 2) = y ^ 4 := by
    rw [show -Real.pi * (2 * (n : ℝ)) ^ 2 =
        4 * (-Real.pi * (n : ℝ) ^ 2) by ring,
      show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.exp_nat_mul]
  have h3 : Real.exp (-Real.pi * (3 * (n : ℝ)) ^ 2) = y ^ 9 := by
    rw [show -Real.pi * (3 * (n : ℝ)) ^ 2 =
        9 * (-Real.pi * (n : ℝ) ^ 2) by ring,
      show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num,
      Real.exp_nat_mul]
  rw [h2, h3]
  have hy3 : y ^ 3 < (1 / 2 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hyhalf hypos.le (by norm_num)
  have hy8 : 0 ≤ 3 * y ^ 8 := by positivity
  have hbracket : 0 < 1 - 4 * y ^ 3 + 3 * y ^ 8 := by
    nlinarith
  nlinarith [mul_pos hypos hbracket]

theorem routeRPoissonThetaShearArchimedean_int_nonneg (n : ℤ) :
    0 ≤ (routeRPoissonThetaShearArchimedean (n : ℝ)).re := by
  by_cases hn : n = 0
  · subst n
    simp [routeRPoissonThetaShearArchimedean_zero]
  · exact (routeRPoissonThetaShearArchimedean_int_pos_of_ne_zero hn).le

/-- The explicit endpoint-corrected theta trace is strictly positive. -/
theorem routeRPoissonThetaShearLatticeTrace_one_re_pos :
    0 < (ccmRationalArchimedeanLatticeTrace
      routeRPoissonThetaShearArchimedean 1).re := by
  have hsumC : Summable (fun n : ℤ =>
      routeRPoissonThetaShearArchimedean (1 * (n : ℝ))) :=
    ccmRationalArchimedeanLatticeTrace_summable
      routeRPoissonThetaShearArchimedean one_ne_zero
  have hsumRe : Summable (fun n : ℤ =>
      (routeRPoissonThetaShearArchimedean (n : ℝ)).re) := by
    simpa using Complex.reCLM.summable hsumC
  rw [ccmRationalArchimedeanLatticeTrace, Complex.re_tsum hsumC]
  simpa using hsumRe.tsum_pos
    routeRPoissonThetaShearArchimedean_int_nonneg 1
    (routeRPoissonThetaShearArchimedean_int_pos_of_ne_zero one_ne_zero)

theorem routeRPoissonThetaShearLatticeTrace_one_ne_zero :
    ccmRationalArchimedeanLatticeTrace
      routeRPoissonThetaShearArchimedean 1 ≠ 0 := by
  intro h
  have hpos := routeRPoissonThetaShearLatticeTrace_one_re_pos
  rw [h] at hpos
  simp at hpos

/-- At the fixed aperture, Poisson summation preserves the nonzero shear exactly. -/
theorem routeRPoissonThetaShearLatticeTrace_poisson_fixed :
    ccmRationalArchimedeanLatticeTrace routeRPoissonThetaShearArchimedean 1 =
      ccmRationalArchimedeanLatticeTrace
        (FourierTransform.fourier routeRPoissonThetaShearArchimedean) 1 := by
  simpa using ccmRationalArchimedeanLatticeTrace_poisson
    routeRPoissonThetaShearArchimedean (by norm_num : (0 : ℝ) < 1)

/-- Actual rational-adelic Bruhat source vector carrying the theta shear. -/
def routeRPoissonThetaShearAdelic : CCMRationalAdelicBruhatSimpleTensor :=
  routeRPoissonThetaShearArchimedean ⊗ₜ[ℂ]
    _root_.RHTower.ccmRationalIntegralFiniteAdelesBruhat

/-- Fixed-point endpoint of the actual adelic witness vanishes. -/
theorem routeRPoissonThetaShearAdelic_zeroEval :
    ccmRationalAdelicBruhatZeroEval routeRPoissonThetaShearAdelic = 0 := by
  simp [routeRPoissonThetaShearAdelic,
    routeRPoissonThetaShearArchimedean_zero]

/-- Haar endpoint of the actual adelic witness vanishes. -/
theorem routeRPoissonThetaShearAdelic_integral :
    ccmRationalAdelicBruhatIntegral routeRPoissonThetaShearAdelic = 0 := by
  have harch : ccmRationalArchimedeanSchwartzIntegral
      routeRPoissonThetaShearArchimedean = 0 := by
    rw [ccmRationalArchimedeanSchwartzIntegral_apply,
      ← _root_.RHTower.deningerFourier_zero]
    exact fourier_routeRPoissonThetaShearArchimedean_zero
  rw [routeRPoissonThetaShearAdelic,
    ccmRationalAdelicBruhatIntegral_tmul, harch]
  simp

/-- The actual simultaneous-endpoint-kernel vector is nonzero. -/
theorem routeRPoissonThetaShearAdelic_ne_zero :
    routeRPoissonThetaShearAdelic ≠ 0 := by
  have harch : routeRPoissonThetaShearArchimedean 1 ≠ 0 := by
    intro h
    have hpos := routeRPoissonThetaShearArchimedean_int_pos_of_ne_zero
      (n := (1 : ℤ)) one_ne_zero
    norm_num at hpos
    rw [h] at hpos
    simp at hpos
  have hzero : (0 : CCMRationalFiniteAdele) ∈ ccmRationalIntegralFiniteAdeles :=
    fun _ => zero_mem _
  intro h
  have heval := congrArg
    (fun t => ccmRationalAdelicBruhatEval t ((1 : ℝ), (0 : CCMRationalFiniteAdele))) h
  rw [routeRPoissonThetaShearAdelic,
    ccmRationalAdelicBruhatEval_tmul,
    _root_.RHTower.ccmRationalIntegralFiniteAdelesBruhat_apply,
    if_pos hzero] at heval
  simp [harch] at heval

/-- Every rationally scaled witness remains in the simultaneous endpoint kernel. -/
theorem routeRPoissonThetaShearAdelic_scaled_endpoints
    (k : CCMRationalAdelicScaling) :
    ccmRationalAdelicBruhatZeroEval (k • routeRPoissonThetaShearAdelic) = 0 ∧
      ccmRationalAdelicBruhatIntegral (k • routeRPoissonThetaShearAdelic) = 0 := by
  rw [ccmRationalAdelicBruhatZeroEval_smul,
    ccmRationalAdelicBruhatIntegral_smul,
    routeRPoissonThetaShearAdelic_zeroEval,
    routeRPoissonThetaShearAdelic_integral]
  exact ⟨rfl, rfl⟩

/-- Rational scaling cannot erase the actual endpoint-corrected witness. -/
theorem routeRPoissonThetaShearAdelic_scaled_ne_zero
    (k : CCMRationalAdelicScaling) :
    k • routeRPoissonThetaShearAdelic ≠ 0 := by
  intro h
  apply routeRPoissonThetaShearAdelic_ne_zero
  calc
    routeRPoissonThetaShearAdelic = k⁻¹ • (k • routeRPoissonThetaShearAdelic) := by simp
    _ = 0 := by rw [h]; simp

/-- Literal no-go package: all prepolar endpoint and Poisson conditions coexist with a nonzero
theta shear on the genuine rational-adelic source. -/
theorem exists_routeRPoissonThetaShearAdelic_noGo :
    ∃ t : CCMRationalAdelicBruhatSimpleTensor,
      t ≠ 0 ∧
      ccmRationalAdelicBruhatZeroEval t = 0 ∧
      ccmRationalAdelicBruhatIntegral t = 0 ∧
      ccmRationalArchimedeanLatticeTrace
        routeRPoissonThetaShearArchimedean 1 ≠ 0 ∧
      ccmRationalArchimedeanLatticeTrace routeRPoissonThetaShearArchimedean 1 =
        ccmRationalArchimedeanLatticeTrace
          (FourierTransform.fourier routeRPoissonThetaShearArchimedean) 1 := by
  exact ⟨routeRPoissonThetaShearAdelic,
    routeRPoissonThetaShearAdelic_ne_zero,
    routeRPoissonThetaShearAdelic_zeroEval,
    routeRPoissonThetaShearAdelic_integral,
    routeRPoissonThetaShearLatticeTrace_one_ne_zero,
    routeRPoissonThetaShearLatticeTrace_poisson_fixed⟩

end GaloisForLFunctions.RHTower
