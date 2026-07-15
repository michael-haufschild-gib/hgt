import GaloisForLFunctions.RHTower.SoninSemilocalGammaLogKernel
import GaloisForLFunctions.RHTower.SoninSemilocalAllEvenJacobiResidue
import GaloisForLFunctions.RHTower.CausalFourierBridge
import GaloisForLFunctions.RHTower.L2FourierIntegralBridge
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

noncomputable section

open Complex Filter MeasureTheory Real Set
open scoped BoundedContinuousFunction Convolution ENNReal FourierTransform

namespace RHTower

theorem norm_semilocalGammaLogKernel_le_one
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (x : ℝ) :
    ‖semilocalGammaLogKernel a x‖ ≤ 1 := by
  by_cases hx : 0 ≤ x
  · calc
      ‖semilocalGammaLogKernel a x‖ ≤ Real.exp (-a * x) :=
        norm_semilocalGammaLogKernel_le_of_nonneg hx
      _ ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by nlinarith)
  · have hx' : x ≤ 0 := le_of_not_ge hx
    calc
      ‖semilocalGammaLogKernel a x‖ ≤ Real.exp ((1 - a) * x) :=
        norm_semilocalGammaLogKernel_le_of_nonpos a x
      _ ≤ 1 := by
        calc
          Real.exp ((1 - a) * x) ≤ Real.exp 0 :=
            Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos
              (sub_nonneg.mpr ha1.le) hx')
          _ = 1 := Real.exp_zero

theorem memLp_two_fourier_of_integrable_of_norm_le
    {f : ℝ → ℂ} (hf : Integrable f) {C : ℝ}
    (hbound : ∀ x, ‖f x‖ ≤ C) :
    MemLp (FourierTransform.fourier f) 2 volume := by
  have hfMem : MemLp f 2 volume :=
    memLp_two_of_integrable_of_norm_le hf hbound
  let f2 : Lp ℂ 2 volume := hfMem.toLp f
  have hcoe : (f2 : ℝ → ℂ) =ᵐ[volume] f := by
    simpa [f2] using hfMem.coeFn_toLp
  have hf2int : Integrable (f2 : ℝ → ℂ) := hf.congr hcoe.symm
  have hfourAE :
      ((FourierTransform.fourier f2 : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume]
        FourierTransform.fourier f := by
    calc
      ((FourierTransform.fourier f2 : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume]
          (Real.Lp.fourierTransform
            ((memLp_one_iff_integrable.mpr hf2int).toLp f2) : ℝ → ℂ) :=
        l2_fourier_coeFn_eq_l1_fourier_of_integrable f2 hf2int
      _ =ᵐ[volume] FourierTransform.fourier f := Eventually.of_forall fun x => by
        rw [Real.fourierTransform_toLp]
        exact Real.fourier_congr_ae hcoe x
  exact (memLp_congr_ae hfourAE).mp
    (Lp.memLp (FourierTransform.fourier f2))

def semilocalGammaQuarterKernel : ℝ → ℂ :=
  semilocalGammaLogKernel (1 / 4)

def semilocalGammaQuarterReflection (x : ℝ) : ℂ :=
  semilocalGammaQuarterKernel (-x)

def semilocalGammaAutocorrelation : ℝ → ℂ :=
  semilocalGammaQuarterKernel ⋆[ContinuousLinearMap.mul ℂ ℂ]
    semilocalGammaQuarterReflection

theorem integrable_semilocalGammaQuarterKernel :
    Integrable semilocalGammaQuarterKernel := by
  exact integrable_semilocalGammaLogKernel (by norm_num) (by norm_num)

theorem integrable_semilocalGammaQuarterReflection :
    Integrable semilocalGammaQuarterReflection := by
  simpa [semilocalGammaQuarterReflection] using
    integrable_semilocalGammaQuarterKernel.comp_neg

theorem integrable_semilocalGammaAutocorrelation :
    Integrable semilocalGammaAutocorrelation := by
  exact integrable_semilocalGammaQuarterKernel.integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ)
    integrable_semilocalGammaQuarterReflection

theorem fourier_semilocalGammaQuarterKernel (xi : ℝ) :
    FourierTransform.fourier semilocalGammaQuarterKernel xi =
      Complex.Gamma ((1 : ℝ) / 4 + (2 * Real.pi * xi) * Complex.I) := by
  simpa [semilocalGammaQuarterKernel] using
    (fourier_semilocalGammaLogKernel_frequency
      (a := (1 : ℝ) / 4) (by norm_num) xi)

theorem fourier_semilocalGammaQuarterReflection (xi : ℝ) :
    FourierTransform.fourier semilocalGammaQuarterReflection xi =
      (starRingEnd ℂ)
        (FourierTransform.fourier semilocalGammaQuarterKernel xi) := by
  change FourierTransform.fourier
    (semilocalGammaQuarterKernel ∘ (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ)) xi = _
  rw [Real.fourier_comp_linearIsometry]
  rw [fourier_semilocalGammaQuarterKernel,
    fourier_semilocalGammaQuarterKernel, ← Complex.Gamma_conj]
  congr 2
  apply Complex.ext <;> simp

theorem fourier_semilocalGammaAutocorrelation (xi : ℝ) :
    FourierTransform.fourier semilocalGammaAutocorrelation xi =
      (Complex.normSq
        (Complex.Gamma ((1 : ℝ) / 4 +
          (2 * Real.pi * xi) * Complex.I)) : ℂ) := by
  rw [semilocalGammaAutocorrelation,
    fourier_mul_convolution_eq_of_integrable
      integrable_semilocalGammaQuarterKernel
      integrable_semilocalGammaQuarterReflection,
    fourier_semilocalGammaQuarterReflection,
    fourier_semilocalGammaQuarterKernel, Complex.mul_conj]

theorem integrable_norm_sq_fourier_semilocalGammaQuarterKernel :
    Integrable (fun xi : ℝ =>
      ‖FourierTransform.fourier semilocalGammaQuarterKernel xi‖ ^ 2) := by
  have hmem : MemLp
      (FourierTransform.fourier semilocalGammaQuarterKernel) 2 volume :=
    memLp_two_fourier_of_integrable_of_norm_le
      integrable_semilocalGammaQuarterKernel
      (norm_semilocalGammaLogKernel_le_one (by norm_num) (by norm_num))
  exact (memLp_two_iff_integrable_sq_norm hmem.1).mp hmem

theorem integrable_fourier_semilocalGammaAutocorrelation :
    Integrable (FourierTransform.fourier semilocalGammaAutocorrelation) := by
  have hcomplex := Complex.ofRealCLM.integrable_comp
    integrable_norm_sq_fourier_semilocalGammaQuarterKernel
  apply hcomplex.congr
  filter_upwards with xi
  rw [fourier_semilocalGammaAutocorrelation,
    fourier_semilocalGammaQuarterKernel, Complex.normSq_eq_norm_sq]
  simp only [Complex.ofRealCLM_apply]

def semilocalGammaAutocorrelationShift (x : ℝ) : ℝ :=
  Real.log (1 + Real.exp x)

def semilocalGammaAutocorrelationScale (x : ℝ) : ℝ :=
  Real.exp (x / 4 - semilocalGammaAutocorrelationShift x / 2)

theorem exp_neg_sub_semilocalGammaAutocorrelationShift (x u : ℝ) :
    Real.exp (-(u - semilocalGammaAutocorrelationShift x)) =
      (1 + Real.exp x) * Real.exp (-u) := by
  rw [show -(u - semilocalGammaAutocorrelationShift x) =
      semilocalGammaAutocorrelationShift x + -u by ring,
    Real.exp_add, semilocalGammaAutocorrelationShift,
    Real.exp_log (by positivity)]

theorem semilocalGammaAutocorrelation_integrand_eq (x u : ℝ) :
    semilocalGammaQuarterKernel u *
        semilocalGammaQuarterReflection (x - u) =
      (semilocalGammaAutocorrelationScale x : ℂ) *
        semilocalGammaLogKernel (1 / 2) (u -
          semilocalGammaAutocorrelationShift x) := by
  rw [semilocalGammaQuarterReflection, semilocalGammaQuarterKernel]
  simp only [neg_sub]
  have hshiftC := congrArg Complex.ofReal
    (exp_neg_sub_semilocalGammaAutocorrelationShift x u)
  push_cast at hshiftC
  have hxC : Complex.exp (-((u : ℂ) - (x : ℂ))) =
      Complex.exp x * Complex.exp (-u) := by
    rw [show -((u : ℂ) - (x : ℂ)) = (x : ℂ) + -(u : ℂ) by ring,
      Complex.exp_add]
  have houter :
      Complex.exp (-(1 / 4 : ℂ) * u) *
          Complex.exp (-(1 / 4 : ℂ) * (u - x)) =
        Complex.exp ((x : ℂ) / 4 -
            (semilocalGammaAutocorrelationShift x : ℂ) / 2) *
          Complex.exp (-(1 / 2 : ℂ) *
            (u - semilocalGammaAutocorrelationShift x)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have hinner :
      Complex.exp (-Complex.exp (-u)) *
          Complex.exp (-Complex.exp (-(u - x))) =
        Complex.exp
          (-Complex.exp (-(u - semilocalGammaAutocorrelationShift x))) := by
    rw [← Complex.exp_add]
    congr 1
    rw [hxC, hshiftC]
    ring
  unfold semilocalGammaLogKernel semilocalGammaAutocorrelationScale
  push_cast
  calc
    Complex.exp (-(1 / 4 : ℂ) * u) * Complex.exp (-Complex.exp (-u)) *
          (Complex.exp (-(1 / 4 : ℂ) * (u - x)) *
            Complex.exp (-Complex.exp (-(u - x)))) =
        (Complex.exp (-(1 / 4 : ℂ) * u) *
            Complex.exp (-(1 / 4 : ℂ) * (u - x))) *
          (Complex.exp (-Complex.exp (-u)) *
            Complex.exp (-Complex.exp (-(u - x)))) := by ring
    _ = (Complex.exp ((x : ℂ) / 4 -
            (semilocalGammaAutocorrelationShift x : ℂ) / 2) *
          Complex.exp (-(1 / 2 : ℂ) *
            (u - semilocalGammaAutocorrelationShift x))) *
          Complex.exp
            (-Complex.exp (-(u - semilocalGammaAutocorrelationShift x))) := by
      rw [houter, hinner]
    _ = Complex.exp ((x : ℂ) / 4 -
            (semilocalGammaAutocorrelationShift x : ℂ) / 2) *
          (Complex.exp (-(1 / 2 : ℂ) *
              (u - semilocalGammaAutocorrelationShift x)) *
            Complex.exp
              (-Complex.exp (-(u - semilocalGammaAutocorrelationShift x)))) := by ring

theorem semilocalGammaAutocorrelation_eq_scale_mul_Gamma (x : ℝ) :
    semilocalGammaAutocorrelation x =
      (semilocalGammaAutocorrelationScale x : ℂ) *
        Complex.Gamma ((1 : ℂ) / 2) := by
  rw [semilocalGammaAutocorrelation, MeasureTheory.convolution_def]
  change (∫ u : ℝ, semilocalGammaQuarterKernel u *
      semilocalGammaQuarterReflection (x - u)) = _
  simp_rw [semilocalGammaAutocorrelation_integrand_eq]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_sub_right_eq_self
    (semilocalGammaLogKernel ((1 : ℝ) / 2))
    (semilocalGammaAutocorrelationShift x)]
  rw [integral_semilocalGammaLogKernel (by norm_num)]
  push_cast
  rfl

theorem semilocalGammaAutocorrelation_eq_scale_mul_sqrt_pi (x : ℝ) :
    semilocalGammaAutocorrelation x =
      (semilocalGammaAutocorrelationScale x : ℂ) *
        (Real.sqrt Real.pi : ℂ) := by
  rw [semilocalGammaAutocorrelation_eq_scale_mul_Gamma,
    Complex.Gamma_one_half_eq]
  congr 2
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_nonneg,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one]

theorem one_add_exp_eq_exp_half_mul_two_cosh (x : ℝ) :
    1 + Real.exp x =
      Real.exp (x / 2) * (2 * Real.cosh (x / 2)) := by
  symm
  calc
    Real.exp (x / 2) * (2 * Real.cosh (x / 2)) =
        Real.exp (x / 2) *
          (Real.exp (x / 2) + Real.exp (-(x / 2))) := by
      rw [Real.cosh_eq]
      ring
    _ = Real.exp x + 1 := by
      rw [mul_add, ← Real.exp_add, ← Real.exp_add]
      rw [show x / 2 + x / 2 = x by ring,
        show x / 2 + -(x / 2) = 0 by ring, Real.exp_zero]
    _ = 1 + Real.exp x := add_comm _ _

theorem log_one_add_exp_eq_half_add_log_two_cosh (x : ℝ) :
    Real.log (1 + Real.exp x) =
      x / 2 + Real.log (2 * Real.cosh (x / 2)) := by
  rw [one_add_exp_eq_exp_half_mul_two_cosh,
    Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp]

theorem semilocalGammaAutocorrelationScale_eq_two_cosh_rpow (x : ℝ) :
    semilocalGammaAutocorrelationScale x =
      (2 * Real.cosh (x / 2)) ^ (-(1 : ℝ) / 2) := by
  rw [semilocalGammaAutocorrelationScale,
    semilocalGammaAutocorrelationShift,
    log_one_add_exp_eq_half_add_log_two_cosh,
    Real.rpow_def_of_pos (by positivity : 0 < 2 * Real.cosh (x / 2))]
  congr 1
  ring

theorem semilocalGammaAutocorrelationScale_eq_characteristic (x : ℝ) :
    semilocalGammaAutocorrelationScale x =
      (2 : ℝ) ^ (-(1 : ℝ) / 2) *
        semilocalArchimedeanCharacteristic (x / 2) := by
  rw [semilocalGammaAutocorrelationScale_eq_two_cosh_rpow,
    Real.mul_rpow (by positivity) (Real.cosh_pos _).le]
  rfl

theorem continuous_semilocalGammaAutocorrelationScale :
    Continuous semilocalGammaAutocorrelationScale := by
  unfold semilocalGammaAutocorrelationScale semilocalGammaAutocorrelationShift
  apply Real.continuous_exp.comp
  apply Continuous.sub
  · fun_prop
  · apply Continuous.div_const
    apply Continuous.log
    · fun_prop
    · intro x
      positivity

theorem continuous_semilocalGammaAutocorrelation :
    Continuous semilocalGammaAutocorrelation := by
  rw [show semilocalGammaAutocorrelation = fun x =>
      (semilocalGammaAutocorrelationScale x : ℂ) *
        (Real.sqrt Real.pi : ℂ) by
    funext x
    exact semilocalGammaAutocorrelation_eq_scale_mul_sqrt_pi x]
  exact (Complex.ofRealCLM.continuous.comp
    continuous_semilocalGammaAutocorrelationScale).mul continuous_const

theorem integral_fourier_semilocalGammaAutocorrelation (t : ℝ) :
    (∫ xi : ℝ,
        Complex.exp (((2 * Real.pi * xi * t : ℝ) : ℂ) * Complex.I) *
          (Complex.normSq
            (Complex.Gamma ((1 : ℝ) / 4 +
              (2 * Real.pi * xi) * Complex.I)) : ℂ)) =
      semilocalGammaAutocorrelation t := by
  have hinv := integrable_semilocalGammaAutocorrelation.fourierInv_fourier_eq
    integrable_fourier_semilocalGammaAutocorrelation
    (v := t) continuous_semilocalGammaAutocorrelation.continuousAt
  rw [Real.fourierInv_eq'] at hinv
  rw [show FourierTransform.fourier semilocalGammaAutocorrelation =
      fun xi : ℝ =>
        (Complex.normSq
          (Complex.Gamma ((1 : ℝ) / 4 +
            (2 * Real.pi * xi) * Complex.I)) : ℂ) by
    funext xi
    exact fourier_semilocalGammaAutocorrelation xi] at hinv
  simpa only [smul_eq_mul, Real.inner_apply, Complex.ofReal_mul, mul_assoc] using hinv

def semilocalGammaCharacteristicKernel (t s : ℝ) : ℂ :=
  Complex.exp (((t * s : ℝ) : ℂ) * Complex.I) *
    (Complex.normSq
      (Complex.Gamma ((1 : ℝ) / 4 + (s / 2) * Complex.I)) : ℂ)

theorem integral_semilocalGammaCharacteristicKernel (t : ℝ) :
    (∫ s : ℝ, semilocalGammaCharacteristicKernel t s) =
      (4 * Real.pi : ℂ) * semilocalGammaAutocorrelation (2 * t) := by
  let G : ℝ → ℂ := semilocalGammaCharacteristicKernel t
  have hscale := MeasureTheory.Measure.integral_comp_mul_left G (4 * Real.pi)
  have habs : |(4 * Real.pi : ℝ)⁻¹| = (4 * Real.pi : ℝ)⁻¹ := by
    rw [abs_of_pos]
    positivity
  rw [habs] at hscale
  have hscaled :
      (∫ xi : ℝ, G ((4 * Real.pi) * xi)) =
        semilocalGammaAutocorrelation (2 * t) := by
    rw [show (fun xi : ℝ => G ((4 * Real.pi) * xi)) =
        fun xi : ℝ =>
          Complex.exp (((2 * Real.pi * xi * (2 * t) : ℝ) : ℂ) * Complex.I) *
            (Complex.normSq
              (Complex.Gamma ((1 : ℝ) / 4 +
                (2 * Real.pi * xi) * Complex.I)) : ℂ) by
      funext xi
      unfold G semilocalGammaCharacteristicKernel
      congr 1
      · congr 1
        push_cast
        ring
      · congr 2
        push_cast
        ring]
    exact integral_fourier_semilocalGammaAutocorrelation (2 * t)
  change (∫ s : ℝ, G s) = _
  calc
    (∫ s : ℝ, G s) =
        (4 * Real.pi : ℂ) * (∫ xi : ℝ, G ((4 * Real.pi) * xi)) := by
      rw [hscale, real_smul]
      push_cast
      field_simp [Real.pi_ne_zero]
    _ = (4 * Real.pi : ℂ) *
        semilocalGammaAutocorrelation (2 * t) := by rw [hscaled]

theorem integral_semilocalGammaCharacteristicKernel_closedForm (t : ℝ) :
    (∫ s : ℝ, semilocalGammaCharacteristicKernel t s) =
      ((4 * Real.pi * Real.sqrt Real.pi *
          (2 : ℝ) ^ (-(1 : ℝ) / 2) *
          semilocalArchimedeanCharacteristic t : ℝ) : ℂ) := by
  rw [integral_semilocalGammaCharacteristicKernel,
    semilocalGammaAutocorrelation_eq_scale_mul_sqrt_pi,
    semilocalGammaAutocorrelationScale_eq_characteristic]
  push_cast
  ring

theorem semilocalGammaNormalization_constant :
    (2 * Real.pi) ^ (-(3 : ℝ) / 2) *
        (4 * Real.pi * Real.sqrt Real.pi *
          (2 : ℝ) ^ (-(1 : ℝ) / 2)) = 1 := by
  have hA : 0 < 2 * Real.pi := mul_pos two_pos Real.pi_pos
  rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring,
    Real.rpow_neg hA.le]
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by ring,
    Real.rpow_add hA 1 (1 / 2), Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_eq_rpow]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtTwo : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hsqrtPi : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_nonneg
  field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2),
    Real.sqrt_ne_zero'.mpr Real.pi_pos, Real.pi_ne_zero]
  nlinarith

end RHTower
