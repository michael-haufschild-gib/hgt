import GaloisForLFunctions.RHTower.FZZCigarMarkedRadialReplicaResponse
import GaloisForLFunctions.RHTower.SuzukiLogisticCoupling
import Mathlib.MeasureTheory.Integral.Prod
import GaloisForLFunctions.RHTower.FZZCigarParityDelaySourceContinuation

/-!
# Fermi coupling integration and shared versus independent source factors

The original neutral radial kernel averaged against the positive unit-mass density
`B(u) = exp(u - exp(u))` is the literal Fermi occupancy. Its coupling insertion averages
to a scaled logistic density. Absolute integrability justifies the Fourier Fubini step.

The integrated first marked operator has normalized response
`c * (digamma (1-i*q) - digamma (1+i*q))`, where `q=p/exp(v)` and
`c=(2+exp(v)^2)/exp(v)^2`. It is purely imaginary and vanishes exactly at `p=0`.
Two independently integrated, momentum-reflected factors have zero paired insertion
at every momentum. A pair integrated with one shared coupling instead retains the
strict mixed response of the radial source, with coupling replaced by `Re digamma(1)`.
Its first insertion response and its mixed response both vanish exactly at zero momentum.

All marked quantities are original integrated first-order operator insertions. No
outer coupling differentiation of a finite-deficit family is assumed. The reflected
products are diagnostics, distinct from the physical winding sum. These theorems do
not identify `B` with the nonzero-mode law of the full CFT, identify the full-line
Fourier parameter with the Xi Mellin parameter, or enforce the source Ward identity.
-/

open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry
noncomputable section

def fzzExponentialLogCouplingDensity (u : ℝ) : ℝ := fzzRadialCouplingDensity 0 0 u

def fzzFermiCouplingAverage (v x : ℝ) : ℝ :=
  ∫ u : ℝ, fzzExponentialLogCouplingDensity u * fzzNeutralRadialKernel u v x

def fzzFermiCouplingDensity (v x : ℝ) : ℝ :=
  ∫ u : ℝ, fzzExponentialLogCouplingDensity u * fzzRadialCouplingDensity u v x

theorem fzzExponentialLogCouplingDensity_pos (u : ℝ) :
    0 < fzzExponentialLogCouplingDensity u := fzzRadialCouplingDensity_pos 0 0 u

theorem integrable_fzzExponentialLogCouplingDensity : Integrable fzzExponentialLogCouplingDensity :=
  integrable_fzzRadialCouplingDensity 0 0

theorem fzzExponentialLogCouplingDensity_mass :
    (∫ u : ℝ, fzzExponentialLogCouplingDensity u) = 1 := fzzRadialCouplingDensity_mass 0 0

private theorem log_density_eq (u : ℝ) :
    fzzExponentialLogCouplingDensity u = Real.exp u * Real.exp (-Real.exp u) := by
  simp only [fzzExponentialLogCouplingDensity, fzzRadialCouplingDensity,
    fzzNeutralRadialCoordinate, fzzNeutralRadialKernel, Real.exp_zero, zero_add, one_mul]

private theorem coupling_average_integrand (v x u : ℝ) :
    fzzExponentialLogCouplingDensity u * fzzNeutralRadialKernel u v x =
      (1 + Real.exp (Real.exp v * x))⁻¹ *
        fzzExponentialLogCouplingDensity (Real.log (1 + Real.exp (Real.exp v * x)) + u) := by
  let C := 1 + Real.exp (Real.exp v * x)
  have hC : 0 < C := by dsimp [C]; positivity
  have he : Real.exp (Real.log C + u) = C * Real.exp u := by
    rw [Real.exp_add, Real.exp_log hC]
  change fzzExponentialLogCouplingDensity u * Real.exp (-Real.exp (u + Real.exp v * x)) =
    C⁻¹ * fzzExponentialLogCouplingDensity (Real.log C + u)
  rw [log_density_eq, log_density_eq, he, Real.exp_add u]
  have hx : -Real.exp u + -(Real.exp u * Real.exp (Real.exp v * x)) = -(C * Real.exp u) := by
    dsimp [C]
    ring
  rw [mul_assoc, ← Real.exp_add, hx]
  field_simp

theorem fzzFermiCouplingAverage_eq (v x : ℝ) :
    fzzFermiCouplingAverage v x = (1 + Real.exp (Real.exp v * x))⁻¹ := by
  simp only [fzzFermiCouplingAverage, coupling_average_integrand, integral_const_mul,
    integral_add_left_eq_self, fzzExponentialLogCouplingDensity_mass, mul_one]

theorem integrable_fzzFermiCouplingAverage_integrand (v x : ℝ) :
    Integrable (fun u : ℝ => fzzExponentialLogCouplingDensity u * fzzNeutralRadialKernel u v x) := by
  simp only [coupling_average_integrand]
  exact (integrable_fzzExponentialLogCouplingDensity.comp_add_left _).const_mul _

private def gammaTwoLogDensity (u : ℝ) : ℝ := Real.exp (2*u - Real.exp u)

private theorem gamma_two_log_mass : (∫ u : ℝ, gammaTwoLogDensity u) = 1 := by
  have h := GaloisForLFunctions.Gamma_vertical_eq_fourier (σ := 2) (by norm_num) 0
  have hg : Complex.Gamma (2 : ℂ) = 1 := by
    have hh := Complex.Gamma_add_one 1 one_ne_zero
    simpa only [one_add_one_eq_two, Complex.Gamma_one, one_mul] using hh
  simp only [Complex.ofReal_ofNat, Complex.ofReal_zero, zero_mul, add_zero,
    Complex.exp_zero, one_mul, hg] at h
  change (1 : ℂ) = ∫ u : ℝ, (gammaTwoLogDensity u : ℂ) at h
  exact_mod_cast h.symm

private theorem coupling_density_integrand (v x u : ℝ) :
    fzzExponentialLogCouplingDensity u * fzzRadialCouplingDensity u v x =
      (Real.exp v * Real.exp (Real.exp v * x) / (1 + Real.exp (Real.exp v * x))^2) *
        gammaTwoLogDensity (Real.log (1 + Real.exp (Real.exp v * x)) + u) := by
  let C := 1 + Real.exp (Real.exp v * x)
  have hC : 0 < C := by dsimp [C]; positivity
  have he : Real.exp (Real.log C + u) = C * Real.exp u := by
    rw [Real.exp_add, Real.exp_log hC]
  have h2 : Real.exp (2 * (Real.log C + u)) = C^2 * Real.exp u ^ 2 := by
    rw [show 2*(Real.log C+u) = (Real.log C+u)+(Real.log C+u) by ring,
      Real.exp_add, he]
    ring
  change fzzExponentialLogCouplingDensity u *
      (Real.exp v * Real.exp (u + Real.exp v * x) * Real.exp (-Real.exp (u + Real.exp v * x))) =
    (Real.exp v * Real.exp (Real.exp v * x) / C^2) * gammaTwoLogDensity (Real.log C + u)
  rw [log_density_eq, gammaTwoLogDensity, Real.exp_sub, h2, he, Real.exp_add u]
  have hx : Real.exp (-Real.exp u) * Real.exp (-(Real.exp u * Real.exp (Real.exp v * x))) =
      (Real.exp (C*Real.exp u))⁻¹ := by
    rw [← Real.exp_add, ← Real.exp_neg]
    congr 1
    dsimp [C]
    ring
  calc
    _ = (Real.exp v * Real.exp (Real.exp v*x) * Real.exp u^2) *
        (Real.exp (-Real.exp u) * Real.exp (-(Real.exp u * Real.exp (Real.exp v*x)))) := by ring
    _ = _ := by rw [hx]; field_simp

theorem fzzFermiCouplingDensity_eq (v x : ℝ) :
    fzzFermiCouplingDensity v x = Real.exp v * _root_.RHTower.logisticKernel (Real.exp v * x) := by
  simp only [fzzFermiCouplingDensity, coupling_density_integrand, integral_const_mul,
    integral_add_left_eq_self, gamma_two_log_mass, mul_one, _root_.RHTower.logisticKernel]
  ring

theorem fzzFermiCouplingAverage_eq_parityDelay (v w : ℝ) :
    fzzFermiCouplingAverage v (Real.exp w / Real.exp v) =
      _root_.RHTower.fzzCigarParityDelay (Real.exp w) := by
  rw [fzzFermiCouplingAverage_eq, mul_div_cancel₀ _ (Real.exp_ne_zero v),
    _root_.RHTower.fzzCigarParityDelay_eq_fermi (Real.exp_pos w), add_comm]

theorem hasDerivAt_fzzFermiCouplingAverage (v x : ℝ) :
    HasDerivAt (fzzFermiCouplingAverage v) (-fzzFermiCouplingDensity v x) x := by
  have hd := ((((hasDerivAt_id x).const_mul (Real.exp v)).exp).const_add 1).inv
    (by positivity : 1 + Real.exp (Real.exp v * x) ≠ 0)
  have he : fzzFermiCouplingAverage v = fun x : ℝ => (1 + Real.exp (Real.exp v * x))⁻¹ := by
    funext x
    exact fzzFermiCouplingAverage_eq v x
  rw [he, fzzFermiCouplingDensity_eq, _root_.RHTower.logisticKernel]
  simpa only [id_eq, Pi.inv_apply, mul_one, one_mul, neg_div, mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using! hd

def fzzFermiCouplingJointDensity (v : ℝ) (z : ℝ × ℝ) : ℝ :=
  fzzExponentialLogCouplingDensity z.1 * fzzRadialCouplingDensity z.1 v z.2

private theorem joint_density_pos (v : ℝ) (z : ℝ × ℝ) : 0 < fzzFermiCouplingJointDensity v z :=
  mul_pos (fzzExponentialLogCouplingDensity_pos z.1) (fzzRadialCouplingDensity_pos z.1 v z.2)

private theorem joint_density_continuous (v : ℝ) : Continuous (fzzFermiCouplingJointDensity v) := by
  unfold fzzFermiCouplingJointDensity fzzExponentialLogCouplingDensity fzzRadialCouplingDensity
    fzzNeutralRadialKernel fzzNeutralRadialCoordinate
  fun_prop

theorem integrable_fzzFermiCouplingJointDensity (v : ℝ) :
    Integrable (fzzFermiCouplingJointDensity v) (volume.prod volume) := by
  apply (integrable_prod_iff (joint_density_continuous v).aestronglyMeasurable).mpr
  constructor
  · filter_upwards with u
    exact (integrable_fzzRadialCouplingDensity u v).const_mul (fzzExponentialLogCouplingDensity u)
  · have he : (fun u : ℝ => ∫ x : ℝ, ‖fzzFermiCouplingJointDensity v (u,x)‖) =
        fzzExponentialLogCouplingDensity := by
      funext u
      have hn : (fun x : ℝ => ‖fzzFermiCouplingJointDensity v (u,x)‖) =
          fun x : ℝ => fzzFermiCouplingJointDensity v (u,x) := by
        funext x
        rw [Real.norm_eq_abs, abs_of_pos (joint_density_pos v (u,x))]
      rw [hn]
      simp only [fzzFermiCouplingJointDensity, integral_const_mul, fzzRadialCouplingDensity_mass, mul_one]
    rw [he]
    exact integrable_fzzExponentialLogCouplingDensity

private theorem joint_character_integrable (v p : ℝ) :
    Integrable (fun z : ℝ × ℝ => (fzzFermiCouplingJointDensity v z : ℂ) *
      Complex.exp (((p*z.2 : ℝ) : ℂ)*Complex.I)) (volume.prod volume) := by
  apply (integrable_fzzFermiCouplingJointDensity v).mono'
  · have hc : Continuous (fun z : ℝ × ℝ => (fzzFermiCouplingJointDensity v z : ℂ) *
        Complex.exp (((p*z.2 : ℝ) : ℂ)*Complex.I)) := by
      exact (Complex.continuous_ofReal.comp (joint_density_continuous v)).mul (by fun_prop)
    exact hc.aestronglyMeasurable
  · filter_upwards with z
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (joint_density_pos v z), Complex.norm_exp_ofReal_mul_I, mul_one, le_refl]

def fzzFermiCouplingCharacteristic (v p : ℝ) : ℂ :=
  ∫ u : ℝ, (fzzExponentialLogCouplingDensity u : ℂ) * fzzRadialCouplingCharacteristic u v p

private theorem coupling_character (q : ℝ) :
    (∫ u : ℝ, (fzzExponentialLogCouplingDensity u : ℂ) *
      Complex.exp (((q*u : ℝ) : ℂ)*Complex.I)) = Complex.Gamma (1 + (q : ℂ)*Complex.I) := by
  change fzzRadialCouplingCharacteristic 0 0 q = _
  rw [fzzRadialCouplingCharacteristic_eq_gamma]
  simp

theorem fzzFermiCouplingCharacteristic_eq (v p : ℝ) :
    fzzFermiCouplingCharacteristic v p =
      Complex.Gamma (1 + ((p/Real.exp v : ℝ) : ℂ)*Complex.I) *
        Complex.Gamma (1 + ((-p/Real.exp v : ℝ) : ℂ)*Complex.I) := by
  unfold fzzFermiCouplingCharacteristic
  simp only [fzzRadialCouplingCharacteristic_eq_gamma, ← mul_assoc]
  rw [integral_mul_const]
  have he : (fun u : ℝ => (fzzExponentialLogCouplingDensity u : ℂ) *
      Complex.exp (-(((p*u/Real.exp v : ℝ) : ℂ)*Complex.I))) =
      fun u : ℝ => (fzzExponentialLogCouplingDensity u : ℂ) *
        Complex.exp ((((-p/Real.exp v)*u : ℝ) : ℂ)*Complex.I) := by
    funext u
    congr 2
    push_cast
    ring
  rw [he, coupling_character, mul_comm]

theorem fzzFermiCouplingCharacteristic_eq_density_fourier (v p : ℝ) :
    fzzFermiCouplingCharacteristic v p = ∫ x : ℝ, (fzzFermiCouplingDensity v x : ℂ) *
      Complex.exp (((p*x : ℝ) : ℂ)*Complex.I) := by
  have h := integral_integral_swap (f := fun u x : ℝ =>
    (fzzFermiCouplingJointDensity v (u,x) : ℂ) * Complex.exp (((p*x : ℝ) : ℂ)*Complex.I))
      (joint_character_integrable v p)
  change (∫ u : ℝ, ∫ x : ℝ, (fzzFermiCouplingJointDensity v (u,x) : ℂ) *
      Complex.exp (((p*x : ℝ) : ℂ)*Complex.I)) =
    ∫ x : ℝ, ∫ u : ℝ, (fzzFermiCouplingJointDensity v (u,x) : ℂ) *
      Complex.exp (((p*x : ℝ) : ℂ)*Complex.I) at h
  have hl : (∫ u : ℝ, ∫ x : ℝ, (fzzFermiCouplingJointDensity v (u,x) : ℂ) *
      Complex.exp (((p*x : ℝ) : ℂ)*Complex.I)) = fzzFermiCouplingCharacteristic v p := by
    simp only [fzzFermiCouplingJointDensity, Complex.ofReal_mul, mul_assoc,
      integral_const_mul, fzzFermiCouplingCharacteristic, fzzRadialCouplingCharacteristic]
  have hr : (∫ x : ℝ, ∫ u : ℝ, (fzzFermiCouplingJointDensity v (u,x) : ℂ) *
      Complex.exp (((p*x : ℝ) : ℂ)*Complex.I)) =
    ∫ x : ℝ, (fzzFermiCouplingDensity v x : ℂ) * Complex.exp (((p*x : ℝ) : ℂ)*Complex.I) := by
    simp only [integral_mul_const, fzzFermiCouplingJointDensity, integral_complex_ofReal,
      fzzFermiCouplingDensity]
  rw [hl, hr] at h
  exact h

theorem fzzFermiCouplingCharacteristic_ne_zero (v p : ℝ) :
    fzzFermiCouplingCharacteristic v p ≠ 0 := by
  rw [fzzFermiCouplingCharacteristic_eq]
  apply mul_ne_zero <;> apply Complex.Gamma_ne_zero_of_re_pos <;>
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero] <;> exact zero_lt_one

private def couplingMomentIntegrand (q u : ℝ) : ℂ :=
  (u : ℂ) * (fzzExponentialLogCouplingDensity u : ℂ) *
    Complex.exp (((q*u : ℝ) : ℂ)*Complex.I)

private theorem unit_marked_zero (q u : ℝ) :
    fzzMarkedRadialReplicaIntegrand 0 0 q 0 u =
      (fzzExponentialLogCouplingDensity u : ℂ) * Complex.exp (((q*u : ℝ) : ℂ)*Complex.I) := by
  rw [log_density_eq]
  simp only [fzzMarkedRadialReplicaIntegrand, mul_zero, sub_zero, one_mul,
    Real.exp_zero, zero_add, Real.exp_sub, Real.exp_neg, Complex.ofReal_mul,
    div_eq_mul_inv, Complex.ofReal_inv, Complex.ofReal_one]

private theorem unit_marked_jet (q u : ℝ) :
    deriv (fun δ => fzzMarkedRadialReplicaIntegrand 0 0 q δ u) 0 =
      (-3 : ℂ) * couplingMomentIntegrand q u := by
  rw [(hasDerivAt_fzzMarkedRadialReplicaIntegrand 0 0 q u).deriv, unit_marked_zero]
  norm_num [fzzMarkedRadialReplicaRate, couplingMomentIntegrand]
  ring

private theorem coupling_moment_integrable (q : ℝ) : Integrable (couplingMomentIntegrand q) := by
  have hi := (integrable_fzzMarkedRadialReplicaInsertion 0 0 q).const_mul (-(1/3 : ℂ))
  apply hi.congr
  filter_upwards with u
  rw [unit_marked_jet]
  ring

private theorem coupling_moment_integral (q : ℝ) :
    (∫ u : ℝ, couplingMomentIntegrand q u) =
      Complex.Gamma (1+(q : ℂ)*Complex.I) * Complex.digamma (1+(q : ℂ)*Complex.I) := by
  have h := fzzMarkedRadialReplicaIntegral_deriv_eq_integral 0 0 q
  simp only [unit_marked_jet, integral_const_mul] at h
  apply mul_left_cancel₀ (show (-3 : ℂ) ≠ 0 by norm_num)
  rw [← h, (hasDerivAt_fzzMarkedRadialReplicaIntegral 0 0 q).deriv,
    fzzMarkedRadialReplicaIntegral_zero, fzzRadialCouplingCharacteristic_eq_gamma]
  norm_num [fzzMarkedRadialReplicaRate]
  ring

private theorem coupling_character_integrable (q : ℝ) :
    Integrable (fun u : ℝ => (fzzExponentialLogCouplingDensity u : ℂ) *
      Complex.exp (((q*u : ℝ) : ℂ)*Complex.I)) :=
  integrable_fzzRadialCouplingCharacteristic_integrand 0 0 q

def fzzFermiCouplingMarkedIntegral (v p : ℝ) : ℂ :=
  ∫ u : ℝ, (fzzExponentialLogCouplingDensity u : ℂ) *
    deriv (fzzMarkedRadialReplicaIntegral u v p) 0

private theorem coupled_marked_integrand (v p u : ℝ) :
    (fzzExponentialLogCouplingDensity u : ℂ) *
      deriv (fzzMarkedRadialReplicaIntegral u v p) 0 =
    ((fzzMarkedRadialReplicaRate v : ℂ) * Complex.Gamma (1+((p/Real.exp v : ℝ) : ℂ)*Complex.I)) *
      (couplingMomentIntegrand (-p/Real.exp v) u -
        Complex.digamma (1+((p/Real.exp v : ℝ) : ℂ)*Complex.I) *
          ((fzzExponentialLogCouplingDensity u : ℂ) *
            Complex.exp ((((-p/Real.exp v)*u : ℝ) : ℂ)*Complex.I))) := by
  rw [(hasDerivAt_fzzMarkedRadialReplicaIntegral u v p).deriv,
    fzzMarkedRadialReplicaIntegral_zero, fzzRadialCouplingCharacteristic_eq_gamma]
  have he : -(((p*u/Real.exp v : ℝ) : ℂ)*Complex.I) =
      ((((-p/Real.exp v)*u : ℝ) : ℂ)*Complex.I) := by
    push_cast
    ring
  rw [he]
  unfold couplingMomentIntegrand
  ring

theorem integrable_fzzFermiCouplingMarked_integrand (v p : ℝ) :
    Integrable (fun u : ℝ => (fzzExponentialLogCouplingDensity u : ℂ) *
      deriv (fzzMarkedRadialReplicaIntegral u v p) 0) := by
  simp only [coupled_marked_integrand]
  exact ((coupling_moment_integrable _).sub
    ((coupling_character_integrable _).const_mul _)).const_mul _

/-- The marked response is integrated before normalization. This identity keeps the specified
order of integration and uses the already proved radial insertion interchange. -/
theorem fzzFermiCouplingMarkedIntegral_eq_iterated_insertion (v p : ℝ) :
    fzzFermiCouplingMarkedIntegral v p = ∫ u : ℝ, ∫ x : ℝ,
      (fzzExponentialLogCouplingDensity u : ℂ) *
        deriv (fun δ => fzzMarkedRadialReplicaIntegrand u v p δ x) 0 := by
  unfold fzzFermiCouplingMarkedIntegral
  apply integral_congr_ae
  filter_upwards with u
  rw [fzzMarkedRadialReplicaIntegral_deriv_eq_integral, integral_const_mul]

theorem fzzFermiCouplingMarkedIntegral_eq (v p : ℝ) :
    fzzFermiCouplingMarkedIntegral v p =
      (fzzMarkedRadialReplicaRate v : ℂ) *
        (Complex.digamma (1+((-p/Real.exp v : ℝ) : ℂ)*Complex.I) -
          Complex.digamma (1+((p/Real.exp v : ℝ) : ℂ)*Complex.I)) *
        fzzFermiCouplingCharacteristic v p := by
  simp only [fzzFermiCouplingMarkedIntegral, coupled_marked_integrand, integral_const_mul]
  rw [integral_sub (coupling_moment_integrable _)
      ((coupling_character_integrable _).const_mul _), integral_const_mul,
    coupling_moment_integral, coupling_character, fzzFermiCouplingCharacteristic_eq]
  ring

def fzzFermiCouplingMarkedResponse (v p : ℝ) : ℂ :=
  fzzFermiCouplingMarkedIntegral v p / fzzFermiCouplingCharacteristic v p

theorem fzzFermiCouplingMarkedResponse_eq (v p : ℝ) :
    fzzFermiCouplingMarkedResponse v p = (fzzMarkedRadialReplicaRate v : ℂ) *
      (Complex.digamma (1+((-p/Real.exp v : ℝ) : ℂ)*Complex.I) -
        Complex.digamma (1+((p/Real.exp v : ℝ) : ℂ)*Complex.I)) := by
  rw [fzzFermiCouplingMarkedResponse, fzzFermiCouplingMarkedIntegral_eq,
    mul_div_cancel_right₀ _ (fzzFermiCouplingCharacteristic_ne_zero v p)]

private theorem gamma_negative_conj (q : ℝ) :
    Complex.Gamma (1 + ((-q : ℝ) : ℂ) * Complex.I) =
      (starRingEnd ℂ) (Complex.Gamma (1 + (q : ℂ) * Complex.I)) := by
  rw [← Complex.Gamma_conj]
  congr 1
  simp only [map_add, map_one, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.ofReal_neg, neg_mul, mul_neg]

private theorem digamma_negative_conj (q : ℝ) :
    Complex.digamma (1 + ((-q : ℝ) : ℂ) * Complex.I) =
      (starRingEnd ℂ) (Complex.digamma (1 + (q : ℂ) * Complex.I)) := by
  rw [← ReflectedDigammaAnomaly.digamma_conj]
  congr 1
  simp only [map_add, map_one, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.ofReal_neg, neg_mul, mul_neg]

theorem fzzFermiCouplingCharacteristic_eq_normSq (v p : ℝ) :
    fzzFermiCouplingCharacteristic v p =
      (Complex.normSq (Complex.Gamma (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I)) : ℂ) := by
  rw [fzzFermiCouplingCharacteristic_eq, neg_div, gamma_negative_conj, Complex.mul_conj]

theorem fzzFermiCouplingCharacteristic_re_pos (v p : ℝ) :
    0 < (fzzFermiCouplingCharacteristic v p).re := by
  rw [fzzFermiCouplingCharacteristic_eq_normSq, Complex.ofReal_re, Complex.normSq_pos]
  apply Complex.Gamma_ne_zero_of_re_pos
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
    add_zero]
  exact zero_lt_one

theorem fzzFermiCouplingCharacteristic_im (v p : ℝ) :
    (fzzFermiCouplingCharacteristic v p).im = 0 := by
  rw [fzzFermiCouplingCharacteristic_eq_normSq, Complex.ofReal_im]

theorem fzzFermiCouplingCharacteristic_neg_momentum (v p : ℝ) :
    fzzFermiCouplingCharacteristic v (-p) = fzzFermiCouplingCharacteristic v p := by
  simp only [fzzFermiCouplingCharacteristic_eq, neg_neg, mul_comm]

theorem fzzFermiCouplingMarkedResponse_re (v p : ℝ) :
    (fzzFermiCouplingMarkedResponse v p).re = 0 := by
  rw [fzzFermiCouplingMarkedResponse_eq, neg_div, digamma_negative_conj]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    Complex.conj_re, sub_self, mul_zero, zero_mul]

theorem fzzFermiCouplingMarkedResponse_neg_momentum (v p : ℝ) :
    fzzFermiCouplingMarkedResponse v (-p) = -fzzFermiCouplingMarkedResponse v p := by
  simp only [fzzFermiCouplingMarkedResponse_eq, neg_neg]
  ring

private theorem marked_response_im_neg {p : ℝ} (v : ℝ) (hp : 0 < p) :
    (fzzFermiCouplingMarkedResponse v p).im < 0 := by
  have hi := verticalDigammaIm_pos 1 (p / Real.exp v) (div_pos hp (Real.exp_pos v))
  change 0 < (Complex.digamma (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I)).im at hi
  rw [fzzFermiCouplingMarkedResponse_eq, neg_div, digamma_negative_conj]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
    Complex.conj_im, zero_mul, add_zero]
  exact mul_neg_of_pos_of_neg (fzzMarkedRadialReplicaRate_pos v) (by linarith)

theorem fzzFermiCouplingMarkedResponse_im_neg (v w : ℝ) :
    (fzzFermiCouplingMarkedResponse v (Real.exp w)).im < 0 :=
  marked_response_im_neg v (Real.exp_pos w)

theorem fzzFermiCouplingMarkedResponse_zero_iff (v p : ℝ) :
    fzzFermiCouplingMarkedResponse v p = 0 ↔ p = 0 := by
  constructor
  · intro h
    rcases lt_trichotomy p 0 with hp | hp | hp
    · have hn : fzzFermiCouplingMarkedResponse v (-p) = 0 := by
        rw [fzzFermiCouplingMarkedResponse_neg_momentum, h, neg_zero]
      have hi := marked_response_im_neg v (neg_pos.mpr hp)
      rw [hn, Complex.zero_im] at hi
      exact False.elim (lt_irrefl _ hi)
    · exact hp
    · have hi := marked_response_im_neg v hp
      rw [h, Complex.zero_im] at hi
      exact False.elim (lt_irrefl _ hi)
  · rintro rfl
    simp only [fzzFermiCouplingMarkedResponse_eq, neg_zero, sub_self, mul_zero]

/-- The product-rule insertion for two independently integrated, reflected source factors. -/
def fzzFermiCouplingPairedMarkedIntegral (v p : ℝ) : ℂ :=
  fzzFermiCouplingMarkedIntegral v p * fzzFermiCouplingCharacteristic v (-p) +
    fzzFermiCouplingCharacteristic v p * fzzFermiCouplingMarkedIntegral v (-p)

theorem fzzFermiCouplingPairedMarkedIntegral_eq_zero (v p : ℝ) :
    fzzFermiCouplingPairedMarkedIntegral v p = 0 := by
  simp only [fzzFermiCouplingPairedMarkedIntegral, fzzFermiCouplingMarkedIntegral_eq,
    fzzFermiCouplingCharacteristic_neg_momentum, neg_neg]
  ring

def fzzFermiCouplingPairedMarkedResponse (v p : ℝ) : ℂ :=
  fzzFermiCouplingPairedMarkedIntegral v p /
    (fzzFermiCouplingCharacteristic v p * fzzFermiCouplingCharacteristic v (-p))

theorem fzzFermiCouplingPairedMarkedResponse_eq_zero (v p : ℝ) :
    fzzFermiCouplingPairedMarkedResponse v p = 0 := by
  rw [fzzFermiCouplingPairedMarkedResponse, fzzFermiCouplingPairedMarkedIntegral_eq_zero, zero_div]

theorem hasDerivAt_fzzFermiCouplingPairedMarkedResponse (v p : ℝ) :
    HasDerivAt (fzzFermiCouplingPairedMarkedResponse v) 0 p := by
  have he : fzzFermiCouplingPairedMarkedResponse v = fun _ : ℝ => (0 : ℂ) := by
    funext t
    exact fzzFermiCouplingPairedMarkedResponse_eq_zero v t
  rw [he]
  exact hasDerivAt_const p (0 : ℂ)

theorem fzzFermiCouplingPairedMixedResponse_eq_zero (v p : ℝ) :
    deriv (fzzFermiCouplingPairedMarkedResponse v) p = 0 :=
  (hasDerivAt_fzzFermiCouplingPairedMarkedResponse v p).deriv

/-- Independent integration of reflected factors can erase the fixed-coupling mixed zero set. -/
theorem fzzFermiCoupling_nonzero_momentum_cancellation (v w : ℝ) :
    Real.exp w ≠ 0 ∧
      deriv (fzzFermiCouplingPairedMarkedResponse v) (Real.exp w) = 0 ∧
      fzzFermiCouplingMarkedResponse v (Real.exp w) ≠ 0 := by
  exact ⟨Real.exp_ne_zero w, fzzFermiCouplingPairedMixedResponse_eq_zero v _,
    fun h => Real.exp_ne_zero w ((fzzFermiCouplingMarkedResponse_zero_iff v _).mp h)⟩


theorem integrable_fzzFermiCouplingDensity_integrand (v x : ℝ) :
    Integrable (fun u : ℝ => fzzExponentialLogCouplingDensity u * fzzRadialCouplingDensity u v x) := by
  have hi : Integrable gammaTwoLogDensity :=
    Integrable.of_integral_ne_zero (by rw [gamma_two_log_mass]; exact one_ne_zero)
  simp only [coupling_density_integrand]
  exact (hi.comp_add_left _).const_mul _

theorem fzzFermiCouplingJointDensity_mass (v : ℝ) :
    (∫ z : ℝ × ℝ, fzzFermiCouplingJointDensity v z ∂(volume.prod volume)) = 1 := by
  rw [integral_prod _ (integrable_fzzFermiCouplingJointDensity v)]
  simp only [fzzFermiCouplingJointDensity, integral_const_mul,
    fzzRadialCouplingDensity_mass, mul_one, fzzExponentialLogCouplingDensity_mass]

theorem integrable_fzzFermiCouplingDensity (v : ℝ) :
    Integrable (fzzFermiCouplingDensity v) :=
  (integrable_fzzFermiCouplingJointDensity v).integral_prod_right

theorem fzzFermiCouplingDensity_mass (v : ℝ) :
    (∫ x : ℝ, fzzFermiCouplingDensity v x) = 1 := by
  have h := fzzFermiCouplingJointDensity_mass v
  rw [integral_prod_symm _ (integrable_fzzFermiCouplingJointDensity v)] at h
  exact h

theorem integrable_fzzFermiCouplingCharacteristic_integrand (v p : ℝ) :
    Integrable (fun u : ℝ => (fzzExponentialLogCouplingDensity u : ℂ) *
      fzzRadialCouplingCharacteristic u v p) := by
  have h := (joint_character_integrable v p).integral_prod_left
  simpa only [fzzFermiCouplingJointDensity, Complex.ofReal_mul, mul_assoc,
    integral_const_mul, fzzRadialCouplingCharacteristic] using h

private theorem shared_pair_zero (u v p : ℝ) :
    fzzMarkedRadialReplicaPairedIntegral u v p 0 = fzzFermiCouplingCharacteristic v p := by
  rw [fzzMarkedRadialReplicaPairedIntegral, fzzMarkedRadialReplicaIntegral_zero,
    fzzMarkedRadialReplicaIntegral_zero, fzzRadialCouplingCharacteristic_eq_gamma,
    fzzRadialCouplingCharacteristic_eq_gamma, fzzFermiCouplingCharacteristic_eq]
  have he : Complex.exp (-(((p*u/Real.exp v : ℝ) : ℂ)*Complex.I)) *
      Complex.exp (-((((-p)*u/Real.exp v : ℝ) : ℂ)*Complex.I)) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1
    push_cast
    ring
  calc
    _ = (Complex.exp (-(((p*u/Real.exp v : ℝ) : ℂ)*Complex.I)) *
        Complex.exp (-((((-p)*u/Real.exp v : ℝ) : ℂ)*Complex.I))) *
        (Complex.Gamma (1+((p/Real.exp v : ℝ) : ℂ)*Complex.I) *
          Complex.Gamma (1+((-p/Real.exp v : ℝ) : ℂ)*Complex.I)) := by ring
    _ = _ := by rw [he, one_mul]

private theorem shared_pair_jet (u v p : ℝ) :
    deriv (fzzMarkedRadialReplicaPairedIntegral u v p) 0 =
      ((2*fzzMarkedRadialReplicaRate v *
        (u-(Complex.digamma (1+((p/Real.exp v : ℝ) : ℂ)*Complex.I)).re) : ℝ) : ℂ) *
        fzzFermiCouplingCharacteristic v p := by
  have h := fzzMarkedRadialReplicaPairedResponse_eq u v p
  rw [fzzMarkedRadialReplicaPairedResponse, shared_pair_zero] at h
  exact (div_eq_iff (fzzFermiCouplingCharacteristic_ne_zero v p)).mp h

private theorem coupling_moment_zero_integrable :
    Integrable (fun u : ℝ => (u : ℂ) * (fzzExponentialLogCouplingDensity u : ℂ)) := by
  have h := coupling_moment_integrable 0
  change Integrable (fun u : ℝ => (u : ℂ) * (fzzExponentialLogCouplingDensity u : ℂ) *
    Complex.exp ((((0 : ℝ)*u : ℝ) : ℂ)*Complex.I)) at h
  simpa only [zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one] using h

private theorem coupling_moment_zero_integral :
    (∫ u : ℝ, (u : ℂ) * (fzzExponentialLogCouplingDensity u : ℂ)) =
      ((Complex.digamma 1).re : ℂ) := by
  have h := coupling_moment_integral 0
  simp only [couplingMomentIntegrand, zero_mul, Complex.ofReal_zero,
    Complex.exp_zero, mul_one, add_zero, Complex.Gamma_one, one_mul] at h
  have hc := digamma_negative_conj 0
  simp only [neg_zero, Complex.ofReal_zero, zero_mul, add_zero] at hc
  exact h.trans (Complex.conj_eq_iff_re.mp hc.symm).symm

/-- One coupling variable is shared by both reflected factors before their integration. -/
def fzzFermiSharedCouplingCharacteristic (v p : ℝ) : ℂ :=
  ∫ u : ℝ, (fzzExponentialLogCouplingDensity u : ℂ) *
    fzzMarkedRadialReplicaPairedIntegral u v p 0

def fzzFermiSharedCouplingMarkedIntegral (v p : ℝ) : ℂ :=
  ∫ u : ℝ, (fzzExponentialLogCouplingDensity u : ℂ) *
    deriv (fzzMarkedRadialReplicaPairedIntegral u v p) 0

theorem fzzFermiSharedCouplingCharacteristic_eq (v p : ℝ) :
    fzzFermiSharedCouplingCharacteristic v p = fzzFermiCouplingCharacteristic v p := by
  simp only [fzzFermiSharedCouplingCharacteristic, shared_pair_zero, integral_mul_const,
    integral_complex_ofReal, fzzExponentialLogCouplingDensity_mass, Complex.ofReal_one, one_mul]

theorem integrable_fzzFermiSharedCouplingCharacteristic_integrand (v p : ℝ) :
    Integrable (fun u : ℝ => (fzzExponentialLogCouplingDensity u : ℂ) *
      fzzMarkedRadialReplicaPairedIntegral u v p 0) := by
  simp only [shared_pair_zero]
  exact integrable_fzzExponentialLogCouplingDensity.ofReal.mul_const _

private theorem shared_marked_integrand (v p u : ℝ) :
    (fzzExponentialLogCouplingDensity u : ℂ) *
      deriv (fzzMarkedRadialReplicaPairedIntegral u v p) 0 =
    (2*(fzzMarkedRadialReplicaRate v : ℂ)*fzzFermiCouplingCharacteristic v p) *
      ((u : ℂ)*(fzzExponentialLogCouplingDensity u : ℂ) -
        ((Complex.digamma (1+((p/Real.exp v : ℝ) : ℂ)*Complex.I)).re : ℂ) *
          (fzzExponentialLogCouplingDensity u : ℂ)) := by
  rw [shared_pair_jet]
  push_cast
  ring

theorem integrable_fzzFermiSharedCouplingMarked_integrand (v p : ℝ) :
    Integrable (fun u : ℝ => (fzzExponentialLogCouplingDensity u : ℂ) *
      deriv (fzzMarkedRadialReplicaPairedIntegral u v p) 0) := by
  simp only [shared_marked_integrand]
  exact (coupling_moment_zero_integrable.sub
    (integrable_fzzExponentialLogCouplingDensity.ofReal.const_mul _)).const_mul _

theorem fzzFermiSharedCouplingMarkedIntegral_eq (v p : ℝ) :
    fzzFermiSharedCouplingMarkedIntegral v p =
      fzzMarkedRadialReplicaPairedResponse (Complex.digamma 1).re v p *
        fzzFermiCouplingCharacteristic v p := by
  have hb : Integrable (fun u : ℝ => (fzzExponentialLogCouplingDensity u : ℂ)) :=
    integrable_fzzExponentialLogCouplingDensity.ofReal
  simp only [fzzFermiSharedCouplingMarkedIntegral, shared_marked_integrand, integral_const_mul]
  rw [integral_sub coupling_moment_zero_integrable
      (hb.const_mul (((Complex.digamma (1+((p/Real.exp v : ℝ) : ℂ)*Complex.I)).re) : ℂ)),
    integral_const_mul, coupling_moment_zero_integral, integral_complex_ofReal,
    fzzExponentialLogCouplingDensity_mass, fzzMarkedRadialReplicaPairedResponse_eq]
  push_cast
  ring

def fzzFermiSharedCouplingMarkedResponse (v p : ℝ) : ℂ :=
  fzzFermiSharedCouplingMarkedIntegral v p / fzzFermiSharedCouplingCharacteristic v p

theorem fzzFermiSharedCouplingMarkedResponse_eq (v p : ℝ) :
    fzzFermiSharedCouplingMarkedResponse v p =
      fzzMarkedRadialReplicaPairedResponse (Complex.digamma 1).re v p := by
  rw [fzzFermiSharedCouplingMarkedResponse, fzzFermiSharedCouplingMarkedIntegral_eq,
    fzzFermiSharedCouplingCharacteristic_eq,
    mul_div_cancel_right₀ _ (fzzFermiCouplingCharacteristic_ne_zero v p)]

theorem fzzFermiSharedCouplingMixedResponse_zero_iff (v p : ℝ) :
    deriv (fzzFermiSharedCouplingMarkedResponse v) p = 0 ↔ p = 0 := by
  have he : fzzFermiSharedCouplingMarkedResponse v =
      fzzMarkedRadialReplicaPairedResponse (Complex.digamma 1).re v := by
    funext t
    exact fzzFermiSharedCouplingMarkedResponse_eq v t
  rw [he]
  exact fzzMarkedRadialReplicaPairedMixedResponse_zero_iff _ v p

theorem fzzFermiSharedCouplingMixedResponse_re_neg (v w : ℝ) :
    (deriv (fzzFermiSharedCouplingMarkedResponse v) (Real.exp w)).re < 0 := by
  have he : fzzFermiSharedCouplingMarkedResponse v =
      fzzMarkedRadialReplicaPairedResponse (Complex.digamma 1).re v := by
    funext t
    exact fzzFermiSharedCouplingMarkedResponse_eq v t
  rw [he]
  exact fzzMarkedRadialReplicaPairedMixedResponse_re_neg _ v w

theorem fzzFermiSharedCoupling_differs_from_independent (v w : ℝ) :
    deriv (fzzFermiSharedCouplingMarkedResponse v) (Real.exp w) ≠
      deriv (fzzFermiCouplingPairedMarkedResponse v) (Real.exp w) := by
  rw [fzzFermiCouplingPairedMixedResponse_eq_zero]
  exact fun h => Real.exp_ne_zero w ((fzzFermiSharedCouplingMixedResponse_zero_iff v _).mp h)

private def sharedRealResponse (v p : ℝ) : ℝ :=
  (fzzMarkedRadialReplicaPairedResponse (Complex.digamma 1).re v p).re

private theorem shared_real_deriv (v p : ℝ) :
    HasDerivAt (sharedRealResponse v)
      (2*fzzMarkedRadialReplicaRate v/Real.exp v *
        (deriv Complex.digamma (1+((p/Real.exp v : ℝ) : ℂ)*Complex.I)).im) p := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt p
    (hasDerivAt_fzzMarkedRadialReplicaPairedResponse_momentum (Complex.digamma 1).re v p)
  exact h

private theorem shared_real_strictAnti (v : ℝ) :
    StrictAntiOn (sharedRealResponse v) (Ici (0 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · exact fun p _ => (shared_real_deriv v p).continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Ici] at hp
    rw [(shared_real_deriv v p).deriv]
    exact mul_neg_of_pos_of_neg
      (div_pos (mul_pos (by norm_num) (fzzMarkedRadialReplicaRate_pos v)) (Real.exp_pos v))
      (_root_.RHTower.deriv_digamma_vertical_im_neg zero_lt_one
        (div_pos hp (Real.exp_pos v)))

theorem fzzFermiSharedCouplingMarkedResponse_zero (v : ℝ) :
    fzzFermiSharedCouplingMarkedResponse v 0 = 0 := by
  rw [fzzFermiSharedCouplingMarkedResponse_eq, fzzMarkedRadialReplicaPairedResponse_eq]
  simp

theorem fzzFermiSharedCouplingMarkedResponse_neg_momentum (v p : ℝ) :
    fzzFermiSharedCouplingMarkedResponse v (-p) = fzzFermiSharedCouplingMarkedResponse v p := by
  rw [fzzFermiSharedCouplingMarkedResponse_eq, fzzFermiSharedCouplingMarkedResponse_eq,
    fzzMarkedRadialReplicaPairedResponse_eq_sum, fzzMarkedRadialReplicaPairedResponse_eq_sum]
  simp only [neg_neg, add_comm]

private theorem shared_response_re_neg {p : ℝ} (v : ℝ) (hp : 0 < p) :
    (fzzFermiSharedCouplingMarkedResponse v p).re < 0 := by
  have hz : (0 : ℝ) ∈ Ici (0 : ℝ) := by simp
  have hp' : p ∈ Ici (0 : ℝ) := hp.le
  have h := shared_real_strictAnti v hz hp' hp
  change (fzzMarkedRadialReplicaPairedResponse (Complex.digamma 1).re v p).re <
    (fzzMarkedRadialReplicaPairedResponse (Complex.digamma 1).re v 0).re at h
  rw [← fzzFermiSharedCouplingMarkedResponse_eq,
    ← fzzFermiSharedCouplingMarkedResponse_eq, fzzFermiSharedCouplingMarkedResponse_zero,
    Complex.zero_re] at h
  exact h

theorem fzzFermiSharedCouplingMarkedResponse_re_neg (v w : ℝ) :
    (fzzFermiSharedCouplingMarkedResponse v (Real.exp w)).re < 0 :=
  shared_response_re_neg v (Real.exp_pos w)

theorem fzzFermiSharedCouplingMarkedResponse_zero_iff (v p : ℝ) :
    fzzFermiSharedCouplingMarkedResponse v p = 0 ↔ p = 0 := by
  constructor
  · intro h
    rcases lt_trichotomy p 0 with hp | hp | hp
    · have hn := shared_response_re_neg v (neg_pos.mpr hp)
      rw [fzzFermiSharedCouplingMarkedResponse_neg_momentum, h, Complex.zero_re] at hn
      exact False.elim (lt_irrefl _ hn)
    · exact hp
    · have hn := shared_response_re_neg v hp
      rw [h, Complex.zero_re] at hn
      exact False.elim (lt_irrefl _ hn)
  · rintro rfl
    exact fzzFermiSharedCouplingMarkedResponse_zero v

end
end GaloisForLFunctions.RHTower
