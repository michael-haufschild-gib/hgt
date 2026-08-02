import GaloisForLFunctions.RHTower.MobiusThetaInternalJetCofinalComplexLanding
import GaloisForLFunctions.RHTower.MobiusThetaInternalJetPhysicalGraph

/-!
# Complex prime-normal graph for internally promoted Möbius--theta sources

The physical prime-normal residual isolates an integer label before taking the exponent-cofinal
limit.  This file identifies the exact complex Fourier--Laplace shadow of both the isolated head
and the complete residual retaining every coefficient `n ≥ p`.  The raw `p`-head is defined before
spectral evaluation from the Möbius coefficient, logarithmic translation, half-density, and local
theta jet.  Its transform is

`LSeries.term μ (m * (1/2 + I*w)) p * XiC^(k)(w)`.

For prime `p`, reflected raw amplitudes have the unsquared modular ratio

`p ^ (m * (2 * Re(s) - 1))`.

For the complete residual, exact integral--series interchange gives the full tail multiplier;
complex Tannery domination proves that multiplier converges to `μ(p)`.  Hence at a Xi divisor of
arbitrary multiplicity the adjacent complete residual pair is eventually a nonzero vertical
conormal.  Thus label, reflection orientation, multiplicity, and all later arithmetic channels are
retained by one division-free source graph before projectivization.  No divisor datum enters a
source definition.  Hellinger/Ward admission of this graph remains the RH-bearing step.
-/

open Complex Real MeasureTheory ArithmeticFunction LSeries Set Filter Topology
open scoped BigOperators LSeries.notation Moebius

noncomputable section
namespace RHTower

/-- A half-density Dirichlet coefficient promoted by an `m`-fold logarithmic translation lands at
the centered parameter dilated by `m`. -/
theorem LSeries_term_halfDilation_mul_exp_neg_I_mul_log
    (f : ℕ → ℂ) (m n : ℕ) (w : ℂ) :
    LSeries.term f ((m : ℂ) / 2) n *
        Complex.exp (-I * w * ((m : ℝ) * Real.log n : ℝ)) =
      LSeries.term f ((m : ℂ) * mobiusThetaCenteredParameter w) n := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  have hpow :
      Complex.exp (-I * w * ((m : ℝ) * Real.log n : ℝ)) =
        (n : ℂ) ^ (-I * w * (m : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn)]
    change Complex.exp (-I * w * (((m : ℝ) * Real.log n : ℝ) : ℂ)) =
      Complex.exp (Complex.log ((n : ℝ) : ℂ) * (-I * w * (m : ℂ)))
    rw [← Complex.ofReal_log hnpos.le]
    congr 1
    push_cast
    ring
  rw [hpow]
  rw [show -I * w * (m : ℂ) = -((m : ℂ) * (I * w)) by ring,
    Complex.cpow_neg]
  rw [mobiusThetaCenteredParameter]
  rw [show (m : ℂ) * (1 / 2 + I * w) =
      (m : ℂ) / 2 + (m : ℂ) * (I * w) by ring]
  rw [Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Arithmetic amplitude of one raw integer head at complex Dirichlet parameter `s`. -/
def mobiusThetaPrimeRawAmplitude (p m : ℕ) (s : ℂ) : ℂ :=
  LSeries.term (↗(μ : ArithmeticFunction ℤ)) ((m : ℂ) * s) p

/-- Exact modulus of a prime raw amplitude. -/
theorem norm_mobiusThetaPrimeRawAmplitude_of_prime
    {p : ℕ} (hp : p.Prime) (m : ℕ) (s : ℂ) :
    ‖mobiusThetaPrimeRawAmplitude p m s‖ =
      (p : ℝ) ^ (-((m : ℝ) * s.re)) := by
  rw [mobiusThetaPrimeRawAmplitude, LSeries.norm_term_eq]
  rw [ArithmeticFunction.moebius_apply_prime hp]
  norm_num only [Int.cast_neg, Int.cast_one, norm_neg, norm_one,
    one_div, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero]
  rw [if_neg hp.ne_zero]
  rw [Real.rpow_neg (by exact_mod_cast hp.pos.le : (0 : ℝ) ≤ p)]

/-- The raw prime head never vanishes. -/
theorem mobiusThetaPrimeRawAmplitude_ne_zero_of_prime
    {p : ℕ} (hp : p.Prime) (m : ℕ) (s : ℂ) :
    mobiusThetaPrimeRawAmplitude p m s ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_mobiusThetaPrimeRawAmplitude_of_prime hp]
  exact Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _

/-- Unsquared reflected modular cocycle of one prime head. -/
theorem mobiusThetaPrimeRawAmplitude_reflection_ratio
    {p : ℕ} (hp : p.Prime) (m : ℕ) (s : ℂ) :
    ‖mobiusThetaPrimeRawAmplitude p m (1 - s)‖ /
        ‖mobiusThetaPrimeRawAmplitude p m s‖ =
      (p : ℝ) ^ ((m : ℝ) * (2 * s.re - 1)) := by
  rw [norm_mobiusThetaPrimeRawAmplitude_of_prime hp,
    norm_mobiusThetaPrimeRawAmplitude_of_prime hp]
  rw [Complex.sub_re, Complex.one_re]
  rw [← Real.rpow_sub (by exact_mod_cast hp.pos : (0 : ℝ) < p)]
  congr 1
  ring

/-- Reverse orientation of the unsquared modular cocycle. -/
theorem mobiusThetaPrimeRawAmplitude_reverseReflection_ratio
    {p : ℕ} (hp : p.Prime) (m : ℕ) (s : ℂ) :
    ‖mobiusThetaPrimeRawAmplitude p m s‖ /
        ‖mobiusThetaPrimeRawAmplitude p m (1 - s)‖ =
      (p : ℝ) ^ (-((m : ℝ) * (2 * s.re - 1))) := by
  rw [norm_mobiusThetaPrimeRawAmplitude_of_prime hp,
    norm_mobiusThetaPrimeRawAmplitude_of_prime hp]
  rw [Complex.sub_re, Complex.one_re]
  rw [← Real.rpow_sub (by exact_mod_cast hp.pos : (0 : ℝ) < p)]
  congr 1
  ring

/-- Reflection-odd source graph profile in the continuous Cartan clock
`t = m log p`. -/
theorem mobiusThetaPrimeRawAmplitude_reflectionOddProfile
    {p : ℕ} (hp : p.Prime) (m : ℕ) (s : ℂ) :
    ‖mobiusThetaPrimeRawAmplitude p m (1 - s)‖ /
          ‖mobiusThetaPrimeRawAmplitude p m s‖ -
        ‖mobiusThetaPrimeRawAmplitude p m s‖ /
          ‖mobiusThetaPrimeRawAmplitude p m (1 - s)‖ =
      Real.exp ((2 * s.re - 1) * ((m : ℝ) * Real.log p)) -
        Real.exp (-((2 * s.re - 1) * ((m : ℝ) * Real.log p))) := by
  rw [mobiusThetaPrimeRawAmplitude_reflection_ratio hp,
    mobiusThetaPrimeRawAmplitude_reverseReflection_ratio hp]
  rw [Real.rpow_def_of_pos (by exact_mod_cast hp.pos : (0 : ℝ) < p),
    Real.rpow_def_of_pos (by exact_mod_cast hp.pos : (0 : ℝ) < p)]
  congr 1 <;> ring_nf

/-- Raw translated `p`-head with internal jet promotion performed in its local theta coordinate. -/
def mobiusThetaInternalJetRawHeadSource
    (k p m : ℕ) (x : ℝ) : ℂ :=
  LSeries.term (↗(μ : ArithmeticFunction ℤ)) ((m : ℂ) / 2) p *
    (-I * ((x - (m : ℝ) * Real.log p : ℝ) : ℂ)) ^ k *
      (thetaCuspFullSource (x - (m : ℝ) * Real.log p) : ℂ)

/-- Fourier--Laplace integrand of one raw internally promoted prime head. -/
def mobiusThetaInternalJetRawHeadIntegrand
    (k p m : ℕ) (w : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-I * w * (x : ℂ)) *
    mobiusThetaInternalJetRawHeadSource k p m x

/-- Fourier--Laplace transform of one raw internally promoted prime head. -/
def mobiusThetaInternalJetRawHeadFourierLaplace
    (k p m : ℕ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, mobiusThetaInternalJetRawHeadIntegrand k p m w x

theorem mobiusThetaInternalJetRawHeadIntegrand_eq
    (k p m : ℕ) (w : ℂ) (x : ℝ) :
    mobiusThetaInternalJetRawHeadIntegrand k p m w x =
      mobiusThetaPrimeRawAmplitude p m (mobiusThetaCenteredParameter w) *
        thetaCuspFourierLaplaceJetIntegrand k w
          (x - (m : ℝ) * Real.log p) := by
  rw [mobiusThetaInternalJetRawHeadIntegrand,
    mobiusThetaInternalJetRawHeadSource, mobiusThetaPrimeRawAmplitude,
    thetaCuspFourierLaplaceJetIntegrand,
    thetaCuspFourierLaplaceIntegrand]
  rw [show Complex.exp (-I * w * (x : ℂ)) =
      Complex.exp (-I * w * (((m : ℝ) * Real.log p : ℝ) : ℂ)) *
        Complex.exp (-I * w *
          ((x - (m : ℝ) * Real.log p : ℝ) : ℂ)) by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring]
  rw [← LSeries_term_halfDilation_mul_exp_neg_I_mul_log]
  ring

theorem integrable_mobiusThetaInternalJetRawHeadIntegrand
    (k p m : ℕ) {w : ℂ} (hw : |w.im| < 1) :
    Integrable (mobiusThetaInternalJetRawHeadIntegrand k p m w) := by
  rw [show mobiusThetaInternalJetRawHeadIntegrand k p m w = fun x : ℝ =>
      mobiusThetaPrimeRawAmplitude p m (mobiusThetaCenteredParameter w) *
        thetaCuspFourierLaplaceJetIntegrand k w
          (x - (m : ℝ) * Real.log p) by
    funext x
    exact mobiusThetaInternalJetRawHeadIntegrand_eq k p m w x]
  exact ((integrable_thetaCuspFourierLaplaceJetIntegrand k hw).comp_add_right
    (-((m : ℝ) * Real.log p))).const_mul _

/-- **Exact raw-head source-to-Xi landing.**  Source translation produces the arithmetic prime
amplitude, while internal local promotion produces the corresponding Xi jet. -/
theorem mobiusThetaInternalJetRawHeadFourierLaplace_eq
    (k p m : ℕ) {w : ℂ} (hw : |w.im| < 1) :
    mobiusThetaInternalJetRawHeadFourierLaplace k p m w =
      mobiusThetaPrimeRawAmplitude p m (mobiusThetaCenteredParameter w) *
        iteratedDeriv k XiC w := by
  rw [mobiusThetaInternalJetRawHeadFourierLaplace]
  simp_rw [mobiusThetaInternalJetRawHeadIntegrand_eq]
  rw [integral_const_mul]
  rw [show
      (∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand k w
        (x - (m : ℝ) * Real.log p)) =
      ∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand k w x by
    simpa only [sub_eq_add_neg] using
      (integral_add_right_eq_self
        (thetaCuspFourierLaplaceJetIntegrand k w)
        (-((m : ℝ) * Real.log p)))]
  rw [← iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet]
  exact (abs_lt.mp hw)

/-- Singular normal reader applied to the raw head: half-density gain followed by logarithmic
recentering. -/
def mobiusThetaInternalJetRawHeadNormalReader
    (k p m : ℕ) (x : ℝ) : ℂ :=
  (((p : ℝ) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
    mobiusThetaInternalJetRawHeadSource k p m
      (x + (m : ℝ) * Real.log p)

/-- The normal reader exactly recovers the oriented local theta jet. -/
theorem mobiusThetaInternalJetRawHeadNormalReader_eq
    {p : ℕ} (hp : 0 < p) (k m : ℕ) (x : ℝ) :
    mobiusThetaInternalJetRawHeadNormalReader k p m x =
      ((μ p : ℤ) : ℂ) * (-I * (x : ℂ)) ^ k *
        (thetaCuspFullSource x : ℂ) := by
  rw [mobiusThetaInternalJetRawHeadNormalReader,
    mobiusThetaInternalJetRawHeadSource,
    LSeries.term_of_ne_zero hp.ne']
  have hpR : (0 : ℝ) ≤ p := by positivity
  rw [Complex.ofReal_cpow hpR]
  have hpcpow : (p : ℂ) ^ ((m : ℂ) / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Nat.cast_ne_zero.mpr hp.ne'))
  push_cast
  ring_nf
  field_simp [hpcpow]

/-- Division-free adjacent-jet conormal pair of one raw integer head. -/
def mobiusThetaInternalJetRawHeadConormalPair
    (k p m : ℕ) (w : ℂ) : ℂ × ℂ :=
  (mobiusThetaInternalJetRawHeadFourierLaplace k p m w,
    mobiusThetaInternalJetRawHeadFourierLaplace (k + 1) p m w)

/-- **Prime-labelled multiplicity retention.**  At every actual Xi divisor, the raw prime-head
conormal is vertical and nonzero at the first nonvanishing jet.  The vertical coefficient is the
same source-derived prime amplitude whose reflected ratio gives the Cartan cocycle above. -/
theorem mobiusThetaInternalJetRawHeadConormalPair_at_divisor
    {p : ℕ} (hp : p.Prime) (m : ℕ) (rho : XiDivisorSupport) :
    mobiusThetaInternalJetRawHeadConormalPair
        (xiSupportMultiplicity rho - 1) p m
        (xiSpectralPointSupport rho) =
      (0, mobiusThetaPrimeRawAmplitude p m (rho : ℂ) *
        iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho)) ∧
    mobiusThetaPrimeRawAmplitude p m (rho : ℂ) *
        iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho) ≠ 0 := by
  have hrpos : 0 < xiSupportMultiplicity rho :=
    xiSupportMultiplicity_pos rho
  have hrpred : xiSupportMultiplicity rho - 1 < xiSupportMultiplicity rho :=
    Nat.sub_lt hrpos (by omega)
  have hzero :=
    iteratedDeriv_XiC_eq_zero_before_supportMultiplicity rho hrpred
  have hsucc :
      xiSupportMultiplicity rho - 1 + 1 = xiSupportMultiplicity rho := by
    omega
  have hfirst :=
    mobiusThetaInternalJetRawHeadFourierLaplace_eq
      (xiSupportMultiplicity rho - 1) p m
      (abs_im_xiSpectralPointSupport_lt_one rho)
  have hsecond :=
    mobiusThetaInternalJetRawHeadFourierLaplace_eq
      (xiSupportMultiplicity rho) p m
      (abs_im_xiSpectralPointSupport_lt_one rho)
  rw [mobiusThetaCenteredParameter_xiSpectralPointSupport] at hfirst hsecond
  constructor
  · rw [mobiusThetaInternalJetRawHeadConormalPair, hfirst, hsucc,
      hsecond, hzero, mul_zero]
  · exact mul_ne_zero
      (mobiusThetaPrimeRawAmplitude_ne_zero_of_prime hp m (rho : ℂ))
      (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)

/-! ## Complete prime-normal residual graph

The raw head above identifies the retained channel.  The source required by Route R is the full
residual, including every `n ≥ p` coefficient before transformation.  The following construction
performs the prime recentering on the whole source and proves exact integral--series interchange.
-/

/-- Half-density normalization and the compensating spectral phase combine into the centered
complex prime power. -/
theorem mobiusThetaPrimeNormal_halfDensityPhase
    {p : ℕ} (hp : 0 < p) (m : ℕ) (w : ℂ) :
    ((((p : ℝ) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
        Complex.exp (I * w * ((m : ℝ) * Real.log p : ℝ))) =
      (p : ℂ) ^ ((m : ℂ) * mobiusThetaCenteredParameter w) := by
  rw [Complex.ofReal_cpow (by exact_mod_cast hp.le : (0 : ℝ) ≤ p)]
  norm_num only [Complex.ofReal_natCast, Complex.ofReal_div,
    Complex.ofReal_natCast]
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hp.ne')]
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hp.ne')]
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.ofReal_log
        (by exact_mod_cast hp.le : (0 : ℝ) ≤ p)).symm
  rw [hlog, ← Complex.exp_add]
  congr 1
  rw [mobiusThetaCenteredParameter]
  push_cast
  ring

/-- Exact recentering law for an arbitrary arithmetic channel `n`. -/
theorem mobiusThetaPrimeNormal_coefficient_recenter
    {p : ℕ} (hp : 0 < p) (m n : ℕ) (w : ℂ) :
    ((((p : ℝ) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
          LSeries.term (↗(μ : ArithmeticFunction ℤ)) ((m : ℂ) / 2) n *
        Complex.exp (-I * w *
          ((m : ℝ) * (Real.log n - Real.log p) : ℝ))) =
      (p : ℂ) ^ ((m : ℂ) * mobiusThetaCenteredParameter w) *
        LSeries.term (↗(μ : ArithmeticFunction ℤ))
          ((m : ℂ) * mobiusThetaCenteredParameter w) n := by
  rw [show
      Complex.exp (-I * w *
          ((m : ℝ) * (Real.log n - Real.log p) : ℝ)) =
        Complex.exp (I * w * ((m : ℝ) * Real.log p : ℝ)) *
          Complex.exp (-I * w *
            ((m : ℝ) * Real.log n : ℝ)) by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring]
  rw [← LSeries_term_halfDilation_mul_exp_neg_I_mul_log]
  rw [← mobiusThetaPrimeNormal_halfDensityPhase hp]
  ring

/-- Complete normalized residual packet.  Index `j` represents exactly `n = p + j`; no head
truncation is made. -/
def mobiusThetaInternalJetPrimeNormalResidualSourceTerm
    (k p m j : ℕ) (x : ℝ) : ℂ :=
  ((((p : ℝ) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
      LSeries.term (↗(μ : ArithmeticFunction ℤ)) ((m : ℂ) / 2) (p + j)) *
    (-I * ((x - (m : ℝ) *
      (Real.log (p + j) - Real.log p) : ℝ) : ℂ)) ^ k *
      (thetaCuspFullSource (x - (m : ℝ) *
        (Real.log (p + j) - Real.log p)) : ℂ)

/-- Complex coefficient read from the `j`-th recentered residual packet. -/
def mobiusThetaPrimeNormalResidualSpectralCoefficient
    (p m : ℕ) (w : ℂ) (j : ℕ) : ℂ :=
  (p : ℂ) ^ ((m : ℂ) * mobiusThetaCenteredParameter w) *
    LSeries.term (↗(μ : ArithmeticFunction ℤ))
      ((m : ℂ) * mobiusThetaCenteredParameter w) (p + j)

def mobiusThetaInternalJetPrimeNormalResidualIntegrand
    (k p m : ℕ) (w : ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (-I * w * (x : ℂ)) *
    mobiusThetaInternalJetPrimeNormalResidualSourceTerm k p m j x

theorem mobiusThetaInternalJetPrimeNormalResidualIntegrand_eq
    {p : ℕ} (hp : 0 < p) (k m : ℕ) (w : ℂ) (j : ℕ) (x : ℝ) :
    mobiusThetaInternalJetPrimeNormalResidualIntegrand k p m w j x =
      mobiusThetaPrimeNormalResidualSpectralCoefficient p m w j *
        thetaCuspFourierLaplaceJetIntegrand k w
          (x - (m : ℝ) *
            (Real.log (p + j) - Real.log p)) := by
  let d : ℝ := (m : ℝ) * (Real.log (p + j) - Real.log p)
  let c : ℂ := (((p : ℝ) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
    LSeries.term (↗(μ : ArithmeticFunction ℤ)) ((m : ℂ) / 2) (p + j)
  let a : ℂ := (p : ℂ) ^
      ((m : ℂ) * mobiusThetaCenteredParameter w) *
    LSeries.term (↗(μ : ArithmeticFunction ℤ))
      ((m : ℂ) * mobiusThetaCenteredParameter w) (p + j)
  change Complex.exp (-I * w * (x : ℂ)) *
      (c * (-I * ((x - d : ℝ) : ℂ)) ^ k *
        (thetaCuspFullSource (x - d) : ℂ)) =
    a * ((-I * ((x - d : ℝ) : ℂ)) ^ k *
      (Complex.exp (-I * w * ((x - d : ℝ) : ℂ)) *
        (thetaCuspFullSource (x - d) : ℂ)))
  have hphase : Complex.exp (-I * w * (x : ℂ)) =
      Complex.exp (-I * w * (d : ℂ)) *
        Complex.exp (-I * w * ((x - d : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hcoeff : c * Complex.exp (-I * w * (d : ℂ)) = a := by
    simpa only [c, a, d, Nat.cast_add] using
      mobiusThetaPrimeNormal_coefficient_recenter hp m (p + j) w
  rw [hphase]
  calc
    (Complex.exp (-I * w * (d : ℂ)) *
          Complex.exp (-I * w * ((x - d : ℝ) : ℂ))) *
        (c * (-I * ((x - d : ℝ) : ℂ)) ^ k *
          (thetaCuspFullSource (x - d) : ℂ)) =
      (c * Complex.exp (-I * w * (d : ℂ))) *
        ((-I * ((x - d : ℝ) : ℂ)) ^ k *
          (Complex.exp (-I * w * ((x - d : ℝ) : ℂ)) *
            (thetaCuspFullSource (x - d) : ℂ))) := by ring
    _ = _ := by rw [hcoeff]

theorem integrable_mobiusThetaInternalJetPrimeNormalResidualIntegrand
    {p : ℕ} (hp : 0 < p) (k m : ℕ) {w : ℂ}
    (hw : |w.im| < 1) (j : ℕ) :
    Integrable (mobiusThetaInternalJetPrimeNormalResidualIntegrand k p m w j) := by
  rw [show mobiusThetaInternalJetPrimeNormalResidualIntegrand k p m w j =
      fun x : ℝ => mobiusThetaPrimeNormalResidualSpectralCoefficient p m w j *
        thetaCuspFourierLaplaceJetIntegrand k w
          (x - (m : ℝ) *
            (Real.log (p + j) - Real.log p)) by
    funext x
    exact mobiusThetaInternalJetPrimeNormalResidualIntegrand_eq hp k m w j x]
  exact ((integrable_thetaCuspFourierLaplaceJetIntegrand k hw).comp_add_right
    (-((m : ℝ) *
      (Real.log (p + j) - Real.log p)))).const_mul _

theorem integral_norm_mobiusThetaInternalJetPrimeNormalResidualIntegrand
    {p : ℕ} (hp : 0 < p) (k m : ℕ) (w : ℂ) (j : ℕ) :
    ∫ x : ℝ,
        ‖mobiusThetaInternalJetPrimeNormalResidualIntegrand k p m w j x‖ =
      ‖mobiusThetaPrimeNormalResidualSpectralCoefficient p m w j‖ *
        ∫ x : ℝ, ‖thetaCuspFourierLaplaceJetIntegrand k w x‖ := by
  simp_rw [mobiusThetaInternalJetPrimeNormalResidualIntegrand_eq hp, norm_mul]
  rw [integral_const_mul]
  congr 1
  simpa only [sub_eq_add_neg] using
    (integral_add_right_eq_self
      (fun x : ℝ => ‖thetaCuspFourierLaplaceJetIntegrand k w x‖)
      (-((m : ℝ) *
        (Real.log (p + j) - Real.log p))))

set_option maxHeartbeats 800000 in
theorem summable_norm_mobiusThetaPrimeNormalResidualSpectralCoefficient
    {p m : ℕ} (hm : m ≠ 0) {w : ℂ}
    (hms : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) :
    Summable (fun j : ℕ =>
      ‖mobiusThetaPrimeNormalResidualSpectralCoefficient p m w j‖) := by
  have hcoeff : LSeriesSummable (↗(μ : ArithmeticFunction ℤ))
      ((m : ℂ) * mobiusThetaCenteredParameter w) :=
    LSeriesSummable_moebius_iff.mpr
      (one_lt_natCast_mul_re hm hms)
  unfold LSeriesSummable at hcoeff
  have hshift : Summable (fun j : ℕ =>
      ‖LSeries.term (↗(μ : ArithmeticFunction ℤ))
        ((m : ℂ) * mobiusThetaCenteredParameter w) (j + p)‖) :=
    (_root_.summable_nat_add_iff p).2 hcoeff.norm
  have hmul := hshift.mul_left
    ‖(p : ℂ) ^ ((m : ℂ) * mobiusThetaCenteredParameter w)‖
  have hfun : (fun j : ℕ =>
      ‖mobiusThetaPrimeNormalResidualSpectralCoefficient p m w j‖) =
      (fun j : ℕ =>
        ‖(p : ℂ) ^ ((m : ℂ) * mobiusThetaCenteredParameter w)‖ *
          ‖LSeries.term (↗(μ : ArithmeticFunction ℤ))
            ((m : ℂ) * mobiusThetaCenteredParameter w) (j + p)‖) := by
    funext j
    rw [mobiusThetaPrimeNormalResidualSpectralCoefficient, norm_mul]
    congr 3
    omega
  rw [hfun]
  exact hmul

theorem summable_integral_norm_mobiusThetaInternalJetPrimeNormalResidualIntegrand
    {p m : ℕ} (hp : 0 < p) (hm : m ≠ 0) (k : ℕ) {w : ℂ}
    (hms : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) :
    Summable (fun j : ℕ =>
      ∫ x : ℝ,
        ‖mobiusThetaInternalJetPrimeNormalResidualIntegrand k p m w j x‖) := by
  simpa only [integral_norm_mobiusThetaInternalJetPrimeNormalResidualIntegrand hp] using
    (summable_norm_mobiusThetaPrimeNormalResidualSpectralCoefficient hm hms).mul_right
      (∫ x : ℝ, ‖thetaCuspFourierLaplaceJetIntegrand k w x‖)

theorem integral_mobiusThetaInternalJetPrimeNormalResidualIntegrand
    {p : ℕ} (hp : 0 < p) (k m : ℕ) {w : ℂ}
    (hw : |w.im| < 1) (j : ℕ) :
    ∫ x : ℝ, mobiusThetaInternalJetPrimeNormalResidualIntegrand k p m w j x =
      mobiusThetaPrimeNormalResidualSpectralCoefficient p m w j *
        iteratedDeriv k XiC w := by
  simp_rw [mobiusThetaInternalJetPrimeNormalResidualIntegrand_eq hp]
  rw [integral_const_mul]
  rw [show
      (∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand k w
        (x - (m : ℝ) * (Real.log (p + j) - Real.log p))) =
      ∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand k w x by
    simpa only [sub_eq_add_neg] using
      (integral_add_right_eq_self
        (thetaCuspFourierLaplaceJetIntegrand k w)
        (-((m : ℝ) * (Real.log (p + j) - Real.log p))))]
  rw [← iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet]
  exact abs_lt.mp hw

/-- Full source-side residual synthesized before Fourier--Laplace evaluation. -/
def mobiusThetaInternalJetPrimeNormalResidualSource
    (k p m : ℕ) (x : ℝ) : ℂ :=
  ∑' j : ℕ, mobiusThetaInternalJetPrimeNormalResidualSourceTerm k p m j x

def mobiusThetaInternalJetPrimeNormalResidualFourierLaplace
    (k p m : ℕ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-I * w * (x : ℂ)) *
    mobiusThetaInternalJetPrimeNormalResidualSource k p m x

/-- Full residual multiplier, retaining every arithmetic coefficient `n ≥ p`. -/
def mobiusThetaPrimeNormalResidualMultiplier
    (p m : ℕ) (w : ℂ) : ℂ :=
  ∑' j : ℕ, mobiusThetaPrimeNormalResidualSpectralCoefficient p m w j

/-- **Exact full residual source-to-Xi landing.**  Source synthesis precedes evaluation, and every
coefficient `n ≥ p` is retained. -/
theorem mobiusThetaInternalJetPrimeNormalResidualFourierLaplace_eq
    {p : ℕ} (hp : 0 < p) (k : ℕ) {m : ℕ} (hm : m ≠ 0)
    {w : ℂ} (hw : |w.im| < 1)
    (hms : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) :
    mobiusThetaInternalJetPrimeNormalResidualFourierLaplace k p m w =
      mobiusThetaPrimeNormalResidualMultiplier p m w *
        iteratedDeriv k XiC w := by
  unfold mobiusThetaInternalJetPrimeNormalResidualFourierLaplace
    mobiusThetaInternalJetPrimeNormalResidualSource
  have hinter (x : ℝ) :
      Complex.exp (-I * w * (x : ℂ)) *
          (∑' j : ℕ,
            mobiusThetaInternalJetPrimeNormalResidualSourceTerm k p m j x) =
        ∑' j : ℕ,
          mobiusThetaInternalJetPrimeNormalResidualIntegrand k p m w j x := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    rfl
  simp_rw [hinter]
  rw [← integral_tsum_of_summable_integral_norm
    (fun j => integrable_mobiusThetaInternalJetPrimeNormalResidualIntegrand
      hp k m hw j)
    (summable_integral_norm_mobiusThetaInternalJetPrimeNormalResidualIntegrand
      hp hm k hms)]
  simp_rw [integral_mobiusThetaInternalJetPrimeNormalResidualIntegrand hp k m hw]
  rw [tsum_mul_right]
  rfl

/-! ## Prime isolation and spectral nonannihilation -/

/-- Strict post-`p` spectral coefficient. -/
def mobiusThetaPrimeNormalSpectralTailCoefficient
    (p m : ℕ) (w : ℂ) (j : ℕ) : ℂ :=
  (p : ℂ) ^ ((m : ℂ) * mobiusThetaCenteredParameter w) *
    LSeries.term (↗(μ : ArithmeticFunction ℤ))
      ((m : ℂ) * mobiusThetaCenteredParameter w) (p + j + 1)

/-- Exact modulus of a strict post-`p` coefficient.  Its decay rate is the source ratio
`(p / n)^(m Re(s))`; spectral phase contributes no loss. -/
theorem norm_mobiusThetaPrimeNormalSpectralTailCoefficient
    {p : ℕ} (hp : 0 < p) (m : ℕ) (w : ℂ) (j : ℕ) :
    ‖mobiusThetaPrimeNormalSpectralTailCoefficient p m w j‖ =
      |(μ (p + j + 1) : ℝ)| *
        ((p : ℝ) / (p + j + 1 : ℕ)) ^
          ((m : ℝ) * (mobiusThetaCenteredParameter w).re) := by
  rw [mobiusThetaPrimeNormalSpectralTailCoefficient, norm_mul,
    Complex.norm_natCast_cpow_of_pos hp,
    LSeries.norm_term_eq, if_neg (by omega : p + j + 1 ≠ 0)]
  norm_num only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero]
  rw [Real.div_rpow (by positivity) (by positivity)]
  have hnormmu : ‖((μ (p + j + 1) : ℤ) : ℂ)‖ =
      |(μ (p + j + 1) : ℝ)| := by
    rw [show ((μ (p + j + 1) : ℤ) : ℂ) =
        (((μ (p + j + 1) : ℤ) : ℝ) : ℂ) by norm_cast,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hnormmu]
  push_cast
  ring

/-- The first residual coefficient is exactly the isolated Möbius label. -/
theorem mobiusThetaPrimeNormalResidualSpectralCoefficient_zero
    {p : ℕ} (hp : 0 < p) (m : ℕ) (w : ℂ) :
    mobiusThetaPrimeNormalResidualSpectralCoefficient p m w 0 =
      ((μ p : ℤ) : ℂ) := by
  rw [mobiusThetaPrimeNormalResidualSpectralCoefficient, Nat.add_zero,
    LSeries.term_of_ne_zero hp.ne']
  have hpow : (p : ℂ) ^ ((m : ℂ) * mobiusThetaCenteredParameter w) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Nat.cast_ne_zero.mpr hp.ne'))
  field_simp [hpow]

/-- Successor residual coefficients are exactly the strict tail. -/
theorem mobiusThetaPrimeNormalResidualSpectralCoefficient_succ
    (p m : ℕ) (w : ℂ) (j : ℕ) :
    mobiusThetaPrimeNormalResidualSpectralCoefficient p m w (j + 1) =
      mobiusThetaPrimeNormalSpectralTailCoefficient p m w j := by
  rw [mobiusThetaPrimeNormalResidualSpectralCoefficient,
    mobiusThetaPrimeNormalSpectralTailCoefficient]
  congr 2

/-- Summable, exponent-independent majorant for the strict prime-normal tail. -/
def mobiusThetaPrimeNormalSpectralTailMajorant (p j : ℕ) : ℝ :=
  ((p : ℝ) / (p + j + 1 : ℕ)) ^ (3 / 2 : ℝ)

theorem summable_mobiusThetaPrimeNormalSpectralTailMajorant (p : ℕ) :
    Summable (mobiusThetaPrimeNormalSpectralTailMajorant p) := by
  have hs : Summable (fun j : ℕ => (j : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift : Summable
      (fun j : ℕ => ((j + (p + 1) : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) :=
    (_root_.summable_nat_add_iff (p + 1)).2 hs
  have hmul := hshift.mul_left ((p : ℝ) ^ (3 / 2 : ℝ))
  refine hmul.congr fun j => ?_
  rw [mobiusThetaPrimeNormalSpectralTailMajorant,
    Real.div_rpow (by positivity) (by positivity),
    Real.rpow_neg (by positivity :
      (0 : ℝ) ≤ ((j + (p + 1) : ℕ) : ℝ))]
  push_cast
  ring_nf

theorem norm_mobiusThetaPrimeNormalSpectralTailCoefficient_le_majorant
    {p m : ℕ} (hp : 0 < p) {w : ℂ}
    (hmw : (3 / 2 : ℝ) ≤
      (m : ℝ) * (mobiusThetaCenteredParameter w).re) (j : ℕ) :
    ‖mobiusThetaPrimeNormalSpectralTailCoefficient p m w j‖ ≤
      mobiusThetaPrimeNormalSpectralTailMajorant p j := by
  rw [norm_mobiusThetaPrimeNormalSpectralTailCoefficient hp]
  have hmu : |(μ (p + j + 1) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p + j + 1)
  have hratioPos : 0 < (p : ℝ) / (p + j + 1 : ℕ) := by positivity
  have hratioLe : (p : ℝ) / (p + j + 1 : ℕ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast (by omega : p ≤ p + j + 1)
  unfold mobiusThetaPrimeNormalSpectralTailMajorant
  calc
    |(μ (p + j + 1) : ℝ)| *
          ((p : ℝ) / (p + j + 1 : ℕ)) ^
            ((m : ℝ) * (mobiusThetaCenteredParameter w).re) ≤
        1 * ((p : ℝ) / (p + j + 1 : ℕ)) ^
            ((m : ℝ) * (mobiusThetaCenteredParameter w).re) := by
      gcongr
    _ ≤ ((p : ℝ) / (p + j + 1 : ℕ)) ^ (3 / 2 : ℝ) := by
      simpa only [one_mul] using
        Real.rpow_le_rpow_of_exponent_ge hratioPos hratioLe hmw

/-- Each strict arithmetic channel vanishes at every fixed centered parameter in the right
half-plane. -/
theorem tendsto_mobiusThetaPrimeNormalSpectralTailCoefficient_zero
    {p : ℕ} (hp : 0 < p) {w : ℂ}
    (hw : 0 < (mobiusThetaCenteredParameter w).re) (j : ℕ) :
    Tendsto
      (fun m : ℕ => mobiusThetaPrimeNormalSpectralTailCoefficient p m w j)
      atTop (nhds 0) := by
  have hratioPos : 0 < (p : ℝ) / (p + j + 1 : ℕ) := by positivity
  have hratioLt : (p : ℝ) / (p + j + 1 : ℕ) < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast (by omega : p < p + j + 1)
  have hpow : Tendsto
      (fun m : ℕ => ((p : ℝ) / (p + j + 1 : ℕ)) ^
        ((m : ℝ) * (mobiusThetaCenteredParameter w).re))
      atTop (nhds 0) := by
    have hb := tendsto_rpow_atTop_of_base_lt_one
      ((p : ℝ) / (p + j + 1 : ℕ)) (by linarith) hratioLt
    exact hb.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hw)
  have hnorm : Tendsto
      (fun m : ℕ => |(μ (p + j + 1) : ℝ)| *
        ((p : ℝ) / (p + j + 1 : ℕ)) ^
          ((m : ℝ) * (mobiusThetaCenteredParameter w).re))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hpow
  rw [tendsto_zero_iff_norm_tendsto_zero]
  convert hnorm using 1
  funext m
  exact norm_mobiusThetaPrimeNormalSpectralTailCoefficient hp m w j

/-- Full strict tail vanishes by a complex-valued Tannery theorem. -/
theorem tendsto_tsum_mobiusThetaPrimeNormalSpectralTailCoefficient_zero
    {p : ℕ} (hp : 0 < p) {w : ℂ}
    (hw : 0 < (mobiusThetaCenteredParameter w).re) :
    Tendsto
      (fun m : ℕ =>
        ∑' j : ℕ, mobiusThetaPrimeNormalSpectralTailCoefficient p m w j)
      atTop (nhds 0) := by
  rw [show (0 : ℂ) = ∑' _j : ℕ, 0 by simp]
  apply tendsto_tsum_of_dominated_convergence
    (summable_mobiusThetaPrimeNormalSpectralTailMajorant p)
  · exact tendsto_mobiusThetaPrimeNormalSpectralTailCoefficient_zero hp hw
  · have hexp :=
      (tendsto_natCast_atTop_atTop.atTop_mul_const hw).eventually_ge_atTop
        (3 / 2 : ℝ)
    filter_upwards [hexp] with m hm j
    exact norm_mobiusThetaPrimeNormalSpectralTailCoefficient_le_majorant hp hm j

/-- Head-plus-tail form of the residual multiplier, suitable for prime isolation. -/
def mobiusThetaPrimeNormalAsymptoticMultiplier
    (p m : ℕ) (w : ℂ) : ℂ :=
  ((μ p : ℤ) : ℂ) +
    ∑' j : ℕ, mobiusThetaPrimeNormalSpectralTailCoefficient p m w j

theorem tendsto_mobiusThetaPrimeNormalAsymptoticMultiplier
    {p : ℕ} (hp : 0 < p) {w : ℂ}
    (hw : 0 < (mobiusThetaCenteredParameter w).re) :
    Tendsto (mobiusThetaPrimeNormalAsymptoticMultiplier p · w) atTop
      (nhds ((μ p : ℤ) : ℂ)) := by
  unfold mobiusThetaPrimeNormalAsymptoticMultiplier
  simpa using tendsto_const_nhds.add
    (tendsto_tsum_mobiusThetaPrimeNormalSpectralTailCoefficient_zero hp hw)

/-- On the honest Möbius half-plane, complete residual and head-plus-tail multipliers agree. -/
theorem mobiusThetaPrimeNormalResidualMultiplier_eq_asymptoticMultiplier
    {p m : ℕ} (hp : 0 < p) (hm : m ≠ 0) {w : ℂ}
    (hms : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) :
    mobiusThetaPrimeNormalResidualMultiplier p m w =
      mobiusThetaPrimeNormalAsymptoticMultiplier p m w := by
  have hsNorm :=
    summable_norm_mobiusThetaPrimeNormalResidualSpectralCoefficient
      (p := p) hm hms
  have hs : Summable
      (mobiusThetaPrimeNormalResidualSpectralCoefficient p m w) :=
    Summable.of_norm hsNorm
  have hsplit := hs.sum_add_tsum_nat_add 1
  rw [mobiusThetaPrimeNormalResidualMultiplier,
    mobiusThetaPrimeNormalAsymptoticMultiplier]
  calc
    (∑' j : ℕ, mobiusThetaPrimeNormalResidualSpectralCoefficient p m w j) =
        ∑ i ∈ Finset.range 1,
            mobiusThetaPrimeNormalResidualSpectralCoefficient p m w i +
          ∑' j : ℕ,
            mobiusThetaPrimeNormalResidualSpectralCoefficient p m w (j + 1) :=
      hsplit.symm
    _ = ((μ p : ℤ) : ℂ) +
          ∑' j : ℕ, mobiusThetaPrimeNormalSpectralTailCoefficient p m w j := by
      rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        mobiusThetaPrimeNormalResidualSpectralCoefficient_zero hp]
      congr 1

/-- Honest Möbius convergence domain is eventually reached at every fixed right-half-plane
centered parameter. -/
theorem eventually_mobiusThetaPrimeNormalResidual_convergenceDomain
    {w : ℂ} (hw : 0 < (mobiusThetaCenteredParameter w).re) :
    ∀ᶠ m : ℕ in atTop,
      m ≠ 0 ∧ 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt
    (1 / (mobiusThetaCenteredParameter w).re)
  filter_upwards [eventually_ge_atTop (max 1 N)] with m hm
  have hm1 : 1 ≤ m := le_trans (Nat.le_max_left 1 N) hm
  have hNm : N ≤ m := le_trans (Nat.le_max_right 1 N) hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm1)
  have hcast : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hNm
  have hlarge : 1 / (mobiusThetaCenteredParameter w).re < (m : ℝ) :=
    lt_of_lt_of_le hN hcast
  have hone : 1 < (m : ℝ) * (mobiusThetaCenteredParameter w).re :=
    (div_lt_iff₀ hw).mp hlarge
  exact ⟨by omega,
    (div_lt_iff₀ hmpos).mpr (by simpa [mul_comm] using hone)⟩

/-- **Source-derived prime isolation.**  The exact full residual multiplier converges to its
retained Möbius coefficient throughout the right half-plane. -/
theorem tendsto_mobiusThetaPrimeNormalResidualMultiplier
    {p : ℕ} (hp : 0 < p) {w : ℂ}
    (hw : 0 < (mobiusThetaCenteredParameter w).re) :
    Tendsto (mobiusThetaPrimeNormalResidualMultiplier p · w) atTop
      (nhds ((μ p : ℤ) : ℂ)) := by
  have hasym := tendsto_mobiusThetaPrimeNormalAsymptoticMultiplier hp hw
  have heq :
      (mobiusThetaPrimeNormalAsymptoticMultiplier p · w) =ᶠ[atTop]
        (mobiusThetaPrimeNormalResidualMultiplier p · w) := by
    filter_upwards [eventually_mobiusThetaPrimeNormalResidual_convergenceDomain hw]
      with m hm
    exact (mobiusThetaPrimeNormalResidualMultiplier_eq_asymptoticMultiplier
      hp hm.1 hm.2).symm
  exact hasym.congr' heq

/-- Prime residual multiplier is eventually nonzero; no scalar nonannihilation hypothesis is
required. -/
theorem eventually_mobiusThetaPrimeNormalResidualMultiplier_ne_zero_of_prime
    {p : ℕ} (hp : p.Prime) {w : ℂ}
    (hw : 0 < (mobiusThetaCenteredParameter w).re) :
    ∀ᶠ m : ℕ in atTop,
      mobiusThetaPrimeNormalResidualMultiplier p m w ≠ 0 := by
  have hmu : ((μ p : ℤ) : ℂ) ≠ 0 := by
    rw [ArithmeticFunction.moebius_apply_prime hp]
    norm_num
  exact (tendsto_mobiusThetaPrimeNormalResidualMultiplier hp.pos hw).eventually_ne hmu

/-- Division-free conormal pair of the complete prime-normal residual source. -/
def mobiusThetaInternalJetPrimeNormalResidualConormalPair
    (k p m : ℕ) (w : ℂ) : ℂ × ℂ :=
  (mobiusThetaInternalJetPrimeNormalResidualFourierLaplace k p m w,
    mobiusThetaInternalJetPrimeNormalResidualFourierLaplace (k + 1) p m w)

/-- **Complete residual multiplicity retention.**  At every Xi divisor, the full target-free
prime-normal residual eventually gives a nonzero vertical conormal.  Nonannihilation follows from
prime isolation rather than from an assumed scalar coefficient. -/
theorem eventually_mobiusThetaInternalJetPrimeNormalResidualConormalPair_at_divisor
    {p : ℕ} (hp : p.Prime) (rho : XiDivisorSupport) :
    ∀ᶠ m : ℕ in atTop,
      mobiusThetaInternalJetPrimeNormalResidualConormalPair
          (xiSupportMultiplicity rho - 1) p m
          (xiSpectralPointSupport rho) =
        (0, mobiusThetaPrimeNormalResidualMultiplier p m
          (xiSpectralPointSupport rho) *
            iteratedDeriv (xiSupportMultiplicity rho) XiC
              (xiSpectralPointSupport rho)) ∧
      mobiusThetaPrimeNormalResidualMultiplier p m
          (xiSpectralPointSupport rho) *
            iteratedDeriv (xiSupportMultiplicity rho) XiC
              (xiSpectralPointSupport rho) ≠ 0 := by
  have hcenter : mobiusThetaCenteredParameter
      (xiSpectralPointSupport rho) = (rho : ℂ) :=
    mobiusThetaCenteredParameter_xiSpectralPointSupport rho
  have hre : 0 < (mobiusThetaCenteredParameter
      (xiSpectralPointSupport rho)).re := by
    rw [hcenter]
    exact (xi_divisor_support_re_mem_open_unit rho).1
  have hdomain :=
    eventually_mobiusThetaPrimeNormalResidual_convergenceDomain hre
  have hmult :=
    eventually_mobiusThetaPrimeNormalResidualMultiplier_ne_zero_of_prime hp hre
  filter_upwards [hdomain, hmult] with m hm hmultne
  have hrpos : 0 < xiSupportMultiplicity rho :=
    xiSupportMultiplicity_pos rho
  have hrpred : xiSupportMultiplicity rho - 1 < xiSupportMultiplicity rho :=
    Nat.sub_lt hrpos (by omega)
  have hzero :=
    iteratedDeriv_XiC_eq_zero_before_supportMultiplicity rho hrpred
  have hsucc : xiSupportMultiplicity rho - 1 + 1 =
      xiSupportMultiplicity rho := by omega
  have hfirst :=
    mobiusThetaInternalJetPrimeNormalResidualFourierLaplace_eq hp.pos
      (xiSupportMultiplicity rho - 1) hm.1
      (abs_im_xiSpectralPointSupport_lt_one rho) hm.2
  have hsecond :=
    mobiusThetaInternalJetPrimeNormalResidualFourierLaplace_eq hp.pos
      (xiSupportMultiplicity rho) hm.1
      (abs_im_xiSpectralPointSupport_lt_one rho) hm.2
  constructor
  · rw [mobiusThetaInternalJetPrimeNormalResidualConormalPair,
      hfirst, hsucc, hsecond, hzero, mul_zero]
  · exact mul_ne_zero hmultne
      (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)

end RHTower
