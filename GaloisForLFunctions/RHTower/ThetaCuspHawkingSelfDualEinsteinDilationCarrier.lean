import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskyTiltedAngularLeakage
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Hawking dilation carrier in self-dual Einstein--AdS4

The massless four-dimensional topological black hole is locally `AdS4`. In the Plebanski
self-dual sector, the exact Einstein--Lambda plane-wave vertex is a double copy of the
kinematic bracket. For affine horizon momenta `p,q` and common cusp charge `h`, its curvature
correction vanishes and the vertex reduces to

`V(p,q;h) = (1/2) h^2 (p-q)^2`.

The diagonal plane-wave vertex is zero. An ingoing Hawking dilation mode is instead a Mellin
continuum of affine momenta. If its Mellin exponent is `a`, pair convolution gives the exact
variance moment

`4 B(a+2,a) - 4 B(a+1,a) + B(a,a) = B(a,a)/(2a+1)`.

After Gamma normalization, the source coefficient is `a h^2`. Birmingham--Mokhtari's exact
fundamental ingoing exponent satisfies `a = -2 alpha = 1 + rho/2`; theta cusp charge is
`h = rho/2`. Hence a seed of amplitude `A` produces coefficient

`A^2 (1+rho/2) (rho/2)^2`,

which is nonzero at every Xi divisor. Its angular weight is `2h=rho`; every tilted divisor
therefore has nonzero residual against a symmetric Birmingham--Mokhtari angular operator.

Statements concern exact self-dual Einstein cusp-horizon principal germ. Full non-self-dual
second-order Teukolsky projection and global Evans incidence are separate equations.
-/

open Complex Real Set
open scoped InnerProductSpace

namespace RHTower

noncomputable section

def ads4SelfDualKinematicBracket (p h q k : ℂ) : ℂ :=
  p * k - h * q

def ads4SelfDualPlaneWaveVertex
    (curvature p h q k : ℂ) : ℂ :=
  (1 / 2 : ℂ) * ads4SelfDualKinematicBracket p h q k *
    (ads4SelfDualKinematicBracket p h q k - curvature * (h - k))

theorem ads4SelfDualPlaneWaveVertex_diagonal
    (curvature p h : ℂ) :
    ads4SelfDualPlaneWaveVertex curvature p h p h = 0 := by
  unfold ads4SelfDualPlaneWaveVertex ads4SelfDualKinematicBracket
  ring

theorem ads4SelfDualPlaneWaveVertex_sameTransverseCharge
    (curvature p q h : ℂ) :
    ads4SelfDualPlaneWaveVertex curvature p h q h =
      (1 / 2 : ℂ) * h ^ 2 * (p - q) ^ 2 := by
  unfold ads4SelfDualPlaneWaveVertex ads4SelfDualKinematicBracket
  ring

def d4ThetaHawkingSelfDualDilationExponent (z : ℂ) : ℂ :=
  1 + d4ThetaTeukolskyLinearCuspWeight z

theorem d4ThetaHawkingSelfDualDilationExponent_eq (z : ℂ) :
    d4ThetaHawkingSelfDualDilationExponent z =
      1 + d4ThetaTeukolskyRho z / 2 := by
  rw [d4ThetaHawkingSelfDualDilationExponent,
    d4ThetaTeukolskyLinearCuspWeight_eq_half_rho]

theorem d4ThetaHawkingSelfDualDilationExponent_eq_bmIngoing (z : ℂ) :
    d4ThetaHawkingSelfDualDilationExponent z =
      -2 * d4FundamentalQNMIngoingExponent z := by
  rw [d4ThetaHawkingSelfDualDilationExponent_eq]
  unfold d4FundamentalQNMIngoingExponent
  ring

def ads4SelfDualMellinVarianceMoment (a : ℂ) : ℂ :=
  Complex.betaIntegral a a / (2 * a + 1)

lemma complexGamma_ne_zero_of_re_pos {a : ℂ} (ha : 0 < a.re) :
    Complex.Gamma a ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m hm
  have hre := congrArg Complex.re hm
  simp at hre
  linarith

lemma betaIntegral_self_ne_zero_of_re_pos {a : ℂ} (ha : 0 < a.re) :
    Complex.betaIntegral a a ≠ 0 := by
  have hgamma : Complex.Gamma a ≠ 0 := complexGamma_ne_zero_of_re_pos ha
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral ha ha
  intro hzero
  rw [hzero, mul_zero] at hbeta
  exact mul_ne_zero hgamma hgamma hbeta

theorem ads4SelfDualMellinVarianceMoment_ne_zero
    {a : ℂ} (ha : 0 < a.re) :
    ads4SelfDualMellinVarianceMoment a ≠ 0 := by
  unfold ads4SelfDualMellinVarianceMoment
  apply div_ne_zero (betaIntegral_self_ne_zero_of_re_pos ha)
  intro hzero
  have hre := congrArg Complex.re hzero
  simp at hre
  linarith

lemma betaIntegral_add_one_left
    {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Complex.betaIntegral (a + 1) b =
      a / (a + b) * Complex.betaIntegral a b := by
  have habRe : 0 < (a + b).re := by
    simp only [Complex.add_re]
    linarith
  have ha0 : a ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hab0 : a + b ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hGab : Complex.Gamma (a + b) ≠ 0 :=
    complexGamma_ne_zero_of_re_pos habRe
  have h0 := Complex.Gamma_mul_Gamma_eq_betaIntegral ha hb
  have ha1 : 0 < (a + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have h1 := Complex.Gamma_mul_Gamma_eq_betaIntegral ha1 hb
  rw [Complex.Gamma_add_one a ha0,
    show a + 1 + b = (a + b) + 1 by ring,
    Complex.Gamma_add_one (a + b) hab0] at h1
  have hrel : a * Complex.betaIntegral a b =
      (a + b) * Complex.betaIntegral (a + 1) b := by
    apply mul_left_cancel₀ hGab
    calc
      Complex.Gamma (a + b) *
          (a * Complex.betaIntegral a b) =
          a * (Complex.Gamma (a + b) *
            Complex.betaIntegral a b) := by ring
      _ = a * (Complex.Gamma a * Complex.Gamma b) := by rw [← h0]
      _ = Complex.Gamma (a + b) *
          ((a + b) * Complex.betaIntegral (a + 1) b) := by
            rw [show a * (Complex.Gamma a * Complex.Gamma b) =
              (a * Complex.Gamma a) * Complex.Gamma b by ring, h1]
            ring
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hab0).2
  simpa [mul_comm] using hrel.symm

def ads4SelfDualMellinPolynomialMoment (a : ℂ) : ℂ :=
  4 * Complex.betaIntegral (a + 2) a -
    4 * Complex.betaIntegral (a + 1) a +
      Complex.betaIntegral a a

theorem ads4SelfDualMellinPolynomialMoment_eq
    {a : ℂ} (ha : 0 < a.re) :
    ads4SelfDualMellinPolynomialMoment a =
      ads4SelfDualMellinVarianceMoment a := by
  have ha1 : 0 < (a + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hshift2 := betaIntegral_add_one_left (a := a + 1) (b := a) ha1 ha
  rw [ads4SelfDualMellinPolynomialMoment,
    show a + 2 = (a + 1) + 1 by ring,
    hshift2,
    betaIntegral_add_one_left ha ha,
    ads4SelfDualMellinVarianceMoment]
  have ha2 : a + a ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have htwoplus : 2 * a + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have ha0 : a ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  rw [show a + a = 2 * a by ring,
    show a + 1 + a = 2 * a + 1 by ring]
  have hhalf : a / (2 * a) = (1 / 2 : ℂ) := by
    field_simp [ha0]
  rw [hhalf]
  have htwoplus' : 1 + a * 2 ≠ 0 := by
    intro hzero
    apply htwoplus
    linear_combination hzero
  rw [show 2 * a + 1 = 1 + a * 2 by ring]
  field_simp [htwoplus']
  ring

theorem ads4SelfDualMellinPolynomialMoment_ne_zero
    {a : ℂ} (ha : 0 < a.re) :
    ads4SelfDualMellinPolynomialMoment a ≠ 0 := by
  rw [ads4SelfDualMellinPolynomialMoment_eq ha]
  exact ads4SelfDualMellinVarianceMoment_ne_zero ha

def ads4SelfDualNormalizedMellinSourceCoefficient (a h : ℂ) : ℂ :=
  (h ^ 2 / 2) * ads4SelfDualMellinPolynomialMoment a *
    Complex.Gamma (2 * a + 2) / Complex.Gamma a ^ 2

theorem ads4SelfDualNormalizedMellinSourceCoefficient_eq
    {a h : ℂ} (ha : 0 < a.re) :
    ads4SelfDualNormalizedMellinSourceCoefficient a h = a * h ^ 2 := by
  have ha0 : a ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  have htwoa0 : 2 * a ≠ 0 := mul_ne_zero (by norm_num) ha0
  have htwoaplus0 : 2 * a + 1 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  have hgamma : Complex.Gamma a ≠ 0 := complexGamma_ne_zero_of_re_pos ha
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral ha ha
  rw [ads4SelfDualNormalizedMellinSourceCoefficient,
    ads4SelfDualMellinPolynomialMoment_eq ha,
    ads4SelfDualMellinVarianceMoment,
    show 2 * a + 2 = (2 * a + 1) + 1 by ring,
    Complex.Gamma_add_one (2 * a + 1) htwoaplus0,
    Complex.Gamma_add_one (2 * a) htwoa0]
  field_simp [hgamma, htwoaplus0]
  rw [show Complex.Gamma a ^ 2 =
    Complex.Gamma a * Complex.Gamma a by ring, hbeta]
  ring

def d4ThetaHawkingSelfDualQuadraticCarrierCoefficient
    (amplitude z : ℂ) : ℂ :=
  amplitude ^ 2 * ads4SelfDualNormalizedMellinSourceCoefficient
    (d4ThetaHawkingSelfDualDilationExponent z)
    (d4ThetaTeukolskyLinearCuspWeight z)

def d4ThetaHawkingSelfDualQuadraticCarrierCuspWeight (z : ℂ) : ℂ :=
  2 * d4ThetaTeukolskyLinearCuspWeight z

theorem d4ThetaHawkingSelfDualQuadraticCarrierCuspWeight_eq_rho (z : ℂ) :
    d4ThetaHawkingSelfDualQuadraticCarrierCuspWeight z =
      d4ThetaTeukolskyRho z := by
  exact d4ThetaTeukolskyQuadraticChiralCuspWeight_eq_rho z

lemma d4ThetaTeukolskyLinearCuspWeight_xi_ne_zero (q : XiZeroCopy) :
    d4ThetaTeukolskyLinearCuspWeight (xiSpectralPoint q) ≠ 0 := by
  rw [d4ThetaTeukolskyLinearCuspWeight_eq_half_rho,
    d4ThetaTeukolskyRho_xiSpectralPoint]
  apply div_ne_zero
  · intro hzero
    have hre := congrArg Complex.re hzero
    have hstrip := xi_divisor_support_re_mem_open_unit q.1
    simp at hre
    linarith
  · norm_num

lemma d4ThetaHawkingSelfDualDilationExponent_xi_re_pos (q : XiZeroCopy) :
    0 < (d4ThetaHawkingSelfDualDilationExponent (xiSpectralPoint q)).re := by
  rw [d4ThetaHawkingSelfDualDilationExponent_eq,
    d4ThetaTeukolskyRho_xiSpectralPoint]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  simp
  linarith

theorem d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_ne_zero
    {amplitude : ℂ} (ha : amplitude ≠ 0) (q : XiZeroCopy) :
    d4ThetaHawkingSelfDualQuadraticCarrierCoefficient amplitude
      (xiSpectralPoint q) ≠ 0 := by
  unfold d4ThetaHawkingSelfDualQuadraticCarrierCoefficient
  rw [ads4SelfDualNormalizedMellinSourceCoefficient_eq
    (d4ThetaHawkingSelfDualDilationExponent_xi_re_pos q)]
  exact mul_ne_zero (pow_ne_zero 2 ha)
    (mul_ne_zero
      (by
        intro hzero
        have hre := congrArg Complex.re hzero
        have hpos := d4ThetaHawkingSelfDualDilationExponent_xi_re_pos q
        simp at hre
        linarith)
      (pow_ne_zero 2 (d4ThetaTeukolskyLinearCuspWeight_xi_ne_zero q)))

theorem d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_eq
    (amplitude : ℂ) (q : XiZeroCopy) :
    d4ThetaHawkingSelfDualQuadraticCarrierCoefficient amplitude
        (xiSpectralPoint q) =
      amplitude ^ 2 *
        (1 + (q.1 : ℂ) / 2) * ((q.1 : ℂ) / 2) ^ 2 := by
  rw [d4ThetaHawkingSelfDualQuadraticCarrierCoefficient,
    ads4SelfDualNormalizedMellinSourceCoefficient_eq
      (d4ThetaHawkingSelfDualDilationExponent_xi_re_pos q),
    d4ThetaHawkingSelfDualDilationExponent_eq,
    d4ThetaTeukolskyLinearCuspWeight_eq_half_rho,
    d4ThetaTeukolskyRho_xiSpectralPoint]
  ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def d4ThetaHawkingSelfDualQuadraticCarrierVector
    (amplitude : ℂ) (profile : H) (q : XiZeroCopy) : H :=
  d4ThetaHawkingSelfDualQuadraticCarrierCoefficient amplitude
      (xiSpectralPoint q) • profile

theorem d4ThetaHawkingSelfDualQuadraticCarrierVector_ne_zero
    {amplitude : ℂ} {profile : H} (q : XiZeroCopy)
    (ha : amplitude ≠ 0) (hprofile : profile ≠ 0) :
    d4ThetaHawkingSelfDualQuadraticCarrierVector amplitude profile q ≠ 0 := by
  unfold d4ThetaHawkingSelfDualQuadraticCarrierVector
  exact smul_ne_zero
    (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_ne_zero ha q)
    hprofile

theorem d4ThetaHawkingSelfDualQuadraticCarrier_tilted_forces_angularMixing
    (A : H → H) {amplitude : ℂ} {profile : H} (q : XiZeroCopy)
    (hsa :
      ⟪d4ThetaHawkingSelfDualQuadraticCarrierVector amplitude profile q,
        A (d4ThetaHawkingSelfDualQuadraticCarrierVector amplitude profile q)⟫_ℂ =
      ⟪A (d4ThetaHawkingSelfDualQuadraticCarrierVector amplitude profile q),
        d4ThetaHawkingSelfDualQuadraticCarrierVector amplitude profile q⟫_ℂ)
    (ha : amplitude ≠ 0) (hprofile : profile ≠ 0)
    (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    A (d4ThetaHawkingSelfDualQuadraticCarrierVector amplitude profile q) -
        d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue
          (xiSpectralPoint q) •
            d4ThetaHawkingSelfDualQuadraticCarrierVector amplitude profile q ≠ 0 := by
  apply d4ThetaTeukolsky_tiltedAngularSource_forces_leakage
    A (d4ThetaHawkingSelfDualQuadraticCarrierVector amplitude profile q) q hsa
    (d4ThetaHawkingSelfDualQuadraticCarrierVector_ne_zero q ha hprofile)
  intro hzero
  apply htilt
  have hre := congrArg Complex.re
    (show d4ThetaTeukolskyRho (xiSpectralPoint q) = (q.1 : ℂ) from
      d4ThetaTeukolskyRho_xiSpectralPoint q)
  simp [d4ThetaTeukolskyRho, hzero] at hre
  simpa using hre.symm

end

end RHTower

