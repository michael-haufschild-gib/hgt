import GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMECrossBranchTeukolskyResidue
import GaloisForLFunctions.RHTower.ScrewCurvatureSumOfSquares

/-!
# Quadratic cusp-weight endpoint for the chiral Teukolsky return

Birmingham--Mokhtari's exact `d = 4` gravitational hypergeometric reduction uses the
self-adjoint horizon-Laplacian eigenvalue

`Q = 1/4 + xi^(2 : ℕ)`.

The theta-cusp continuation used in the preceding black-hole modules has

`rho = 1/2 + I*z`, `xi_cusp = I*(1-rho)/2 = z/2 + I/4`.

This module first records a necessary correction.  At every actual Xi divisor, `0 < re rho < 1`
and `re z != 0`.  Consequently `im xi_cusp > 0` and the continued eigenvalue `Q` has nonzero
imaginary part.  Thus the existing cusp channel is never a physical eigenchannel of the
self-adjoint horizon operator, even if RH is assumed.  It is an analytic resonance continuation.

The modular scattering pole has Eisenstein weight

`s(z) = 1/4 + I*z/2 = rho/2`.

A local holomorphic quadratic gravitational source has principal cusp weight `2*s = rho`.
Re-centering this doubled weight on the Birmingham--Mokhtari principal-series line gives momentum

`-I*(2*s - 1/2) = z`.

Equivalently, the full complex separation of the exact QNM branches is

`omega_+ - omega_- = 2*xi_cusp = z + I/2`.

The same re-centering subtracts `I/2` from this raw gap and produces the candidate physical
eigenvalue

`Q_H = 1/4 + z^(2 : ℕ)`.

For an Xi divisor, `re z != 0`, so

`im Q_H = 2*(re z)*(im z)`

vanishes exactly on the critical line.  Global reality of this de-aliased angular spectrum is
therefore equivalent to RH.

**[FALSIFIED]** Directly identifying the old theta-cusp `Q` with Birmingham--Mokhtari's physical
horizon eigenvalue.

**[PAPER-PROVED] [LEAN-PROVED]** Nonphysicality of the raw continued `Q`, quadratic cusp-weight
doubling and re-centering, pointwise reality criterion, and global RH equivalence.

**[OPEN CORE]** Prove that the reduced second-order chiral Teukolsky source has a nonzero `2*s`
principal coefficient.  A tilted divisor must then either leave the self-adjoint angular spectrum
or mix with other angular sectors.  Generic KMS, passivity, CCR, scalar optical energy, and the
existing analytically continued Jost formulas do not establish this source incidence.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Eisenstein weight of the linear theta-cusp scattering pole. -/
def d4ThetaTeukolskyLinearCuspWeight (z : ℂ) : ℂ :=
  thetaCuspHawkingOpticalCuspResonanceParameter z

/-- Principal cusp weight of a holomorphic quadratic return source. -/
def d4ThetaTeukolskyQuadraticChiralCuspWeight (z : ℂ) : ℂ :=
  2 * d4ThetaTeukolskyLinearCuspWeight z

/-- Birmingham--Mokhtari momentum centered at the unitary Eisenstein line. -/
def d4ThetaTeukolskyMomentumOfCuspWeight (s : ℂ) : ℂ :=
  -Complex.I * (s - 1 / 2)

/-- Momentum carried by the doubled chiral cusp weight. -/
def d4ThetaTeukolskyQuadraticChiralAngularMomentum (z : ℂ) : ℂ :=
  d4ThetaTeukolskyMomentumOfCuspWeight
    (d4ThetaTeukolskyQuadraticChiralCuspWeight z)

/-- Self-adjoint angular Casimir candidate of the doubled chiral cusp weight. -/
def d4ThetaTeukolskyQuadraticChiralAngularEigenvalue (z : ℂ) : ℂ :=
  d4ThetaTeukolskyQuadraticChiralCuspWeight z *
    (1 - d4ThetaTeukolskyQuadraticChiralCuspWeight z)

/-- Every divisor-indexed quadratic principal return lies on the unitary Eisenstein line. -/
def D4ThetaTeukolskyQuadraticChiralPrincipalReturnIsUnitary : Prop :=
  ∀ q : XiZeroCopy,
    (d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q)).re = 1 / 2

lemma d4ThetaTeukolskyLinearCuspWeight_eq_half_rho (z : ℂ) :
    d4ThetaTeukolskyLinearCuspWeight z = d4ThetaTeukolskyRho z / 2 := by
  unfold d4ThetaTeukolskyLinearCuspWeight
    thetaCuspHawkingOpticalCuspResonanceParameter d4ThetaTeukolskyRho
  ring

/-- Quadratic cusp-weight addition sends the modular pole parameter `rho/2` to `rho`. -/
theorem d4ThetaTeukolskyQuadraticChiralCuspWeight_eq_rho (z : ℂ) :
    d4ThetaTeukolskyQuadraticChiralCuspWeight z = d4ThetaTeukolskyRho z := by
  rw [d4ThetaTeukolskyQuadraticChiralCuspWeight,
    d4ThetaTeukolskyLinearCuspWeight_eq_half_rho]
  ring

lemma d4ThetaTeukolskyMomentumOfLinearCuspWeight_eq (z : ℂ) :
    d4ThetaTeukolskyMomentumOfCuspWeight
        (d4ThetaTeukolskyLinearCuspWeight z) =
      thetaCuspHawkingTopologicalBlackHoleAngularMomentum z := by
  unfold d4ThetaTeukolskyMomentumOfCuspWeight
    d4ThetaTeukolskyLinearCuspWeight
    thetaCuspHawkingOpticalCuspResonanceParameter
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Re-centering the doubled cusp weight gives the centered Xi momentum. -/
theorem d4ThetaTeukolskyQuadraticChiralAngularMomentum_eq (z : ℂ) :
    d4ThetaTeukolskyQuadraticChiralAngularMomentum z = z := by
  unfold d4ThetaTeukolskyQuadraticChiralAngularMomentum
    d4ThetaTeukolskyMomentumOfCuspWeight
  rw [d4ThetaTeukolskyQuadraticChiralCuspWeight_eq_rho]
  unfold d4ThetaTeukolskyRho
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The apparent half-shift is exactly the Weyl re-centering correction after weight doubling. -/
theorem d4ThetaTeukolskyQuadraticChiralAngularMomentum_eq_raw_sub_half
    (z : ℂ) :
    d4ThetaTeukolskyQuadraticChiralAngularMomentum z =
      2 * thetaCuspHawkingTopologicalBlackHoleAngularMomentum z - Complex.I / 2 := by
  rw [d4ThetaTeukolskyQuadraticChiralAngularMomentum_eq]
  unfold thetaCuspHawkingTopologicalBlackHoleAngularMomentum
  ring

/-- Doubled cusp Casimir is the de-aliased Birmingham--Mokhtari angular eigenvalue. -/
theorem d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_eq (z : ℂ) :
    d4ThetaTeukolskyQuadraticChiralAngularEigenvalue z = 1 / 4 + z ^ 2 := by
  unfold d4ThetaTeukolskyQuadraticChiralAngularEigenvalue
  rw [d4ThetaTeukolskyQuadraticChiralCuspWeight_eq_rho]
  unfold d4ThetaTeukolskyRho
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Doubled chiral weight is unitary exactly when the centered Xi momentum is real. -/
theorem d4ThetaTeukolskyQuadraticChiralCuspWeight_re_eq_half_iff (z : ℂ) :
    (d4ThetaTeukolskyQuadraticChiralCuspWeight z).re = 1 / 2 ↔ z.im = 0 := by
  rw [d4ThetaTeukolskyQuadraticChiralCuspWeight_eq_rho]
  simp [d4ThetaTeukolskyRho]

/-- Weyl-centered momentum of the doubled cusp weight, retained under its original API name. -/
def d4ThetaTeukolskyThermallyDealiasedAngularMomentum (z : ℂ) : ℂ :=
  2 * thetaCuspHawkingTopologicalBlackHoleAngularMomentum z - Complex.I / 2

/-- Candidate physical `d = 4` horizon-Laplacian eigenvalue after quadratic re-centering. -/
def d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue (z : ℂ) : ℂ :=
  1 / 4 + d4ThetaTeukolskyThermallyDealiasedAngularMomentum z ^ 2

/-- Exact QNM-branch return gap after subtracting the Hawking imaginary half-unit. -/
def d4ThetaTeukolskyThermallyDealiasedQNMBranchGap (n : ℕ) (z : ℂ) : ℂ :=
  thetaCuspHawkingTopologicalBlackHoleQNMPlus n z -
    thetaCuspHawkingTopologicalBlackHoleQNMMinus n z - Complex.I / 2

/-- Reality of every divisor-indexed de-aliased angular eigenvalue. -/
def D4ThetaTeukolskyThermallyDealiasedSpectrumIsReal : Prop :=
  ∀ q : XiZeroCopy,
    (d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue
      (xiSpectralPoint q)).im = 0

/-- Quadratic re-centering recovers the centered Xi spectral coordinate exactly. -/
lemma d4ThetaTeukolskyThermallyDealiasedAngularMomentum_eq (z : ℂ) :
    d4ThetaTeukolskyThermallyDealiasedAngularMomentum z = z := by
  unfold d4ThetaTeukolskyThermallyDealiasedAngularMomentum
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum
  ring

/-- Radial decay and overtone cancel from the full complex branch gap; the Hawking subtraction
leaves exactly `z`. -/
theorem d4ThetaTeukolskyThermallyDealiasedQNMBranchGap_eq
    (n : ℕ) (z : ℂ) :
    d4ThetaTeukolskyThermallyDealiasedQNMBranchGap n z = z := by
  unfold d4ThetaTeukolskyThermallyDealiasedQNMBranchGap
    thetaCuspHawkingTopologicalBlackHoleQNMPlus
    thetaCuspHawkingTopologicalBlackHoleQNMMinus
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum
  ring

/-- De-aliased angular eigenvalue has the physical Birmingham--Mokhtari form with momentum `z`. -/
lemma d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_eq (z : ℂ) :
    d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue z = 1 / 4 + z ^ 2 := by
  rw [d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue,
    d4ThetaTeukolskyThermallyDealiasedAngularMomentum_eq]

/-- Exact positive imaginary part of the old continued square-root momentum at an Xi divisor. -/
lemma thetaCuspHawkingBMContinuedAngularMomentum_xi_im (q : XiZeroCopy) :
    (thetaCuspHawkingTopologicalBlackHoleAngularMomentum
      (xiSpectralPoint q)).im = (1 - (q.1 : ℂ).re) / 2 := by
  rw [d4ThetaTeukolskyAngularMomentum_eq_rho,
    d4ThetaTeukolskyRho_xiSpectralPoint]
  simp [Complex.mul_im]

/-- The old cusp square-root momentum is nonreal at every Xi divisor, independently of RH. -/
theorem thetaCuspHawkingBMContinuedAngularMomentum_xi_im_pos (q : XiZeroCopy) :
    0 < (thetaCuspHawkingTopologicalBlackHoleAngularMomentum
      (xiSpectralPoint q)).im := by
  rw [thetaCuspHawkingBMContinuedAngularMomentum_xi_im]
  linarith [(xi_divisor_support_re_mem_open_unit q.1).2]

/-- Imaginary part of the raw analytically continued angular eigenvalue. -/
lemma thetaCuspHawkingBMContinuedAngularEigenvalue_im (z : ℂ) :
    (thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue z).im =
      z.re * (z.im / 2 + 1 / 4) := by
  unfold thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum
  simp [pow_two, Complex.mul_im]
  ring

/-- **Raw-channel no-go.**  At every Xi divisor the old continued `Q` is nonreal, so it cannot be
an eigenvalue of the physical self-adjoint horizon Laplacian. -/
theorem thetaCuspHawkingBMContinuedAngularEigenvalue_xi_im_ne_zero
    (q : XiZeroCopy) :
    (thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue
      (xiSpectralPoint q)).im ≠ 0 := by
  rw [thetaCuspHawkingBMContinuedAngularEigenvalue_im]
  apply mul_ne_zero
  · exact thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q
  · have hpos := thetaCuspHawkingBMContinuedAngularMomentum_xi_im_pos q
    simp [thetaCuspHawkingTopologicalBlackHoleAngularMomentum] at hpos
    have hfactor : 0 < (xiSpectralPoint q).im / 2 + 1 / 4 := by
      norm_num at hpos ⊢
      exact hpos
    exact ne_of_gt hfactor

/-- De-aliased angular reality detects exactly the product of height and Xi tilt. -/
lemma d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_im (z : ℂ) :
    (d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue z).im =
      2 * z.re * z.im := by
  rw [d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_eq]
  simp [pow_two, Complex.mul_im]
  ring

/-- At a divisor, de-aliased angular reality is exactly membership in the critical line. -/
theorem d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_xi_im_eq_zero_iff
    (q : XiZeroCopy) :
    (d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue
      (xiSpectralPoint q)).im = 0 ↔
      (xiSpectralPoint q).im = 0 := by
  rw [d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_im]
  constructor
  · intro h
    have hmul : (xiSpectralPoint q).re * (xiSpectralPoint q).im = 0 := by
      linarith
    exact (mul_eq_zero.mp hmul).resolve_left
      (thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q)
  · intro h
    rw [h]
    ring

/-- On the critical line the candidate eigenvalue lies strictly above the `d = 4` hyperbolic
threshold `1/4`; Xi ordinates never vanish. -/
theorem d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_xi_re_gt_quarter
    (q : XiZeroCopy) (h : (xiSpectralPoint q).im = 0) :
    1 / 4 <
      (d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue
        (xiSpectralPoint q)).re := by
  rw [d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_eq]
  simp [pow_two, Complex.mul_re, h]
  exact thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q

/-- **Quadratic re-centering endpoint.**  If nonlinear chiral Teukolsky return lands in the
physical real angular spectrum, its all-divisor statement is exactly RH. -/
theorem riemannHypothesis_iff_d4ThetaTeukolskyThermallyDealiasedSpectrumIsReal :
    RiemannHypothesis ↔ D4ThetaTeukolskyThermallyDealiasedSpectrumIsReal := by
  constructor
  · intro hRH q
    exact
      (d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_xi_im_eq_zero_iff q).2
        (xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH q)
  · intro hQ
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    refine ⟨(xiSpectralPoint q).re, ?_⟩
    apply Complex.ext
    · simp
    · simp [
        (d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_xi_im_eq_zero_iff q).1
          (hQ q)]

/-- **Quadratic chiral cusp endpoint.**  If the nonzero principal component of the second-order
Teukolsky return has doubled cusp weight, requiring that component to lie on the self-adjoint
principal-series line for every divisor is equivalent to RH. -/
theorem riemannHypothesis_iff_d4ThetaTeukolskyQuadraticChiralPrincipalReturnIsUnitary :
    RiemannHypothesis ↔ D4ThetaTeukolskyQuadraticChiralPrincipalReturnIsUnitary := by
  constructor
  · intro hRH q
    exact (d4ThetaTeukolskyQuadraticChiralCuspWeight_re_eq_half_iff
      (xiSpectralPoint q)).2
      (xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH q)
  · intro hreturn
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    refine ⟨(xiSpectralPoint q).re, ?_⟩
    apply Complex.ext
    · simp
    · simp [(d4ThetaTeukolskyQuadraticChiralCuspWeight_re_eq_half_iff
        (xiSpectralPoint q)).1 (hreturn q)]

end

end RHTower
