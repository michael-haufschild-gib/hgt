import GaloisForLFunctions.RHTower.ThetaCuspHawkingTiltedMirrorOpticalTheoremEndpoint
import GaloisForLFunctions.RHTower.XiHurwitzOrientationPositivePairedSource
import GaloisForLFunctions.RHTower.DeningerArithmeticResidueDuality
import GaloisForLFunctions.RHTower.HardyCarrier

/-!
# Schwarzschild Jost incidence: theta divisor points are source zeros, not QNM poles

`[LITERATURE] [PAPER-PROVED]` For spin `s` on Schwarzschild, the separated
Regge--Wheeler equation is

`(d²/dr_*² + omega² - V_{ell,s}) psi = 0`.

Let `f` be horizon-ingoing and `g` infinity-outgoing.  The retarded radial Green function is

`G(r,r'; omega) = f(r_<,omega) g(r_>,omega) / W(omega)`

and its Evans/Jost denominator is the Wronskian

`W(omega) = -2 i omega A_in(omega)`.

These are Eqs. (2.1)--(2.4) of Casals--Ottewill, arXiv:1112.2695.  The same source/denominator
separation for the Teukolsky initial-value problem is Eqs. (64)--(69) of
Green--Hollands--Sberna--Toomani--Zimmerman, arXiv:2210.15935: initial data enters the numerator,
while QNM poles occur where the homogeneous Wronskian vanishes.

For real nonzero frequency, conservation of the Klein--Gordon/Regge--Wheeler current gives

`|A_in|² - |A_out|² = 1`.

Hence `A_in` and `W` cannot vanish on the physical real axis.  Up to irrelevant phases, write
`|A_in| = cosh eta`, `|A_out| = sinh eta`.  This file formalizes that exact flux-normalized
real-axis Jost normal form.

`[THETA INCIDENCE]` A centered Xi divisor coordinate is `alpha = w + i a`.  In the tilted
Hawking experiment, `w = Re alpha` is the real physical frequency and `a = Im alpha` is a
source tilt.  It is not legitimate to feed the complex number `alpha` into the black-hole Evans
denominator.  The source-dressed retarded matrix element has the normal form

`response_theta = N(w) XiC(w + i a) / W(w)`.

Every divisor orbit has a positive-frequency representative.  At that representative this module
proves unconditionally that `response_theta = 0` while `W(w) != 0`.  Thus theta divisor points are
real-frequency scattering/source zeros, not QNM poles.  Arbitrary finite radial overlap `N(w)`
cannot change this classification.

`[OPTICAL IDENTITY]` The actual real-axis optical identity is the greybody split

`E_infinity + E_horizon = E_source`,

with shares `sinh² eta / cosh² eta` and `1 / cosh² eta`.  At a theta divisor all three densities
vanish.  Horizon passivity is saturated there; it does not exclude the zero.  Positive absorbed
flux and quadratic mass backreaction are given in Eqs. (27)--(28) of
Sberna--Bosch--East--Green--Lehner, arXiv:2112.11168, so zero incoming amplitude also supplies no
sector-local backreaction producer.

`[FALSIFIED PHYSICAL ANSATZ]` A QNM contour expansion is not an orthogonal positive-energy
decomposition.  It contains a direct large-frequency arc, QNM residues, and a branch-cut tail;
Green et al. explicitly warn after Eq. (67) that the pole-only equality is not justified.  Even in
a Hilbert toy model the energy of `direct + pole + cut` contains all three interference terms.
This file proves the exact polarization identity and a closed counterexample to the positive
`pole energy + cut norm²` ansatz used conditionally in
`ThetaCuspHawkingQNMBranchCutCompletionEndpoint`.

`[STATIONARITY WALL]` Making `W` theta-dependent would require theta to alter the stationary
background rather than the incoming data.  For canonical minimally coupled EKG with symmetry
inheritance and the standard sign condition, Bekenstein's integral argument forces stationary
scalar hair to be constant; see Herdeiro--Radu, arXiv:1504.08209, Sec. 3.1.  If theta instead
backreacts dynamically, time-translation invariance is lost and the correct scattering object is
a two-frequency kernel, not a one-variable stationary Evans function.  This no-hair/dynamical
statement is literature input, not claimed as a Lean theorem below.

Therefore a genuine Einstein--Klein--Gordon/Teukolsky incidence closes the category question
negatively.  KMS/passivity cannot exclude the negative cubic chamber through a stationary Jost
completion.  Any surviving Hawking-native RH producer must use nonstationary, coefficient-faithful
multi-frequency backreaction beyond the real-axis Evans problem.
-/

open Complex Real

noncomputable section

namespace RHTower

/-! ## Every Xi divisor orbit has a positive physical-frequency representative -/

/-- Choose the member of a Schwarz-conjugate divisor pair whose centered physical frequency is
positive.  The transverse source tilt is retained by the reflection `alpha ↦ -conj alpha`. -/
def thetaCuspHawkingPositiveFrequencySupport (rho : XiDivisorSupport) :
    XiDivisorSupport :=
  if 0 < (xiSpectralPointSupport rho).re then rho else xiZeroConjEquiv rho

theorem thetaCuspHawkingPositiveFrequencySupport_re_pos (rho : XiDivisorSupport) :
    0 < (xiSpectralPointSupport (thetaCuspHawkingPositiveFrequencySupport rho)).re := by
  by_cases hpos : 0 < (xiSpectralPointSupport rho).re
  · simp [thetaCuspHawkingPositiveFrequencySupport, hpos]
  · have hneg : (xiSpectralPointSupport rho).re < 0 := by
      have hne := xiSpectralPointSupport_re_ne_zero rho
      exact lt_of_le_of_ne (le_of_not_gt hpos) hne
    rw [thetaCuspHawkingPositiveFrequencySupport, if_neg hpos,
      xiSpectralPointSupport_zeroConj]
    simpa [xiCenteredNegConj] using neg_pos.mpr hneg

/-- Real Schwarzschild carrier frequency attached to the positive divisor representative. -/
def thetaCuspHawkingPositiveJostFrequency (rho : XiDivisorSupport) : ℝ :=
  (xiSpectralPointSupport (thetaCuspHawkingPositiveFrequencySupport rho)).re

/-- Modular theta-source tilt attached to the same representative.  This is not imaginary
Schwarzschild frequency. -/
def thetaCuspHawkingPositiveJostTilt (rho : XiDivisorSupport) : ℝ :=
  (xiSpectralPointSupport (thetaCuspHawkingPositiveFrequencySupport rho)).im

theorem thetaCuspHawkingPositiveJostFrequency_pos (rho : XiDivisorSupport) :
    0 < thetaCuspHawkingPositiveJostFrequency rho :=
  thetaCuspHawkingPositiveFrequencySupport_re_pos rho

/-- Exact separation of one centered divisor point into real physical frequency and source tilt. -/
theorem thetaCuspHawkingPositiveJostCoordinate_eq (rho : XiDivisorSupport) :
    (thetaCuspHawkingPositiveJostFrequency rho : ℂ) +
        (thetaCuspHawkingPositiveJostTilt rho : ℂ) * I =
      xiSpectralPointSupport (thetaCuspHawkingPositiveFrequencySupport rho) := by
  apply Complex.ext <;>
    simp [thetaCuspHawkingPositiveJostFrequency, thetaCuspHawkingPositiveJostTilt]

/-! ## Flux-normalized Schwarzschild Evans/Jost normal form -/

/-- Real-axis Evans denominator `W = -2 i omega A_in`, with the conserved-flux normal form
`A_in = cosh(eta) exp(i phase)`.  Potential-specific data changes `eta` and `phase`, never its
real-axis nonvanishing. -/
def schwarzschildRealAxisEvansNormalForm
    (rapidity phase frequency : ℝ) : ℂ :=
  -2 * I * (frequency : ℂ) * (Real.cosh rapidity : ℂ) *
    Complex.exp (I * (phase : ℂ))

/-- Conserved real-axis flux forbids a Schwarzschild Evans zero at nonzero physical frequency. -/
theorem schwarzschildRealAxisEvansNormalForm_ne_zero
    (rapidity phase : ℝ) {frequency : ℝ} (hfrequency : frequency ≠ 0) :
    schwarzschildRealAxisEvansNormalForm rapidity phase frequency ≠ 0 := by
  unfold schwarzschildRealAxisEvansNormalForm
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr hfrequency))
      (ofReal_ne_zero.mpr (ne_of_gt (Real.cosh_pos rapidity))))
    (Complex.exp_ne_zero _)

/-- Theta-source matrix element of the real-axis retarded Green normal form.  `radialOverlap`
represents the finite radial numerator obtained by integrating the Jost solutions against initial
data.  Theta occurs only in the source numerator. -/
def thetaCuspHawkingSchwarzschildJostDressedResponse
    (rho : XiDivisorSupport) (rapidity phase : ℝ) (radialOverlap : ℂ) : ℂ :=
  radialOverlap *
      XiC (xiSpectralPointSupport (thetaCuspHawkingPositiveFrequencySupport rho)) /
    schwarzschildRealAxisEvansNormalForm rapidity phase
      (thetaCuspHawkingPositiveJostFrequency rho)

theorem thetaCuspHawkingSchwarzschildJostDressedResponse_eq_zero
    (rho : XiDivisorSupport) (rapidity phase : ℝ) (radialOverlap : ℂ) :
    thetaCuspHawkingSchwarzschildJostDressedResponse
      rho rapidity phase radialOverlap = 0 := by
  rw [thetaCuspHawkingSchwarzschildJostDressedResponse,
    XiC_xiSpectralPointSupport_eq_zero_source]
  simp

/-- **Exact incidence classification.** Every theta divisor orbit is a dark scattering/source
zero on its positive real-frequency representative, while the genuine real-axis Schwarzschild
Evans denominator is nonzero there. -/
theorem thetaCuspHawkingXiDivisor_is_scatteringZero_not_realAxisEvansPole
    (rho : XiDivisorSupport) (rapidity phase : ℝ) (radialOverlap : ℂ) :
    thetaCuspHawkingSchwarzschildJostDressedResponse
        rho rapidity phase radialOverlap = 0 ∧
      schwarzschildRealAxisEvansNormalForm rapidity phase
        (thetaCuspHawkingPositiveJostFrequency rho) ≠ 0 := by
  exact ⟨thetaCuspHawkingSchwarzschildJostDressedResponse_eq_zero
      rho rapidity phase radialOverlap,
    schwarzschildRealAxisEvansNormalForm_ne_zero rapidity phase
      (ne_of_gt (thetaCuspHawkingPositiveJostFrequency_pos rho))⟩

/-! ## Actual real-axis optical-energy identity -/

/-- Reflected fraction `|A_out/A_in|²` in flux rapidity coordinates. -/
def schwarzschildRealAxisReflectionEnergyShare (rapidity : ℝ) : ℝ :=
  Real.sinh rapidity ^ 2 / Real.cosh rapidity ^ 2

/-- Horizon-transmitted fraction `|1/A_in|²` in the same coordinates. -/
def schwarzschildRealAxisHorizonEnergyShare (rapidity : ℝ) : ℝ :=
  1 / Real.cosh rapidity ^ 2

/-- Schwarzschild real-axis optical theorem `|R|² + |T|² = 1`. -/
theorem schwarzschildRealAxis_opticalEnergyShares_add (rapidity : ℝ) :
    schwarzschildRealAxisReflectionEnergyShare rapidity +
        schwarzschildRealAxisHorizonEnergyShare rapidity = 1 := by
  unfold schwarzschildRealAxisReflectionEnergyShare
    schwarzschildRealAxisHorizonEnergyShare
  have hcosh : Real.cosh rapidity ≠ 0 := ne_of_gt (Real.cosh_pos rapidity)
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq rapidity]

/-- Theta source shell on the positive-frequency member of one divisor orbit. -/
def thetaCuspHawkingPositiveJostSourceEnergyDensity (rho : XiDivisorSupport) : ℝ :=
  thetaCuspHawkingTiltedBornRightEnergyShellDensity
    (thetaCuspHawkingPositiveJostTilt rho)
    (thetaCuspHawkingPositiveJostFrequency rho)

/-- Portion returned to infinity by the Schwarzschild greybody barrier. -/
def thetaCuspHawkingPositiveJostInfinityEnergyDensity
    (rho : XiDivisorSupport) (rapidity : ℝ) : ℝ :=
  schwarzschildRealAxisReflectionEnergyShare rapidity *
    thetaCuspHawkingPositiveJostSourceEnergyDensity rho

/-- Portion absorbed through the Schwarzschild horizon. -/
def thetaCuspHawkingPositiveJostHorizonEnergyDensity
    (rho : XiDivisorSupport) (rapidity : ℝ) : ℝ :=
  schwarzschildRealAxisHorizonEnergyShare rapidity *
    thetaCuspHawkingPositiveJostSourceEnergyDensity rho

/-- Source-faithful real-axis optical-energy split.  It is continuum-to-continuum plus horizon
absorption; no positive QNM-residue energy is inserted. -/
theorem thetaCuspHawkingPositiveJost_realAxisOpticalEnergyIdentity
    (rho : XiDivisorSupport) (rapidity : ℝ) :
    thetaCuspHawkingPositiveJostInfinityEnergyDensity rho rapidity +
        thetaCuspHawkingPositiveJostHorizonEnergyDensity rho rapidity =
      thetaCuspHawkingPositiveJostSourceEnergyDensity rho := by
  unfold thetaCuspHawkingPositiveJostInfinityEnergyDensity
    thetaCuspHawkingPositiveJostHorizonEnergyDensity
  rw [← add_mul, schwarzschildRealAxis_opticalEnergyShares_add]
  exact one_mul _

/-- Every theta divisor representative has zero incoming shell energy. -/
theorem thetaCuspHawkingPositiveJostSourceEnergyDensity_eq_zero
    (rho : XiDivisorSupport) :
    thetaCuspHawkingPositiveJostSourceEnergyDensity rho = 0 := by
  apply (thetaCuspHawkingTiltedBornRightEnergyShellDensity_eq_zero_iff
    (thetaCuspHawkingPositiveJostFrequency_pos rho)).2
  rw [thetaCuspHawkingPositiveJostCoordinate_eq]
  exact XiC_xiSpectralPointSupport_eq_zero_source _

/-- Exact physical consequence of the source-zero classification: both asymptotic real-axis
fluxes vanish, so sector-local horizon backreaction is not activated. -/
theorem thetaCuspHawkingXiDivisor_zero_realAxisFlux
    (rho : XiDivisorSupport) (rapidity : ℝ) :
    thetaCuspHawkingPositiveJostInfinityEnergyDensity rho rapidity = 0 ∧
      thetaCuspHawkingPositiveJostHorizonEnergyDensity rho rapidity = 0 := by
  rw [thetaCuspHawkingPositiveJostInfinityEnergyDensity,
    thetaCuspHawkingPositiveJostHorizonEnergyDensity,
    thetaCuspHawkingPositiveJostSourceEnergyDensity_eq_zero]
  simp

/-! ## QNM residue, direct arc, and branch cut are not positive orthogonal channels -/

/-- Scalar Hilbert normal form of the field energy after a contour split into direct, pole, and
branch-cut pieces.  The identity below already obstructs a positive two-channel reading; actual
QNMs have the additional problem that their radial profiles are not ordinary finite-energy
vectors. -/
def thetaCuspHawkingQNMDirectCutFieldEnergy (direct pole cut : ℂ) : ℝ :=
  ‖direct + pole + cut‖ ^ 2

/-- Exact three-way polarization.  A pole-plus-cut self-energy sum is valid only after proving
all missing direct and interference terms vanish. -/
theorem thetaCuspHawkingQNMDirectCutFieldEnergy_eq_self_add_interference
    (direct pole cut : ℂ) :
    thetaCuspHawkingQNMDirectCutFieldEnergy direct pole cut =
      ‖direct‖ ^ 2 + ‖pole‖ ^ 2 + ‖cut‖ ^ 2 +
        2 * ((starRingEnd ℂ) direct * pole).re +
        2 * ((starRingEnd ℂ) direct * cut).re +
        2 * ((starRingEnd ℂ) pole * cut).re := by
  rw [thetaCuspHawkingQNMDirectCutFieldEnergy,
    norm_add_sq_complex (direct + pole) cut,
    norm_add_sq_complex direct pole]
  simp only [map_add, add_mul, add_re]
  ring

/-- Closed counterexample to the positive pole-plus-cut ansatz: equal opposite contour pieces
cancel completely although their separate squared norms sum to two. -/
theorem thetaCuspHawkingQNM_poleCutPositiveSum_fails_without_orthogonality :
    thetaCuspHawkingQNMDirectCutFieldEnergy 0 1 (-1) = 0 ∧
      ‖(1 : ℂ)‖ ^ 2 + ‖(-1 : ℂ)‖ ^ 2 = 2 := by
  norm_num [thetaCuspHawkingQNMDirectCutFieldEnergy]

end RHTower
