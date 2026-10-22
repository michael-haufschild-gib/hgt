import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingNonlinearChiralTeukolskyReturnProducer
import GaloisForLFunctions.RHTower.Suzuki.SuzukiAntiPickIdentity

/-!
# Exact chiral AIME residue between topological-black-hole QNM branches

Birmingham--Mokhtari's signs `+xi` and `-xi` are the two QNM-frequency branches associated with
one horizon-Laplacian eigenvalue `Q = 1/4 + xi^(2 : ℕ)`. They are not two angular-momentum eigenspaces.
Consequently a genuine transition between them is a nonadiabatic QNM projection problem, not an
angular Noether commutator.

Sberna--Bosch--East--Green--Lehner derive precisely such a mechanism: absorption changes black-hole
mass, and a sufficiently rapid mass change projects an old QNM onto the QNMs of the new background.
Their excitation coefficient is a simple-Jost-pole normalization times a regularized bilinear
radial overlap. For the Hodge-paired `d=4`, `M=0` gravitational modes, the scalar-minus-vector mass
jet cancels every common operator variation and leaves the exact bracket `12/(Q+2)`.

For the fundamental Birmingham--Mokhtari branches,

`alpha_+ = -I omega_+ / 2`, `alpha_- = -I omega_- / 2`,

and `alpha_+ + alpha_- = -3/2`. Their exact radial functions therefore give the continued
cross-branch moment

`B(alpha_+ + alpha_- + 1, 2) = B(-1/2,2) = -4`.

The radial Jacobian contributes `1/2`, and scalar/vector parity-to-helicity conversion contributes
another `1/2`. In normalization `omega_4 deltaM/l^(2 : ℕ) = 1`, the chiral mass-jet numerator is

`K_-+ = 3 B(-1/2,2)/(Q+2) = -12/(Q+2)`.

The denominator `Q+2` is nonzero at every Xi divisor descendant. The residue normalization is not
only the universal derivative of the vanishing reciprocal-Gamma branch: it also contains the
nonvanishing Gamma boundary prefactor and companion Jost branch. Their exact product is proved to
be the derivative of the full Birmingham--Mokhtari boundary Jost function, retaining its
`z`-dependent phase. Thus the nonlinear numerator times the exact Green function has a simple pole,
and its normalized limit is literally the displayed AIME residue.

**[LITERATURE-DERIVED] [PAPER-PROVED] [LEAN-PROVED]** Exact fundamental cross-branch radial moment,
chiral mass-jet numerator, full-boundary-Jost derivative, Laurent residue, simple-pole frequency
response, horizon-phase support law, projective return determinant, and Cayley completion.

**[NO-GO]** This source-faithful nonlinear gravitational component does not select RH: it excites
every Xi descendant, not only tilted or central ones.

**[OPEN CORE]** In the fixed-angular-channel asymptotically AdS QNM problem the frequency Green
function is meromorphic; direct propagation is the large-frequency contour arc, not a local germ
at a QNM pole. It therefore cannot cancel this principal part. Since AIME is cubic, the reduced
second-order Einstein--Teukolsky source is excluded coefficientwise. Only the full third-order
`++-` Einstein--Teukolsky projection can supply an exact opposite numerator at the same pole.
Computing that coefficient is the remaining nonlinear chiral incidence problem, not KMS,
passivity, CCR, scalar energy, homogeneous angular mixing, or a generic continuum counterterm.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Ingoing exponent on the fundamental negative-frequency Birmingham--Mokhtari branch. -/
def d4FundamentalQNMMinusIngoingExponent (z : ℂ) : ℂ :=
  -Complex.I * thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 z / 2

/-- The two fundamental branch exponents have constant sum `-3/2`; the signed hyperbolic spectral
parameter cancels before radial projection. -/
theorem d4FundamentalQNMBranchIngoingExponent_sum (z : ℂ) :
    d4FundamentalQNMIngoingExponent z +
        d4FundamentalQNMMinusIngoingExponent z = -3 / 2 := by
  rw [d4FundamentalQNMIngoingExponent_eq_qnmPlus]
  unfold d4FundamentalQNMMinusIngoingExponent
    thetaCuspHawkingTopologicalBlackHoleQNMPlus
    thetaCuspHawkingTopologicalBlackHoleQNMMinus
    thetaCuspHawkingTopologicalBlackHoleConformalDecay
  norm_num
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Meromorphic continuation of the exact fundamental `plus/minus` radial bilinear
`B(alpha_+ + alpha_- + 1, 2)`. -/
def d4FundamentalQNMCrossBranchContinuedRadialMoment (z : ℂ) : ℂ :=
  1 / ((d4FundamentalQNMIngoingExponent z +
          d4FundamentalQNMMinusIngoingExponent z + 1) *
        (d4FundamentalQNMIngoingExponent z +
          d4FundamentalQNMMinusIngoingExponent z + 2))

/-- Exact continued cross-branch radial moment `B(-1/2,2)=-4`. -/
theorem d4FundamentalQNMCrossBranchContinuedRadialMoment_eq (z : ℂ) :
    d4FundamentalQNMCrossBranchContinuedRadialMoment z = -4 := by
  unfold d4FundamentalQNMCrossBranchContinuedRadialMoment
  rw [d4FundamentalQNMBranchIngoingExponent_sum]
  norm_num

/-- Exact chiral AIME mass-jet numerator between the two fundamental QNM branches. Factor `3` is
the Birmingham--Mokhtari parity split times radial Jacobian and helicity basis factors. -/
def d4FundamentalQNMCrossBranchChiralMassJetNumerator (z : ℂ) : ℂ :=
  3 * d4FundamentalQNMCrossBranchContinuedRadialMoment z /
    (d4ThetaTeukolskyAngularQ z + 2)

/-- Closed numerator `-12/(Q+2)`. -/
theorem d4FundamentalQNMCrossBranchChiralMassJetNumerator_eq (z : ℂ) :
    d4FundamentalQNMCrossBranchChiralMassJetNumerator z =
      -12 / (d4ThetaTeukolskyAngularQ z + 2) := by
  unfold d4FundamentalQNMCrossBranchChiralMassJetNumerator
  rw [d4FundamentalQNMCrossBranchContinuedRadialMoment_eq]
  ring

/-- Cross-branch numerator is invariant under exchange of the two square-root branches. -/
lemma d4FundamentalQNMCrossBranchChiralMassJetNumerator_shadow (z : ℂ) :
    d4FundamentalQNMCrossBranchChiralMassJetNumerator
        (thetaCuspHawkingOpticalCuspShadow z) =
      d4FundamentalQNMCrossBranchChiralMassJetNumerator z := by
  rw [d4FundamentalQNMCrossBranchChiralMassJetNumerator_eq,
    d4FundamentalQNMCrossBranchChiralMassJetNumerator_eq,
    d4ThetaTeukolskyAngularQ_shadow]

/-- Exact chiral cross-branch mass-jet numerator never vanishes at an Xi descendant. -/
theorem d4FundamentalQNMCrossBranchChiralMassJetNumerator_xi_ne_zero
    (q : XiZeroCopy) :
    d4FundamentalQNMCrossBranchChiralMassJetNumerator (xiSpectralPoint q) ≠ 0 := by
  rw [d4FundamentalQNMCrossBranchChiralMassJetNumerator_eq]
  exact div_ne_zero (by norm_num) (d4ThetaTeukolskyAngularQ_xi_add_two_ne_zero q)

/-- Cubic AIME numerator: seed amplitude times absorbed mass `|A|^(2 : ℕ)` times cross-branch chiral
mass jet. -/
def d4FundamentalQNMCrossBranchAIMENumerator (amplitude z : ℂ) : ℂ :=
  amplitude * (Complex.normSq amplitude : ℂ) *
    d4FundamentalQNMCrossBranchChiralMassJetNumerator z

/-- Cross-branch AIME numerator is nonzero at every Xi descendant exactly for nonzero seed. -/
theorem d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff
    (amplitude : ℂ) (q : XiZeroCopy) :
    d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) ≠ 0 ↔
      amplitude ≠ 0 := by
  constructor
  · contrapose!
    rintro rfl
    simp [d4FundamentalQNMCrossBranchAIMENumerator]
  · intro ha
    have hnormR : Complex.normSq amplitude ≠ 0 := by
      intro h
      exact ha (Complex.normSq_eq_zero.mp h)
    have hnormC : (Complex.normSq amplitude : ℂ) ≠ 0 := by
      exact_mod_cast hnormR
    exact mul_ne_zero (mul_ne_zero ha hnormC)
      (d4FundamentalQNMCrossBranchChiralMassJetNumerator_xi_ne_zero q)

/-- Derivative of the full physical Birmingham--Mokhtari boundary Jost function on the negative
QNM branch. Besides the derivative of the vanishing reciprocal-Gamma factor, this retains the
nonzero Gamma boundary prefactor and companion positive-branch Jost factor. -/
def d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus (n : ℕ) (z : ℂ) : ℂ :=
  let omega := thetaCuspHawkingTopologicalBlackHoleQNMMinus n z
  Complex.Gamma (thetaCuspHawkingHypergeometricRadialC omega) *
      Complex.Gamma (1 / 2 : ℂ) *
    thetaCuspHawkingHypergeometricJostPlus omega z *
      teukolskyNormalizedJostOmegaDerivative n

/-- Product-rule identification of the preceding normalization with the actual derivative of the
full physical boundary Jost function. -/
theorem d4FundamentalQNMCrossBranchBoundaryJost_hasDerivAt_qnmMinus_xi
    (n : ℕ) (q : XiZeroCopy) :
    HasDerivAt
      (fun omega : ℂ =>
        d4GravitationalHypergeometricBoundaryJost omega (xiSpectralPoint q))
      (d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus n (xiSpectralPoint q))
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)) := by
  let z := xiSpectralPoint q
  let omega := thetaCuspHawkingTopologicalBlackHoleQNMMinus n z
  let pref : ℂ → ℂ := fun w =>
    Complex.Gamma (thetaCuspHawkingHypergeometricRadialC w) *
      Complex.Gamma (1 / 2 : ℂ)
  let jPlus : ℂ → ℂ := fun w => thetaCuspHawkingHypergeometricJostPlus w z
  let jMinus : ℂ → ℂ := fun w => thetaCuspHawkingHypergeometricJostMinus w z
  have hprefAna : AnalyticAt ℂ pref omega := by
    exact (thetaCuspHawkingHypergeometricAnalyticAt_gammaRadialC_of_ne_neg_nat omega
      (thetaCuspHawkingHypergeometricRadialC_qnmMinus_ne_neg_nat n · q)).mul
        analyticAt_const
  have hpref : HasDerivAt pref (deriv pref omega) omega :=
    hprefAna.differentiableAt.hasDerivAt
  have hplus : HasDerivAt jPlus (deriv jPlus omega) omega :=
    (thetaCuspHawkingHypergeometricAnalyticAt_jostPlus omega z).differentiableAt.hasDerivAt
  have hminus : HasDerivAt jMinus (teukolskyNormalizedJostOmegaDerivative n) omega := by
    simpa [jMinus, omega, z, teukolskyNormalizedJostOmegaDerivative] using
      thetaCuspHawkingHypergeometricHasDerivAt_jostMinus_qnm n z
  have hminusZero : jMinus omega = 0 := by
    simp [jMinus, omega, thetaCuspHawkingHypergeometricJostMinus_qnm_zero]
  have hprod := (hpref.mul hplus).mul hminus
  have hfun :
      (fun w : ℂ => d4GravitationalHypergeometricBoundaryJost w (xiSpectralPoint q)) =
        pref * jPlus * jMinus := by
    funext w
    simp [d4GravitationalHypergeometricBoundaryJost,
      thetaCuspHawkingHypergeometricPhysicalBoundaryJost,
      thetaCuspHawkingHypergeometricJost, pref, jPlus, jMinus, z]
    ring
  rw [hfun]
  exact hprod.congr_deriv (by
    simp [d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus,
      pref, jPlus, omega, z, hminusZero])

/-- The actual full-boundary derivative is nonzero at every Xi descendant. -/
theorem d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus_xi_ne_zero
    (n : ℕ) (q : XiZeroCopy) :
    d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus n (xiSpectralPoint q) ≠ 0 := by
  unfold d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (Complex.Gamma_ne_zero
          (thetaCuspHawkingHypergeometricRadialC_qnmMinus_ne_neg_nat n · q))
        thetaCuspHawkingHypergeometricGamma_half_ne_zero)
      (thetaCuspHawkingHypergeometricJostPlus_qnmMinus_ne_zero n q))
    (teukolskyNormalizedJostOmegaDerivative_ne_zero n)

/-- Frequency-domain AIME response before extracting the simple-pole residue. The nonlinear
source numerator is evaluated in the fixed angular sector and propagated by the exact
Birmingham--Mokhtari gravitational Green function. -/
def d4FundamentalQNMCrossBranchAIMEFrequencyResponse
    (amplitude z omega : ℂ) : ℂ :=
  d4FundamentalQNMCrossBranchAIMENumerator amplitude z *
    d4GravitationalHypergeometricBoundaryGreen omega z

/-- Nonzero absorbed seed produces an actual simple scattering pole on the opposite fundamental
QNM branch. This proves pole incidence before any residue or Cayley repackaging. -/
theorem d4FundamentalQNMCrossBranchAIMEFrequencyResponse_order_qnmMinus_xi
    {amplitude : ℂ} (ha : amplitude ≠ 0) (q : XiZeroCopy) :
    meromorphicOrderAt
      (fun omega : ℂ =>
        d4FundamentalQNMCrossBranchAIMEFrequencyResponse
          amplitude (xiSpectralPoint q) omega)
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)) =
        ((-1 : ℤ) : WithTop ℤ) := by
  have hnum :
      d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) ≠ 0 :=
    (d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude q).mpr ha
  have hunit : AnalyticAt ℂ
      (fun _ : ℂ =>
        d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q))
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)) :=
    analyticAt_const
  change meromorphicOrderAt
      ((fun _ : ℂ =>
        d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q)) *
        (fun omega : ℂ =>
          d4GravitationalHypergeometricBoundaryGreen omega (xiSpectralPoint q)))
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)) = _
  rw [meromorphicOrderAt_mul_of_ne_zero hunit hnum]
  exact d4GravitationalHypergeometricBoundaryGreen_order_qnmMinus_xi 0 q

/-- Simple-Jost-pole normalized excitation residue of the fundamental negative branch generated
by the positive branch under the chiral mass jet. -/
def d4FundamentalQNMCrossBranchAIMEResidue (amplitude z : ℂ) : ℂ :=
  d4FundamentalQNMCrossBranchAIMENumerator amplitude z /
    d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus 0 z

/-- Actual Laurent-residue extraction from the full Birmingham--Mokhtari boundary Green function.
This closes the gap between a declared normalization and the scattering residue itself. -/
theorem d4FundamentalQNMCrossBranchAIMEFrequencyResponse_tendsto_residue
    (amplitude : ℂ) (q : XiZeroCopy) :
    Tendsto
      (fun omega : ℂ =>
        (omega - thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)) *
          d4FundamentalQNMCrossBranchAIMEFrequencyResponse
            amplitude (xiSpectralPoint q) omega)
      (nhdsWithin
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q))
        {thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)}ᶜ)
      (nhds (d4FundamentalQNMCrossBranchAIMEResidue amplitude (xiSpectralPoint q))) := by
  let sigma := thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)
  let D : ℂ → ℂ := fun omega =>
    d4GravitationalHypergeometricBoundaryJost omega (xiSpectralPoint q)
  let N : ℂ → ℂ := fun _ =>
    d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q)
  have hD : HasDerivAt D
      (d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus 0 (xiSpectralPoint q)) sigma := by
    simpa [D, sigma] using
      d4FundamentalQNMCrossBranchBoundaryJost_hasDerivAt_qnmMinus_xi 0 q
  have hD0 : D sigma = 0 := by
    simp [D, sigma, d4GravitationalHypergeometricBoundaryJost,
      thetaCuspHawkingHypergeometricPhysicalBoundaryJost,
      thetaCuspHawkingHypergeometricJost,
      thetaCuspHawkingHypergeometricJostMinus_qnm_zero]
  have hlim := tendsto_residue_of_simple_zero hD hD0
    (d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus_xi_ne_zero 0 q)
    (continuousAt_const : ContinuousAt N sigma)
  simpa [sigma, D, N, d4FundamentalQNMCrossBranchAIMEResidue,
    d4FundamentalQNMCrossBranchAIMEFrequencyResponse,
    d4GravitationalHypergeometricBoundaryGreen, div_eq_mul_inv] using hlim

/-- Nonzero numerator survives division by exact nonzero derivative of the simple Jost zero. -/
theorem d4FundamentalQNMCrossBranchAIMEResidue_xi_ne_zero_iff
    (amplitude : ℂ) (q : XiZeroCopy) :
    d4FundamentalQNMCrossBranchAIMEResidue amplitude (xiSpectralPoint q) ≠ 0 ↔
      amplitude ≠ 0 := by
  constructor
  · intro hres ha
    rw [ha] at hres
    simp [d4FundamentalQNMCrossBranchAIMEResidue,
      d4FundamentalQNMCrossBranchAIMENumerator] at hres
  · intro ha
    exact div_ne_zero
      ((d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude q).mpr ha)
      (d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus_xi_ne_zero 0 q)

/-- Cross-branch residue after the full complex horizon-frequency phase generated by absorbed
mass. No unitarity of this QNM phase is assumed. -/
def d4FundamentalQNMCrossBranchAIMEResidueWithHorizonPhase
    (advancedTime : ℝ) (amplitude : ℂ)
    (horizonFrequencyJet : ℂ → ℂ) (z : ℂ) : ℂ :=
  d4HorizonBackreactionPhase advancedTime amplitude horizonFrequencyJet z *
    d4FundamentalQNMCrossBranchAIMEResidue amplitude z

/-- Arbitrary horizon-frequency jet cannot erase support of the nonzero simple-pole residue. -/
theorem d4FundamentalQNMCrossBranchAIMEResidueWithHorizonPhase_xi_ne_zero_iff
    (advancedTime : ℝ) (amplitude : ℂ)
    (horizonFrequencyJet : ℂ → ℂ) (q : XiZeroCopy) :
    d4FundamentalQNMCrossBranchAIMEResidueWithHorizonPhase
        advancedTime amplitude horizonFrequencyJet (xiSpectralPoint q) ≠ 0 ↔
      amplitude ≠ 0 := by
  unfold d4FundamentalQNMCrossBranchAIMEResidueWithHorizonPhase
  rw [mul_ne_zero_iff]
  rw [and_iff_right (d4HorizonBackreactionPhase_ne_zero
    advancedTime amplitude horizonFrequencyJet (xiSpectralPoint q))]
  exact d4FundamentalQNMCrossBranchAIMEResidue_xi_ne_zero_iff amplitude q

/-- Branch-resolved returned Jost channel: phased old line plus phased chiral AIME residue. -/
def d4FundamentalQNMCrossBranchAIMEReturnedJost
    (advancedTime : ℝ) (amplitude : ℂ)
    (horizonFrequencyJet : ℂ → ℂ) (omega : ℂ) : ℂ → ℂ :=
  teukolskyReturnedJostWithHorizonPhase omega
    (d4HorizonBackreactionPhase advancedTime amplitude horizonFrequencyJet)
    (d4FundamentalQNMCrossBranchAIMEResidueWithHorizonPhase
      advancedTime amplitude horizonFrequencyJet)

/-- Genuine cross-branch AIME residue makes projective return nonzero at every Xi descendant
exactly for nonzero absorbed seed. -/
theorem d4FundamentalQNMCrossBranchAIMEReturnDeterminant_qnmPlus_ne_zero_iff
    (advancedTime : ℝ) (amplitude : ℂ)
    (horizonFrequencyJet : ℂ → ℂ) (q : XiZeroCopy) :
    teukolskyReturnDeterminant
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q))
        (d4FundamentalQNMCrossBranchAIMEReturnedJost
          advancedTime amplitude horizonFrequencyJet
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q)))
        (xiSpectralPoint q) ≠ 0 ↔
      amplitude ≠ 0 := by
  unfold d4FundamentalQNMCrossBranchAIMEReturnedJost
  exact (teukolskyCrossSource_is_exact_qnmPlus_return_producer 0 q _ _).trans
    (d4FundamentalQNMCrossBranchAIMEResidueWithHorizonPhase_xi_ne_zero_iff
      advancedTime amplitude horizonFrequencyJet q)

/-- Canonical nonperturbative projective Cayley completion of cross-branch AIME return. -/
def d4FundamentalQNMCrossBranchAIMECayleySMatrix
    (advancedTime : ℝ) (amplitude : ℂ)
    (horizonFrequencyJet : ℂ → ℂ) (omega z : ℂ) : ℂ :=
  teukolskyReturnCayleySMatrix omega
    (d4FundamentalQNMCrossBranchAIMEReturnedJost
      advancedTime amplitude horizonFrequencyJet omega) z

/-- Exact theta-shadow inverse law for cross-branch projective completion. -/
theorem d4FundamentalQNMCrossBranchAIMECayleySMatrix_shadow
    (advancedTime : ℝ) (amplitude : ℂ)
    (horizonFrequencyJet : ℂ → ℂ) (omega z : ℂ) :
    d4FundamentalQNMCrossBranchAIMECayleySMatrix
        advancedTime amplitude horizonFrequencyJet omega
        (thetaCuspHawkingOpticalCuspShadow z) =
      (d4FundamentalQNMCrossBranchAIMECayleySMatrix
        advancedTime amplitude horizonFrequencyJet omega z)⁻¹ := by
  exact teukolskyReturnCayleySMatrix_shadow omega _ z

/-- Completed cross-branch AIME return is nontrivial at every Xi descendant exactly for nonzero
absorbed seed. -/
theorem d4FundamentalQNMCrossBranchAIMECayleySMatrix_qnmPlus_ne_one_iff
    (advancedTime : ℝ) (amplitude : ℂ)
    (horizonFrequencyJet : ℂ → ℂ) (q : XiZeroCopy) :
    d4FundamentalQNMCrossBranchAIMECayleySMatrix
        advancedTime amplitude horizonFrequencyJet
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q))
        (xiSpectralPoint q) ≠ 1 ↔
      amplitude ≠ 0 := by
  unfold d4FundamentalQNMCrossBranchAIMECayleySMatrix
    d4FundamentalQNMCrossBranchAIMEReturnedJost
  exact (teukolskyReturnCayleySMatrix_qnmPlus_ne_one_iff_crossSource 0 q _ _).trans
    (d4FundamentalQNMCrossBranchAIMEResidueWithHorizonPhase_xi_ne_zero_iff
      advancedTime amplitude horizonFrequencyJet q)

/-- Source-faithful no-selection theorem: nonzero AIME seed produces nontrivial cross-branch
projective completion at every Xi descendant, central or tilted. -/
theorem d4FundamentalQNMCrossBranchAIMECayleySMatrix_nontrivial_everyXi
    (advancedTime : ℝ) {amplitude : ℂ} (ha : amplitude ≠ 0)
    (horizonFrequencyJet : ℂ → ℂ) :
    ∀ q : XiZeroCopy,
      d4FundamentalQNMCrossBranchAIMECayleySMatrix
          advancedTime amplitude horizonFrequencyJet
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q))
          (xiSpectralPoint q) ≠ 1 := by
  intro q
  exact (d4FundamentalQNMCrossBranchAIMECayleySMatrix_qnmPlus_ne_one_iff
    advancedTime amplitude horizonFrequencyJet q).mpr ha

/-- Full cubic on-shell source numerator in the same inverse-Jost channel. A direct contour arc is
deliberately absent: only a third-order `++-` term sharing this QNM denominator and grade can alter
its local principal part. -/
def d4FullCrossBranchPoleNumerator
    (amplitude : ℂ) (samePoleSourceRemainder : ℂ → ℂ) (z : ℂ) : ℂ :=
  d4FundamentalQNMCrossBranchAIMENumerator amplitude z +
    samePoleSourceRemainder z

/-- Exact source-level cancellation classification at every Xi descendant. -/
theorem d4FullCrossBranchPoleNumerator_xi_eq_zero_iff_counterterm
    (amplitude : ℂ) (samePoleSourceRemainder : ℂ → ℂ) (q : XiZeroCopy) :
    d4FullCrossBranchPoleNumerator amplitude samePoleSourceRemainder
        (xiSpectralPoint q) = 0 ↔
      samePoleSourceRemainder (xiSpectralPoint q) =
        -d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) := by
  unfold d4FullCrossBranchPoleNumerator
  constructor <;> intro h <;> linear_combination h

/-- Principal-part carrier obtained by freezing the full nonlinear source numerator at the target
QNM. Frequency-regular terms are intentionally outside this local object. -/
def d4FullCrossBranchPolePrincipalPart
    (amplitude : ℂ) (samePoleSourceRemainder : ℂ → ℂ) (z omega : ℂ) : ℂ :=
  d4FullCrossBranchPoleNumerator amplitude samePoleSourceRemainder z *
    d4GravitationalHypergeometricBoundaryGreen omega z

/-- Sharp local alternative: full response retains exact simple pole unless remaining third-order
`++-` Einstein--Teukolsky source supplies unique opposite numerator at that same pole. -/
theorem d4FullCrossBranchPolePrincipalPart_order_qnmMinus_xi_iff
    (amplitude : ℂ) (samePoleSourceRemainder : ℂ → ℂ) (q : XiZeroCopy) :
    meromorphicOrderAt
      (fun omega : ℂ =>
        d4FullCrossBranchPolePrincipalPart amplitude samePoleSourceRemainder
          (xiSpectralPoint q) omega)
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)) =
        ((-1 : ℤ) : WithTop ℤ) ↔
      samePoleSourceRemainder (xiSpectralPoint q) ≠
        -d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) := by
  constructor
  · intro horder hremainder
    have hnum : d4FullCrossBranchPoleNumerator amplitude samePoleSourceRemainder
        (xiSpectralPoint q) = 0 :=
      (d4FullCrossBranchPoleNumerator_xi_eq_zero_iff_counterterm
        amplitude samePoleSourceRemainder q).mpr hremainder
    have hzeroOrder :
        meromorphicOrderAt (fun _ : ℂ => (0 : ℂ))
          (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)) = ⊤ :=
      meromorphicOrderAt_eq_top_iff.mpr
        (Eventually.of_forall fun _ : ℂ => (rfl : (0 : ℂ) = 0))
    rw [show (fun omega : ℂ =>
        d4FullCrossBranchPolePrincipalPart amplitude samePoleSourceRemainder
          (xiSpectralPoint q) omega) = (fun _ : ℂ => 0) by
          funext omega
          simp [d4FullCrossBranchPolePrincipalPart, hnum], hzeroOrder] at horder
    exact WithTop.coe_ne_top horder.symm
  · intro hremainder
    have hnum : d4FullCrossBranchPoleNumerator amplitude samePoleSourceRemainder
        (xiSpectralPoint q) ≠ 0 := by
      intro hzero
      exact hremainder
        ((d4FullCrossBranchPoleNumerator_xi_eq_zero_iff_counterterm
          amplitude samePoleSourceRemainder q).mp hzero)
    have hunit : AnalyticAt ℂ
        (fun _ : ℂ =>
          d4FullCrossBranchPoleNumerator amplitude samePoleSourceRemainder
            (xiSpectralPoint q))
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)) :=
      analyticAt_const
    change meromorphicOrderAt
        ((fun _ : ℂ =>
          d4FullCrossBranchPoleNumerator amplitude samePoleSourceRemainder
            (xiSpectralPoint q)) *
          (fun omega : ℂ =>
            d4GravitationalHypergeometricBoundaryGreen omega (xiSpectralPoint q)))
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)) = _
    rw [meromorphicOrderAt_mul_of_ne_zero hunit hnum]
    exact d4GravitationalHypergeometricBoundaryGreen_order_qnmMinus_xi 0 q

/-- Simple-pole residue obtained from full same-pole source numerator by exact Jost-derivative
normalization. -/
def d4FullCrossBranchProjectedResidue
    (amplitude : ℂ) (samePoleSourceRemainder : ℂ → ℂ) (z : ℂ) : ℂ :=
  d4FullCrossBranchPoleNumerator amplitude samePoleSourceRemainder z /
    d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus 0 z

/-- Residue cancellation is equivalent to source-numerator cancellation because target Jost zero
is simple. -/
theorem d4FullCrossBranchProjectedResidue_xi_eq_zero_iff_counterterm
    (amplitude : ℂ) (samePoleSourceRemainder : ℂ → ℂ) (q : XiZeroCopy) :
    d4FullCrossBranchProjectedResidue amplitude samePoleSourceRemainder
        (xiSpectralPoint q) = 0 ↔
      samePoleSourceRemainder (xiSpectralPoint q) =
        -d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) := by
  unfold d4FullCrossBranchProjectedResidue
  rw [div_eq_zero_iff]
  simp only [d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus_xi_ne_zero,
    or_false]
  exact d4FullCrossBranchPoleNumerator_xi_eq_zero_iff_counterterm
    amplitude samePoleSourceRemainder q

/-- Returned Jost channel retaining full same-pole nonlinear source beside exact AIME term and
multiplying physical return by common horizon-backreaction phase. -/
def d4FullCrossBranchAIMEReturnedJost
    (advancedTime : ℝ) (amplitude : ℂ)
    (horizonFrequencyJet samePoleSourceRemainder : ℂ → ℂ)
    (omega : ℂ) : ℂ → ℂ :=
  teukolskyReturnedJostWithHorizonPhase omega
    (d4HorizonBackreactionPhase advancedTime amplitude horizonFrequencyJet)
    (fun z =>
      d4HorizonBackreactionPhase advancedTime amplitude horizonFrequencyJet z *
        d4FullCrossBranchProjectedResidue amplitude samePoleSourceRemainder z)

/-- Full branch-resolved Evans return can vanish at an Xi descendant exactly through the forced
same-pole source counterterm. Common horizon phase and companion Jost factor cannot cancel it. -/
theorem d4FullCrossBranchAIMEReturnDeterminant_qnmPlus_eq_zero_iff_counterterm
    (advancedTime : ℝ) (amplitude : ℂ)
    (horizonFrequencyJet samePoleSourceRemainder : ℂ → ℂ) (q : XiZeroCopy) :
    teukolskyReturnDeterminant
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q))
        (d4FullCrossBranchAIMEReturnedJost
          advancedTime amplitude horizonFrequencyJet samePoleSourceRemainder
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q)))
        (xiSpectralPoint q) = 0 ↔
      samePoleSourceRemainder (xiSpectralPoint q) =
        -d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) := by
  rw [teukolskyReturnDeterminant_qnmPlus]
  have hcomp := thetaCuspHawkingHypergeometricJostMinus_qnmPlus_ne_zero 0 q
  rw [mul_eq_zero]
  simp only [hcomp, or_false]
  rw [d4FullCrossBranchAIMEReturnedJost,
    teukolskyReturnedJostWithHorizonPhase_qnmPlus]
  rw [mul_eq_zero]
  simp only [d4HorizonBackreactionPhase_ne_zero, false_or]
  exact d4FullCrossBranchProjectedResidue_xi_eq_zero_iff_counterterm
    amplitude samePoleSourceRemainder q

/-- For nonzero absorbed seed, counterterm demanded of remaining dynamics is itself nonzero at
every Xi descendant. -/
theorem d4FullCrossBranch_forcedCounterterm_xi_ne_zero_iff
    (amplitude : ℂ) (q : XiZeroCopy) :
    -d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) ≠ 0 ↔
      amplitude ≠ 0 := by
  rw [neg_ne_zero]
  exact d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude q

end

end RHTower
