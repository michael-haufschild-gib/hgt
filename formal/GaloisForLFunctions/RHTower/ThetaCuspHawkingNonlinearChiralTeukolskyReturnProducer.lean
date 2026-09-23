import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskyBackreactionReturnDeterminant

/-!
# Source-derived nonlinear chiral gravitational return producer

This module closes the exact fundamental-mode part of the nonlinear return problem left open by
ThetaCuspHawkingTeukolskyBackreactionReturnDeterminant.

## Same-background source projection

Birmingham--Mokhtari, arXiv:hep-th/0609028, give the exact d=4, M=0
Kodama--Ishibashi gravitational mode

Phi_0(y) = y^alpha (1-y)^(1/2)

on the fundamental plus QNM branch. Here y=1-l^(2 : ℕ)/r^(2 : ℕ) and alpha=-i omega l/2. The Hodge-paired
scalar and vector modes have the same massless radial function. Therefore all common first
variations--kinetic operator, tortoise coordinate, moving horizon, and boundary normalization--
cancel from the scalar-minus-vector channel. The surviving variation is exactly the
potential-bracket split proved in the preceding module,

d(B_S-B_V)/dx|_0 = 12/(Q+2).

The conserved QNM bilinear formula of Lestingi--Sberna--Green, arXiv:2607.19492, projects this
source directly, without a QNM completeness assumption. In dimensionless normalization
omega_4/l^(2 : ℕ)=1,

integral Phi_0^(2 : ℕ) dr/r^(3 : ℕ) = (1/2) B(2 alpha+1,2).

The meromorphic Euler continuation is elementary:

B(2 alpha+1,2)=1/((2 alpha+1)(2 alpha+2)).

For theta coordinate rho=1/2+i z,

alpha=-(rho+2)/4, Q=rho(2-rho)/4,

so the continued radial moment is

4/(rho(rho-2)) = -1/Q.

The radial Jacobian contributes 1/2; changing from scalar/vector parity to two helicities
contributes a second 1/2. The exact off-diagonal helicity kernel is consequently

K_cross = 3 B(2 alpha+1,2)/(Q+2) = -3/(Q(Q+2)).

Every actual Xi divisor has 0 < re rho < 1; hence neither Q nor Q+2 vanishes there.

## Horizon backreaction and return

Absorbed horizon mass is quadratic in a normalized ingoing amplitude A. Its action on the
surviving seed is therefore the cubic AIME source

A |A|^(2 : ℕ) K_cross.

This is the background-mass insertion component of nonlinear gravitational return. The common
horizon frequency jet produces the complex QNM phase

exp(-i v |A|^(2 : ℕ) deltaOmega_H).

The jet remains quantified because the parity-difference calculation deliberately cancels the
common operator variation. No property of that phase is assumed: at the old Jost zero it cancels
identically, while the concrete cubic cross-helicity source survives.

The resulting projective Evans wedge and its Cayley completion are nontrivial at every Xi divisor
whenever A != 0. This is a same-branch, fixed-`Q` comparison invariant, not yet the AIME projection
between the `+xi` and `-xi` QNM-frequency branches. Those signs exchange square-root branches of
one separated eigenvalue; they are not distinct angular-momentum eigenspaces.

Spiers--Pound--Moxon's reduced second-order Teukolsky source is quadratic in the first-order
metric, whereas AIME is cubic.  The algebraically free remainder below must therefore be read as
a same-order third-order remainder if it is to cancel AIME coefficientwise.  The downstream
perturbative-grade theorem proves that every second-order Einstein grade is excluded and that only
the third-order `++-` helicity channel can supply the classified opposite numerator.

**[LITERATURE-DERIVED] [PAPER-PROVED] [LEAN-PROVED]** Fundamental QNM radial moment,
fixed-sector parity-to-helicity source, cubic AIME return, phase cancellation, all-sector
projective nontriviality, theta-mirror Cayley law, and exact projective counterterm classification.

Unevaluated mixed- and anti-chiral coefficients belong to distinct grades and cannot act as the
classified pointwise direct counterterm.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Xi-divisor argument represented by theta scattering coordinate z. -/
def d4ThetaTeukolskyRho (z : ℂ) : ℂ := 1 / 2 + Complex.I * z

/-- Ingoing exponent of exact fundamental plus-branch gravitational QNM. -/
def d4FundamentalQNMIngoingExponent (z : ℂ) : ℂ :=
  -(d4ThetaTeukolskyRho z + 2) / 4

/-- Meromorphic Euler continuation of fundamental radial source moment B(2 alpha+1,2). -/
def d4FundamentalQNMContinuedRadialMoment (z : ℂ) : ℂ :=
  1 / ((2 * d4FundamentalQNMIngoingExponent z + 1) *
    (2 * d4FundamentalQNMIngoingExponent z + 2))

/-- Complex angular eigenvalue in paired gravitational channel. -/
def d4ThetaTeukolskyAngularQ (z : ℂ) : ℂ :=
  thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue z

/-- Exact off-diagonal helicity coefficient after radial projection of scalar/vector
mass-variation split. -/
def d4FundamentalQNMChiralSourceKernel (z : ℂ) : ℂ :=
  3 * d4FundamentalQNMContinuedRadialMoment z /
    (d4ThetaTeukolskyAngularQ z + 2)

/-- Same projected source before parity-to-helicity factor 1/2. -/
def d4FundamentalQNMParitySourceProjection (z : ℂ) : ℂ :=
  6 * d4FundamentalQNMContinuedRadialMoment z /
    (d4ThetaTeukolskyAngularQ z + 2)

/-- Positive-helicity combination of scalar and vector gravitational parities. -/
def d4GravitationalHelicityPlus (scalar vector : ℂ) : ℂ :=
  scalar + Complex.I * vector

/-- Negative-helicity combination of scalar and vector gravitational parities. -/
def d4GravitationalHelicityMinus (scalar vector : ℂ) : ℂ :=
  scalar - Complex.I * vector

lemma d4ThetaTeukolskyRho_shadow (z : ℂ) :
    d4ThetaTeukolskyRho (thetaCuspHawkingOpticalCuspShadow z) =
      2 - d4ThetaTeukolskyRho z := by
  unfold d4ThetaTeukolskyRho thetaCuspHawkingOpticalCuspShadow
  rw [mul_sub, Complex.I_mul_I]
  ring

lemma d4ThetaTeukolskyRho_xiSpectralPoint (q : XiZeroCopy) :
    d4ThetaTeukolskyRho (xiSpectralPoint q) = (q.1 : ℂ) := by
  unfold d4ThetaTeukolskyRho xiSpectralPoint
  ring_nf
  rw [Complex.I_sq]
  ring

lemma d4ThetaTeukolskyAngularMomentum_eq_rho (z : ℂ) :
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum z =
      Complex.I * (1 - d4ThetaTeukolskyRho z) / 2 := by
  unfold thetaCuspHawkingTopologicalBlackHoleAngularMomentum d4ThetaTeukolskyRho
  ring_nf
  rw [Complex.I_sq]
  ring

lemma d4ThetaTeukolskyAngularQ_eq_rho (z : ℂ) :
    d4ThetaTeukolskyAngularQ z =
      d4ThetaTeukolskyRho z * (2 - d4ThetaTeukolskyRho z) / 4 := by
  unfold d4ThetaTeukolskyAngularQ
    thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue
  rw [d4ThetaTeukolskyAngularMomentum_eq_rho]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma d4ThetaTeukolskyAngularQ_shadow (z : ℂ) :
    d4ThetaTeukolskyAngularQ (thetaCuspHawkingOpticalCuspShadow z) =
      d4ThetaTeukolskyAngularQ z := by
  rw [d4ThetaTeukolskyAngularQ_eq_rho, d4ThetaTeukolskyAngularQ_eq_rho,
    d4ThetaTeukolskyRho_shadow]
  ring

/-- Exponent above is literally -i omega/2 on Birmingham--Mokhtari fundamental plus QNM. -/
lemma d4FundamentalQNMIngoingExponent_eq_qnmPlus (z : ℂ) :
    d4FundamentalQNMIngoingExponent z =
      -Complex.I * thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 z / 2 := by
  unfold d4FundamentalQNMIngoingExponent d4ThetaTeukolskyRho
    thetaCuspHawkingTopologicalBlackHoleQNMPlus
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum
    thetaCuspHawkingTopologicalBlackHoleConformalDecay
  norm_num
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Exact beta-denominator reduction of fundamental source moment. -/
lemma d4FundamentalQNMContinuedRadialMoment_denominator (z : ℂ) :
    (2 * d4FundamentalQNMIngoingExponent z + 1) *
        (2 * d4FundamentalQNMIngoingExponent z + 2) =
      -d4ThetaTeukolskyAngularQ z := by
  rw [d4ThetaTeukolskyAngularQ_eq_rho]
  unfold d4FundamentalQNMIngoingExponent
  ring

/-- Continued radial beta moment is exactly -1/Q. -/
theorem d4FundamentalQNMContinuedRadialMoment_eq_neg_inv_Q (z : ℂ) :
    d4FundamentalQNMContinuedRadialMoment z =
      -(d4ThetaTeukolskyAngularQ z)⁻¹ := by
  unfold d4FundamentalQNMContinuedRadialMoment
  rw [d4FundamentalQNMContinuedRadialMoment_denominator]
  simp [one_div]

lemma d4FundamentalQNMContinuedRadialMoment_shadow (z : ℂ) :
    d4FundamentalQNMContinuedRadialMoment
        (thetaCuspHawkingOpticalCuspShadow z) =
      d4FundamentalQNMContinuedRadialMoment z := by
  rw [d4FundamentalQNMContinuedRadialMoment_eq_neg_inv_Q,
    d4FundamentalQNMContinuedRadialMoment_eq_neg_inv_Q,
    d4ThetaTeukolskyAngularQ_shadow]

/-- Away from two physical denominators, source kernel is rational function -3/(Q(Q+2)). -/
theorem d4FundamentalQNMChiralSourceKernel_eq
    (z : ℂ) (hQ : d4ThetaTeukolskyAngularQ z ≠ 0)
    (hQ2 : d4ThetaTeukolskyAngularQ z + 2 ≠ 0) :
    d4FundamentalQNMChiralSourceKernel z =
      -3 / (d4ThetaTeukolskyAngularQ z *
        (d4ThetaTeukolskyAngularQ z + 2)) := by
  rw [d4FundamentalQNMChiralSourceKernel,
    d4FundamentalQNMContinuedRadialMoment_eq_neg_inv_Q]
  field_simp [hQ, hQ2]

lemma d4FundamentalQNMChiralSourceKernel_shadow (z : ℂ) :
    d4FundamentalQNMChiralSourceKernel
        (thetaCuspHawkingOpticalCuspShadow z) =
      d4FundamentalQNMChiralSourceKernel z := by
  unfold d4FundamentalQNMChiralSourceKernel
  rw [d4FundamentalQNMContinuedRadialMoment_shadow,
    d4ThetaTeukolskyAngularQ_shadow]

/-- Helicity off-diagonal is half literal scalar-minus-vector projection. -/
lemma d4FundamentalQNMChiralSourceKernel_eq_half_parityProjection (z : ℂ) :
    d4FundamentalQNMChiralSourceKernel z =
      d4FundamentalQNMParitySourceProjection z / 2 := by
  unfold d4FundamentalQNMChiralSourceKernel d4FundamentalQNMParitySourceProjection
  ring

/-- Exact parity-to-helicity basis change. A response diagonal in scalar/vector parity has
off-diagonal helicity coefficient (scalarResponse-vectorResponse)/2. -/
theorem d4ParityResponse_eq_helicityMix
    (scalarResponse vectorResponse scalarMode vectorMode : ℂ) :
    scalarResponse * scalarMode + Complex.I * vectorResponse * vectorMode =
      (scalarResponse + vectorResponse) / 2 *
          d4GravitationalHelicityPlus scalarMode vectorMode +
        (scalarResponse - vectorResponse) / 2 *
          d4GravitationalHelicityMinus scalarMode vectorMode := by
  unfold d4GravitationalHelicityPlus d4GravitationalHelicityMinus
  ring

private lemma d4XiRho_ne_zero (q : XiZeroCopy) : (q.1 : ℂ) ≠ 0 := by
  intro h
  have hs := xi_divisor_support_re_mem_open_unit q.1
  rw [h] at hs
  norm_num at hs

private lemma d4XiRho_ne_two (q : XiZeroCopy) : (q.1 : ℂ) ≠ 2 := by
  intro h
  have hs := xi_divisor_support_re_mem_open_unit q.1
  rw [h] at hs
  norm_num at hs

private lemma d4XiRho_ne_neg_two (q : XiZeroCopy) : (q.1 : ℂ) ≠ -2 := by
  intro h
  have hs := xi_divisor_support_re_mem_open_unit q.1
  rw [h] at hs
  norm_num at hs

private lemma d4XiRho_ne_four (q : XiZeroCopy) : (q.1 : ℂ) ≠ 4 := by
  intro h
  have hs := xi_divisor_support_re_mem_open_unit q.1
  rw [h] at hs
  norm_num at hs

lemma d4ThetaTeukolskyAngularQ_xi_ne_zero (q : XiZeroCopy) :
    d4ThetaTeukolskyAngularQ (xiSpectralPoint q) ≠ 0 := by
  rw [d4ThetaTeukolskyAngularQ_eq_rho, d4ThetaTeukolskyRho_xiSpectralPoint]
  exact div_ne_zero
    (mul_ne_zero (d4XiRho_ne_zero q) (sub_ne_zero.mpr (d4XiRho_ne_two q).symm))
    (by norm_num)

lemma d4ThetaTeukolskyAngularQ_xi_add_two_ne_zero (q : XiZeroCopy) :
    d4ThetaTeukolskyAngularQ (xiSpectralPoint q) + 2 ≠ 0 := by
  rw [d4ThetaTeukolskyAngularQ_eq_rho, d4ThetaTeukolskyRho_xiSpectralPoint]
  have hfac :
      (q.1 : ℂ) * (2 - (q.1 : ℂ)) / 4 + 2 =
        -(((q.1 : ℂ) - 4) * ((q.1 : ℂ) + 2)) / 4 := by
    ring
  rw [hfac]
  exact div_ne_zero
    (neg_ne_zero.mpr
      (mul_ne_zero (sub_ne_zero.mpr (d4XiRho_ne_four q))
        (by
          simpa only [sub_neg_eq_add] using sub_ne_zero.mpr (d4XiRho_ne_neg_two q))))
    (by norm_num)

lemma d4FundamentalQNMContinuedRadialMoment_xi_ne_zero (q : XiZeroCopy) :
    d4FundamentalQNMContinuedRadialMoment (xiSpectralPoint q) ≠ 0 := by
  rw [d4FundamentalQNMContinuedRadialMoment_eq_neg_inv_Q]
  exact neg_ne_zero.mpr (inv_ne_zero (d4ThetaTeukolskyAngularQ_xi_ne_zero q))

/-- At actual divisor continued beta moment is explicit nonzero quotient 4/(rho(rho-2)). -/
theorem d4FundamentalQNMContinuedRadialMoment_xi_eq_rho (q : XiZeroCopy) :
    d4FundamentalQNMContinuedRadialMoment (xiSpectralPoint q) =
      4 / ((q.1 : ℂ) * ((q.1 : ℂ) - 2)) := by
  rw [d4FundamentalQNMContinuedRadialMoment_eq_neg_inv_Q,
    d4ThetaTeukolskyAngularQ_eq_rho, d4ThetaTeukolskyRho_xiSpectralPoint]
  field_simp [d4XiRho_ne_zero q, d4XiRho_ne_two q]
  simp only [one_div]
  rw [← inv_neg]
  congr 1
  ring

/-- Direct chiral source projection never vanishes on Xi divisor. -/
theorem d4FundamentalQNMChiralSourceKernel_xi_ne_zero (q : XiZeroCopy) :
    d4FundamentalQNMChiralSourceKernel (xiSpectralPoint q) ≠ 0 := by
  unfold d4FundamentalQNMChiralSourceKernel
  exact div_ne_zero
    (mul_ne_zero (by norm_num) (d4FundamentalQNMContinuedRadialMoment_xi_ne_zero q))
    (d4ThetaTeukolskyAngularQ_xi_add_two_ne_zero q)

/-- Normalized cubic horizon-backreaction source: one surviving seed amplitude times its
quadratic absorbed-mass shift times chiral QNM projection. -/
def d4FundamentalQNMNonlinearChiralSource (amplitude z : ℂ) : ℂ :=
  amplitude * (Complex.normSq amplitude : ℂ) *
    d4FundamentalQNMChiralSourceKernel z

lemma d4FundamentalQNMNonlinearChiralSource_shadow (amplitude z : ℂ) :
    d4FundamentalQNMNonlinearChiralSource amplitude
        (thetaCuspHawkingOpticalCuspShadow z) =
      d4FundamentalQNMNonlinearChiralSource amplitude z := by
  unfold d4FundamentalQNMNonlinearChiralSource
  rw [d4FundamentalQNMChiralSourceKernel_shadow]

/-- Every nonzero absorbed horizon mode produces nonzero fixed-angular-sector cross-helicity
return at every actual Xi divisor. This is not a transition between theta-shadow harmonics. -/
theorem d4FundamentalQNMNonlinearChiralSource_xi_ne_zero_iff
    (amplitude : ℂ) (q : XiZeroCopy) :
    d4FundamentalQNMNonlinearChiralSource amplitude (xiSpectralPoint q) ≠ 0 ↔
      amplitude ≠ 0 := by
  constructor
  · contrapose!
    rintro rfl
    simp [d4FundamentalQNMNonlinearChiralSource]
  · intro ha
    have hnormR : Complex.normSq amplitude ≠ 0 := by
      intro h
      exact ha (Complex.normSq_eq_zero.mp h)
    have hnormC : (Complex.normSq amplitude : ℂ) ≠ 0 := by
      exact_mod_cast hnormR
    exact mul_ne_zero (mul_ne_zero ha hnormC)
      (d4FundamentalQNMChiralSourceKernel_xi_ne_zero q)

/-- Complex AIME phase generated by quadratic horizon mass shift and common QNM frequency
jet. QNM frequencies are complex, so this is deliberately not called a unitary phase. -/
def d4HorizonBackreactionPhase (advancedTime : ℝ) (amplitude : ℂ)
    (horizonFrequencyJet : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp
    (-Complex.I * (advancedTime : ℂ) * (Complex.normSq amplitude : ℂ) *
      horizonFrequencyJet z)

lemma d4HorizonBackreactionPhase_ne_zero
    (advancedTime : ℝ) (amplitude : ℂ)
    (horizonFrequencyJet : ℂ → ℂ) (z : ℂ) :
    d4HorizonBackreactionPhase advancedTime amplitude horizonFrequencyJet z ≠ 0 := by
  exact Complex.exp_ne_zero _

/-- Exact returned Jost channel for fundamental normalized AIME component. -/
def d4FundamentalQNMNonlinearReturnedJost
    (advancedTime : ℝ) (amplitude : ℂ)
    (horizonFrequencyJet : ℂ → ℂ) (omega : ℂ) : ℂ → ℂ :=
  teukolskyReturnedJostWithHorizonPhase omega
    (fun z => d4HorizonBackreactionPhase advancedTime amplitude horizonFrequencyJet z *
      amplitude)
    (d4FundamentalQNMNonlinearChiralSource amplitude)

lemma d4FundamentalQNMNonlinearReturnedJost_qnmPlus
    (advancedTime : ℝ) (amplitude : ℂ)
    (horizonFrequencyJet : ℂ → ℂ) (q : XiZeroCopy) :
    d4FundamentalQNMNonlinearReturnedJost advancedTime amplitude horizonFrequencyJet
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q))
        (xiSpectralPoint q) =
      d4FundamentalQNMNonlinearChiralSource amplitude (xiSpectralPoint q) := by
  exact teukolskyReturnedJostWithHorizonPhase_qnmPlus 0 q _ _

/-- Horizon phase cancels at old pole; explicit cubic fixed-sector chiral source makes the
projective Evans wedge nonzero exactly for nonzero ingoing horizon mode. -/
theorem d4FundamentalQNMNonlinearReturnDeterminant_qnmPlus_ne_zero_iff
    (advancedTime : ℝ) (amplitude : ℂ)
    (horizonFrequencyJet : ℂ → ℂ) (q : XiZeroCopy) :
    teukolskyReturnDeterminant
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q))
        (d4FundamentalQNMNonlinearReturnedJost
          advancedTime amplitude horizonFrequencyJet
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q)))
        (xiSpectralPoint q) ≠ 0 ↔
      amplitude ≠ 0 := by
  rw [teukolskyReturnDeterminant_qnmPlus_ne_zero_iff,
    d4FundamentalQNMNonlinearReturnedJost_qnmPlus,
    d4FundamentalQNMNonlinearChiralSource_xi_ne_zero_iff]

/-- Canonical projective Cayley completion of the controlled nonlinear AIME return component. -/
def d4FundamentalQNMNonlinearCayleySMatrix
    (advancedTime : ℝ) (amplitude : ℂ)
    (horizonFrequencyJet : ℂ → ℂ) (omega z : ℂ) : ℂ :=
  teukolskyReturnCayleySMatrix omega
    (d4FundamentalQNMNonlinearReturnedJost
      advancedTime amplitude horizonFrequencyJet omega) z

/-- Exact theta-mirror law for the projective Cayley completion. This algebraic completion is not
identified here with the full angularly resolved gravitational S-matrix. -/
theorem d4FundamentalQNMNonlinearCayleySMatrix_shadow
    (advancedTime : ℝ) (amplitude : ℂ)
    (horizonFrequencyJet : ℂ → ℂ) (omega z : ℂ) :
    d4FundamentalQNMNonlinearCayleySMatrix
        advancedTime amplitude horizonFrequencyJet omega
        (thetaCuspHawkingOpticalCuspShadow z) =
      (d4FundamentalQNMNonlinearCayleySMatrix
        advancedTime amplitude horizonFrequencyJet omega z)⁻¹ := by
  exact teukolskyReturnCayleySMatrix_shadow omega _ z

/-- Completed return is nontrivial in every Xi sector exactly when physical horizon
amplitude is nonzero. -/
theorem d4FundamentalQNMNonlinearCayleySMatrix_qnmPlus_ne_one_iff
    (advancedTime : ℝ) (amplitude : ℂ)
    (horizonFrequencyJet : ℂ → ℂ) (q : XiZeroCopy) :
    d4FundamentalQNMNonlinearCayleySMatrix
        advancedTime amplitude horizonFrequencyJet
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q))
        (xiSpectralPoint q) ≠ 1 ↔
      amplitude ≠ 0 := by
  unfold d4FundamentalQNMNonlinearCayleySMatrix
    d4FundamentalQNMNonlinearReturnedJost
  exact (teukolskyReturnCayleySMatrix_qnmPlus_ne_one_iff_crossSource
    0 q _ _).trans
      (d4FundamentalQNMNonlinearChiralSource_xi_ne_zero_iff amplitude q)

/-- Strong projective form: any nonzero horizon mode makes the completed fundamental comparison
nontrivial at every Xi divisor. It does not assert inter-harmonic sector mixing. -/
theorem d4FundamentalQNMNonlinearCayleySMatrix_nontrivial_everyXi
    (advancedTime : ℝ) {amplitude : ℂ} (ha : amplitude ≠ 0)
    (horizonFrequencyJet : ℂ → ℂ) :
    ∀ q : XiZeroCopy,
      d4FundamentalQNMNonlinearCayleySMatrix
          advancedTime amplitude horizonFrequencyJet
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q))
          (xiSpectralPoint q) ≠ 1 := by
  intro q
  exact (d4FundamentalQNMNonlinearCayleySMatrix_qnmPlus_ne_one_iff
    advancedTime amplitude horizonFrequencyJet q).mpr ha

/-- Full projected cubic source split into exact AIME component and uncomputed third-order
`++-` Teukolsky remainder. -/
def d4FullNonlinearChiralSource
    (amplitude : ℂ) (thirdOrderTeukolskyRemainder : ℂ → ℂ) (z : ℂ) : ℂ :=
  d4FundamentalQNMNonlinearChiralSource amplitude z + thirdOrderTeukolskyRemainder z

/-- Returned Jost channel retaining entire unknown reduced-source remainder explicitly. -/
def d4FullNonlinearChiralReturnedJost
    (advancedTime : ℝ) (amplitude : ℂ)
    (horizonFrequencyJet thirdOrderTeukolskyRemainder : ℂ → ℂ) (omega : ℂ) : ℂ → ℂ :=
  teukolskyReturnedJostWithHorizonPhase omega
    (fun z => d4HorizonBackreactionPhase advancedTime amplitude horizonFrequencyJet z *
      amplitude)
    (d4FullNonlinearChiralSource amplitude thirdOrderTeukolskyRemainder)

/-- Sharp projective-source classification. At a divisor, the completed projective return can
erase the AIME component only through this exact pointwise counterterm. -/
theorem d4FullNonlinearChiralReturnDeterminant_qnmPlus_eq_zero_iff_counterterm
    (advancedTime : ℝ) (amplitude : ℂ)
    (horizonFrequencyJet thirdOrderTeukolskyRemainder : ℂ → ℂ) (q : XiZeroCopy) :
    teukolskyReturnDeterminant
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q))
        (d4FullNonlinearChiralReturnedJost
          advancedTime amplitude horizonFrequencyJet thirdOrderTeukolskyRemainder
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q)))
        (xiSpectralPoint q) = 0 ↔
      thirdOrderTeukolskyRemainder (xiSpectralPoint q) =
        -d4FundamentalQNMNonlinearChiralSource amplitude (xiSpectralPoint q) := by
  rw [teukolskyReturnDeterminant_qnmPlus]
  have hcomp := thetaCuspHawkingHypergeometricJostMinus_qnmPlus_ne_zero 0 q
  rw [mul_eq_zero]
  simp only [hcomp, or_false]
  rw [d4FullNonlinearChiralReturnedJost,
    teukolskyReturnedJostWithHorizonPhase_qnmPlus]
  change d4FullNonlinearChiralSource amplitude thirdOrderTeukolskyRemainder
      (xiSpectralPoint q) = 0 ↔ _
  unfold d4FullNonlinearChiralSource
  constructor <;> intro h <;> linear_combination h

end

end RHTower
