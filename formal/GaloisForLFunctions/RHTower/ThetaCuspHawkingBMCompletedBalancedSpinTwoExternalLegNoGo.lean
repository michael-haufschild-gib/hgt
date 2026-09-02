import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompletedBalancedSpinTwoEisensteinVertex
import GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEBMGlobalSourceIncompatibility

/-!
# External-leg obstruction for the completed balanced spin-two HB source

The corpus completed Plebanski--Maass projection is the canonical balanced spin-two Eisenstein
vertex.  Its projecting Eisenstein parameter on an actual Xi fibre is

`v = rho - 1/2 = I * xiSpectralPoint q`.

The diagonal four-Xi factorization contains the projecting factor twice.  Hence the unamputated
completed vertex is annihilated on shell by

`thetaXi(v)^2 = XiC(xiSpectralPoint q)^2 = 0`.

This is unaffected by the repeated positive leg or by any multiplicative radial Green/left-QNM
response.  A nonzero AIME seed therefore retains its exact simple negative-branch QNM pole, and on
a critical Xi fibre the resulting projected residue cannot equal the unit BM boundary target.

Thus the canonical **unamputated** completed balanced spin-two source route is closed.  Any HB
survivor using this angular vertex must first remove the external Xi zero by a derivative/residue
amputation, or supply a non-factorizing source-to-left-QNM incidence.  Merely changing radial
normalization cannot help.

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [HB ROUTE KILL] [EXTERNAL-LEG OBSTRUCTION]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Centered Eisenstein parameter `rho - 1/2` of an actual Xi projecting leg. -/
def d4BMXiProjectingEisensteinCenteredParameter (q : XiZeroCopy) : ℂ :=
  Complex.I * xiSpectralPoint q

/-- The spectral-coordinate definition recovers the literal centered zero. -/
theorem d4BMXiProjectingEisensteinCenteredParameter_eq (q : XiZeroCopy) :
    d4BMXiProjectingEisensteinCenteredParameter q = (q.1 : ℂ) - 1 / 2 := by
  unfold d4BMXiProjectingEisensteinCenteredParameter xiSpectralPoint
  rw [show Complex.I * (((q.1 : ℂ) - 1 / 2) * -Complex.I) =
      ((q.1 : ℂ) - 1 / 2) * (Complex.I * -Complex.I) by ring]
  rw [mul_neg, Complex.I_mul_I]
  ring

/-- The pole-filled completed factor on an actual Xi projecting leg vanishes. -/
theorem thetaCuspHawkingCompletedEisensteinXiFactor_projectingXi_eq_zero
    (q : XiZeroCopy) :
    thetaCuspHawkingCompletedEisensteinXiFactor
        (d4BMXiProjectingEisensteinCenteredParameter q) = 0 := by
  unfold thetaCuspHawkingCompletedEisensteinXiFactor
    d4BMXiProjectingEisensteinCenteredParameter
  rw [show -Complex.I * (Complex.I * xiSpectralPoint q) = xiSpectralPoint q by
      calc
        -Complex.I * (Complex.I * xiSpectralPoint q) =
            -(Complex.I * Complex.I) * xiSpectralPoint q := by ring
        _ = xiSpectralPoint q := by rw [Complex.I_mul_I]; ring]
  exact XiC_xiSpectralPoint_eq_zero q

/-- The two external Xi factors of the on-shell projecting leg annihilate the canonical balanced
spin-two vertex for every repeated positive-leg parameter. -/
theorem thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_projectingXi_eq_zero
    (u : ℂ) (q : XiZeroCopy) :
    thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex u
        (d4BMXiProjectingEisensteinCenteredParameter q) = 0 := by
  rw [thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_eq,
    thetaCuspHawkingDiagonalCompletedEisensteinCubicVertex_factorization,
    thetaCuspHawkingCompletedEisensteinXiFactor_projectingXi_eq_zero]
  simp

/-- Unamputated HB route class: arbitrary multiplicative radial/left response applied to the
canonical completed balanced spin-two angular vertex. -/
def d4BMUnamputatedCompletedBalancedSpinTwoSamePoleRemainder
    (radialLeftScale repeatedPositiveLeg : ℂ → ℂ) (z : ℂ) : ℂ :=
  radialLeftScale z *
    thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex
      (repeatedPositiveLeg z) (Complex.I * z)

/-- Arbitrary radial/left multiplication cannot remove the projecting external-leg zero. -/
theorem d4BMUnamputatedCompletedBalancedSpinTwoSamePoleRemainder_xi_eq_zero
    (radialLeftScale repeatedPositiveLeg : ℂ → ℂ) (q : XiZeroCopy) :
    d4BMUnamputatedCompletedBalancedSpinTwoSamePoleRemainder
        radialLeftScale repeatedPositiveLeg (xiSpectralPoint q) = 0 := by
  rw [d4BMUnamputatedCompletedBalancedSpinTwoSamePoleRemainder]
  change radialLeftScale (xiSpectralPoint q) *
      thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex
        (repeatedPositiveLeg (xiSpectralPoint q))
        (d4BMXiProjectingEisensteinCenteredParameter q) = 0
  rw [thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_projectingXi_eq_zero]
  simp

/-- For a nonzero seed, the unamputated completed source cannot equal the unique negative AIME
counterterm demanded at the same pole. -/
theorem d4BMUnamputatedCompletedBalancedSpinTwoSamePoleRemainder_ne_forcedCounterterm
    {amplitude : ℂ} (hamplitude : amplitude ≠ 0)
    (radialLeftScale repeatedPositiveLeg : ℂ → ℂ) (q : XiZeroCopy) :
    d4BMUnamputatedCompletedBalancedSpinTwoSamePoleRemainder
        radialLeftScale repeatedPositiveLeg (xiSpectralPoint q) ≠
      -d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) := by
  rw [d4BMUnamputatedCompletedBalancedSpinTwoSamePoleRemainder_xi_eq_zero]
  exact (neg_ne_zero.mpr
    ((d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude q).mpr
      hamplitude)).symm

/-- **Unconditional pole survivor.** For every Xi fibre and every nonzero AIME seed, the full
response using any unamputated completed balanced spin-two source retains the exact simple
negative-branch QNM pole. -/
theorem d4BMUnamputatedCompletedBalancedSpinTwoPole_order_qnmMinus_xi
    {amplitude : ℂ} (hamplitude : amplitude ≠ 0)
    (radialLeftScale repeatedPositiveLeg : ℂ → ℂ) (q : XiZeroCopy) :
    meromorphicOrderAt
      (fun omega : ℂ =>
        d4FullCrossBranchPolePrincipalPart amplitude
          (d4BMUnamputatedCompletedBalancedSpinTwoSamePoleRemainder
            radialLeftScale repeatedPositiveLeg)
          (xiSpectralPoint q) omega)
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)) =
        ((-1 : ℤ) : WithTop ℤ) := by
  exact (d4FullCrossBranchPolePrincipalPart_order_qnmMinus_xi_iff
    amplitude
    (d4BMUnamputatedCompletedBalancedSpinTwoSamePoleRemainder
      radialLeftScale repeatedPositiveLeg) q).mpr
      (d4BMUnamputatedCompletedBalancedSpinTwoSamePoleRemainder_ne_forcedCounterterm
        hamplitude radialLeftScale repeatedPositiveLeg q)

/-- **HB route kill.** On every critical Xi fibre, the canonical unamputated completed balanced
spin-two source fails the exact unit BM incidence, for arbitrary repeated leg and arbitrary
multiplicative radial/left-QNM response. -/
theorem d4HBUnamputatedCompletedBalancedSpinTwoSourceRouteKilled :
    ∀ (n : ℕ) {amplitude : ℂ}, amplitude ≠ 0 →
      ∀ (q : XiZeroCopy) (radialLeftScale repeatedPositiveLeg : ℂ → ℂ),
        (q.1 : ℂ).re = 1 / 2 →
        d4FullCrossBranchProjectedResidue amplitude
            (d4BMUnamputatedCompletedBalancedSpinTwoSamePoleRemainder
              radialLeftScale repeatedPositiveLeg)
            (xiSpectralPoint q) ≠
          d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q := by
  intro n amplitude hamplitude q radialLeftScale repeatedPositiveLeg hline hmatch
  have hremainder :=
    d4FullCrossBranch_samePoleSourceRemainder_ne_zero_of_unitBMTarget_of_criticalLine
      n hamplitude
      (d4BMUnamputatedCompletedBalancedSpinTwoSamePoleRemainder
        radialLeftScale repeatedPositiveLeg)
      q hline hmatch
  exact hremainder
    (d4BMUnamputatedCompletedBalancedSpinTwoSamePoleRemainder_xi_eq_zero
      radialLeftScale repeatedPositiveLeg q)

end

end RHTower
