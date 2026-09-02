import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompletedBalancedSpinTwoExternalLegNoGo
import GaloisForLFunctions.RHTower.XiHedenmalmMultiplicityChain
import GaloisForLFunctions.RHTower.ReflectedBiHeatMultiplicityTomography
import GaloisForLFunctions.HTGeometry.AffineFluxTaylorCoeff

/-!
# Exact external-leg amputation order for the completed balanced spin-two source

Let `m` be the support multiplicity of the Xi zero attached to a projecting leg.
The completed external Xi factor has first nonzero jet in order `m`; its diagonal
square therefore has first nonzero jet in order `2m`.  Consequently every
derivative-amputated completed balanced spin-two source of order below `2m` is
dark on that leg and leaves the nonzero opposite-branch AIME pole uncancelled.
This kills the full subcritical derivative-amputation class, including ordinary
first-derivative LSZ amputation.

The first possible survivor is classified exactly: the order-`2m` vertex jet is
nonzero iff the explicit Bochner/two-shifted-Xi side factor is nonzero.
-/

open Complex Real Filter Topology

namespace RHTower

noncomputable section

abbrev d4BMXiProjectingLegMultiplicity (q : XiZeroCopy) : ℕ :=
  xiSupportMultiplicity q.1

theorem analyticAt_thetaCuspHawkingCompletedEisensteinXiFactor (v : ℂ) :
    AnalyticAt ℂ thetaCuspHawkingCompletedEisensteinXiFactor v := by
  unfold thetaCuspHawkingCompletedEisensteinXiFactor
  exact (XiC_analytic _ (Set.mem_univ _)).comp (by fun_prop)

theorem iteratedDeriv_thetaCuspHawkingCompletedEisensteinXiFactor_projectingXi
    (q : XiZeroCopy) (k : ℕ) :
    iteratedDeriv k thetaCuspHawkingCompletedEisensteinXiFactor
        (d4BMXiProjectingEisensteinCenteredParameter q) =
      (-Complex.I) ^ k * iteratedDeriv k XiC (xiSpectralPoint q) := by
  unfold thetaCuspHawkingCompletedEisensteinXiFactor
  rw [GaloisForLFunctions.HTGeometry.iteratedDeriv_comp_const_mul_of_ne
    XiC k (neg_ne_zero.mpr Complex.I_ne_zero)]
  congr 2
  unfold d4BMXiProjectingEisensteinCenteredParameter
  calc
    -Complex.I * (Complex.I * xiSpectralPoint q) =
        -(Complex.I * Complex.I) * xiSpectralPoint q := by ring
    _ = xiSpectralPoint q := by rw [Complex.I_mul_I]; ring

theorem iteratedDeriv_thetaCuspHawkingCompletedEisensteinXiFactor_projectingXi_eq_zero
    (q : XiZeroCopy) {k : ℕ} (hk : k < d4BMXiProjectingLegMultiplicity q) :
    iteratedDeriv k thetaCuspHawkingCompletedEisensteinXiFactor
        (d4BMXiProjectingEisensteinCenteredParameter q) = 0 := by
  rw [iteratedDeriv_thetaCuspHawkingCompletedEisensteinXiFactor_projectingXi]
  have hzero := iteratedDeriv_XiC_eq_zero_before_supportMultiplicity q.1 hk
  rw [← xiSpectralPoint_eq_support q] at hzero
  rw [hzero, mul_zero]

theorem iteratedDeriv_thetaCuspHawkingCompletedEisensteinXiFactor_projectingXi_ne_zero
    (q : XiZeroCopy) :
    iteratedDeriv (d4BMXiProjectingLegMultiplicity q)
        thetaCuspHawkingCompletedEisensteinXiFactor
        (d4BMXiProjectingEisensteinCenteredParameter q) ≠ 0 := by
  rw [iteratedDeriv_thetaCuspHawkingCompletedEisensteinXiFactor_projectingXi]
  apply mul_ne_zero
  · exact pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)
  · rw [xiSpectralPoint_eq_support]
    exact iteratedDeriv_XiC_ne_zero_at_supportMultiplicity q.1

def d4BMCompletedEisensteinProjectingExternalSquare (v : ℂ) : ℂ :=
  thetaCuspHawkingCompletedEisensteinXiFactor v *
    thetaCuspHawkingCompletedEisensteinXiFactor v

theorem analyticAt_d4BMCompletedEisensteinProjectingExternalSquare (v : ℂ) :
    AnalyticAt ℂ d4BMCompletedEisensteinProjectingExternalSquare v := by
  exact (analyticAt_thetaCuspHawkingCompletedEisensteinXiFactor v).mul
    (analyticAt_thetaCuspHawkingCompletedEisensteinXiFactor v)

theorem iteratedDeriv_d4BMCompletedEisensteinProjectingExternalSquare_eq_zero
    (q : XiZeroCopy) {k : ℕ}
    (hk : k < 2 * d4BMXiProjectingLegMultiplicity q) :
    iteratedDeriv k d4BMCompletedEisensteinProjectingExternalSquare
        (d4BMXiProjectingEisensteinCenteredParameter q) = 0 := by
  change iteratedDeriv k
      (fun v : ℂ => thetaCuspHawkingCompletedEisensteinXiFactor v *
        thetaCuspHawkingCompletedEisensteinXiFactor v)
      (d4BMXiProjectingEisensteinCenteredParameter q) = 0
  have hcont : ContDiffAt ℂ k thetaCuspHawkingCompletedEisensteinXiFactor
      (d4BMXiProjectingEisensteinCenteredParameter q) :=
    (analyticAt_thetaCuspHawkingCompletedEisensteinXiFactor _).contDiffAt
  exact complex_iteratedDeriv_mul_eq_zero_before_add_order hcont hcont
    (fun j hj =>
      iteratedDeriv_thetaCuspHawkingCompletedEisensteinXiFactor_projectingXi_eq_zero
        q hj)
    (fun j hj =>
      iteratedDeriv_thetaCuspHawkingCompletedEisensteinXiFactor_projectingXi_eq_zero
        q hj)
    (by simpa [two_mul] using hk)

theorem iteratedDeriv_d4BMCompletedEisensteinProjectingExternalSquare_at_twiceMultiplicity
    (q : XiZeroCopy) :
    iteratedDeriv (2 * d4BMXiProjectingLegMultiplicity q)
        d4BMCompletedEisensteinProjectingExternalSquare
        (d4BMXiProjectingEisensteinCenteredParameter q) =
      (Nat.choose (2 * d4BMXiProjectingLegMultiplicity q)
          (d4BMXiProjectingLegMultiplicity q) : ℂ) *
        iteratedDeriv (d4BMXiProjectingLegMultiplicity q)
          thetaCuspHawkingCompletedEisensteinXiFactor
          (d4BMXiProjectingEisensteinCenteredParameter q) *
        iteratedDeriv (d4BMXiProjectingLegMultiplicity q)
          thetaCuspHawkingCompletedEisensteinXiFactor
          (d4BMXiProjectingEisensteinCenteredParameter q) := by
  change iteratedDeriv (2 * d4BMXiProjectingLegMultiplicity q)
      (fun v : ℂ => thetaCuspHawkingCompletedEisensteinXiFactor v *
        thetaCuspHawkingCompletedEisensteinXiFactor v)
      (d4BMXiProjectingEisensteinCenteredParameter q) = _
  rw [show 2 * d4BMXiProjectingLegMultiplicity q =
      d4BMXiProjectingLegMultiplicity q + d4BMXiProjectingLegMultiplicity q by ring]
  exact complex_iteratedDeriv_mul_at_add_order
    (analyticAt_thetaCuspHawkingCompletedEisensteinXiFactor _).contDiffAt
    (analyticAt_thetaCuspHawkingCompletedEisensteinXiFactor _).contDiffAt
    (fun j hj =>
      iteratedDeriv_thetaCuspHawkingCompletedEisensteinXiFactor_projectingXi_eq_zero
        q hj)
    (fun j hj =>
      iteratedDeriv_thetaCuspHawkingCompletedEisensteinXiFactor_projectingXi_eq_zero
        q hj)

theorem iteratedDeriv_d4BMCompletedEisensteinProjectingExternalSquare_ne_zero
    (q : XiZeroCopy) :
    iteratedDeriv (2 * d4BMXiProjectingLegMultiplicity q)
        d4BMCompletedEisensteinProjectingExternalSquare
        (d4BMXiProjectingEisensteinCenteredParameter q) ≠ 0 := by
  rw [iteratedDeriv_d4BMCompletedEisensteinProjectingExternalSquare_at_twiceMultiplicity]
  have hchoose : (Nat.choose (2 * d4BMXiProjectingLegMultiplicity q)
      (d4BMXiProjectingLegMultiplicity q) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : d4BMXiProjectingLegMultiplicity q ≤
      2 * d4BMXiProjectingLegMultiplicity q)).ne'
  exact mul_ne_zero
    (mul_ne_zero hchoose
      (iteratedDeriv_thetaCuspHawkingCompletedEisensteinXiFactor_projectingXi_ne_zero q))
    (iteratedDeriv_thetaCuspHawkingCompletedEisensteinXiFactor_projectingXi_ne_zero q)

def d4BMCompletedBalancedSpinTwoProjectingSideFactor (u v : ℂ) : ℂ :=
  thetaCuspHawkingBalancedSpinTwoBochnerCoefficient u v *
    thetaCuspHawkingCompletedEisensteinXiFactor (2 * u + v) *
    thetaCuspHawkingCompletedEisensteinXiFactor (2 * u - v)

theorem thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_eq_externalSquare_mul_side
    (u v : ℂ) :
    thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex u v =
      d4BMCompletedEisensteinProjectingExternalSquare v *
        d4BMCompletedBalancedSpinTwoProjectingSideFactor u v := by
  rw [thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_eq,
    thetaCuspHawkingDiagonalCompletedEisensteinCubicVertex_factorization]
  simp only [d4BMCompletedEisensteinProjectingExternalSquare,
    d4BMCompletedBalancedSpinTwoProjectingSideFactor]
  ring

theorem analyticAt_d4BMCompletedBalancedSpinTwoProjectingSideFactor (u v : ℂ) :
    AnalyticAt ℂ (d4BMCompletedBalancedSpinTwoProjectingSideFactor u) v := by
  have hcoeff : AnalyticAt ℂ
      (fun w : ℂ => thetaCuspHawkingBalancedSpinTwoBochnerCoefficient u w) v := by
    unfold thetaCuspHawkingBalancedSpinTwoBochnerCoefficient
      thetaCuspHawkingEisensteinGeometricEigenvalue
      d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
      d4BMHyperbolicDiagonalGradientShift
    fun_prop
  have hplus : AnalyticAt ℂ
      (fun w : ℂ => thetaCuspHawkingCompletedEisensteinXiFactor (2 * u + w)) v :=
    (analyticAt_thetaCuspHawkingCompletedEisensteinXiFactor _).comp (by fun_prop)
  have hminus : AnalyticAt ℂ
      (fun w : ℂ => thetaCuspHawkingCompletedEisensteinXiFactor (2 * u - w)) v :=
    (analyticAt_thetaCuspHawkingCompletedEisensteinXiFactor _).comp (by fun_prop)
  exact (hcoeff.mul hplus).mul hminus

theorem iteratedDeriv_thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_eq_zero_before_twiceMultiplicity
    (u : ℂ) (q : XiZeroCopy) {k : ℕ}
    (hk : k < 2 * d4BMXiProjectingLegMultiplicity q) :
    iteratedDeriv k
        (fun v : ℂ => thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex u v)
        (d4BMXiProjectingEisensteinCenteredParameter q) = 0 := by
  rw [show (fun v : ℂ => thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex u v) =
      fun v : ℂ => d4BMCompletedEisensteinProjectingExternalSquare v *
        d4BMCompletedBalancedSpinTwoProjectingSideFactor u v by
    funext v
    exact thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_eq_externalSquare_mul_side u v]
  exact complex_iteratedDeriv_mul_eq_zero_before_add_order
    (analyticAt_d4BMCompletedEisensteinProjectingExternalSquare _).contDiffAt
    (analyticAt_d4BMCompletedBalancedSpinTwoProjectingSideFactor u _).contDiffAt
    (fun j hj =>
      iteratedDeriv_d4BMCompletedEisensteinProjectingExternalSquare_eq_zero q hj)
    (fun j hj => (Nat.not_lt_zero j hj).elim)
    (by simpa using hk)

theorem iteratedDeriv_thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_at_twiceMultiplicity
    (u : ℂ) (q : XiZeroCopy) :
    iteratedDeriv (2 * d4BMXiProjectingLegMultiplicity q)
        (fun v : ℂ => thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex u v)
        (d4BMXiProjectingEisensteinCenteredParameter q) =
      iteratedDeriv (2 * d4BMXiProjectingLegMultiplicity q)
          d4BMCompletedEisensteinProjectingExternalSquare
          (d4BMXiProjectingEisensteinCenteredParameter q) *
        d4BMCompletedBalancedSpinTwoProjectingSideFactor u
          (d4BMXiProjectingEisensteinCenteredParameter q) := by
  rw [show (fun v : ℂ => thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex u v) =
      fun v : ℂ => d4BMCompletedEisensteinProjectingExternalSquare v *
        d4BMCompletedBalancedSpinTwoProjectingSideFactor u v by
    funext v
    exact thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_eq_externalSquare_mul_side u v]
  exact complex_iteratedDeriv_mul_of_left_vanishing_below
    (2 * d4BMXiProjectingLegMultiplicity q)
    (analyticAt_d4BMCompletedEisensteinProjectingExternalSquare _).contDiffAt
    (analyticAt_d4BMCompletedBalancedSpinTwoProjectingSideFactor u _).contDiffAt
    (fun j hj =>
      iteratedDeriv_d4BMCompletedEisensteinProjectingExternalSquare_eq_zero q hj)

theorem iteratedDeriv_thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_ne_zero_iff_side
    (u : ℂ) (q : XiZeroCopy) :
    iteratedDeriv (2 * d4BMXiProjectingLegMultiplicity q)
        (fun v : ℂ => thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex u v)
        (d4BMXiProjectingEisensteinCenteredParameter q) ≠ 0 ↔
      d4BMCompletedBalancedSpinTwoProjectingSideFactor u
          (d4BMXiProjectingEisensteinCenteredParameter q) ≠ 0 := by
  rw [iteratedDeriv_thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_at_twiceMultiplicity]
  exact mul_ne_zero_iff.trans
    (and_iff_right
      (iteratedDeriv_d4BMCompletedEisensteinProjectingExternalSquare_ne_zero q))

def d4BMDerivativeAmputatedCompletedBalancedSpinTwoSamePoleRemainder
    (k : ℕ) (radialLeftScale repeatedPositiveLeg : ℂ → ℂ) (z : ℂ) : ℂ :=
  radialLeftScale z *
    iteratedDeriv k
      (fun v : ℂ => thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex
        (repeatedPositiveLeg z) v)
      (Complex.I * z)

theorem d4BMDerivativeAmputatedCompletedBalancedSpinTwoSamePoleRemainder_xi_eq_zero
    (k : ℕ) (radialLeftScale repeatedPositiveLeg : ℂ → ℂ) (q : XiZeroCopy)
    (hk : k < 2 * d4BMXiProjectingLegMultiplicity q) :
    d4BMDerivativeAmputatedCompletedBalancedSpinTwoSamePoleRemainder
        k radialLeftScale repeatedPositiveLeg (xiSpectralPoint q) = 0 := by
  unfold d4BMDerivativeAmputatedCompletedBalancedSpinTwoSamePoleRemainder
  change radialLeftScale (xiSpectralPoint q) *
      iteratedDeriv k
        (fun v : ℂ => thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex
          (repeatedPositiveLeg (xiSpectralPoint q)) v)
        (d4BMXiProjectingEisensteinCenteredParameter q) = 0
  rw [iteratedDeriv_thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_eq_zero_before_twiceMultiplicity
    _ q hk, mul_zero]

theorem d4BMFirstDerivativeAmputatedCompletedBalancedSpinTwoSamePoleRemainder_xi_eq_zero
    (radialLeftScale repeatedPositiveLeg : ℂ → ℂ) (q : XiZeroCopy) :
    d4BMDerivativeAmputatedCompletedBalancedSpinTwoSamePoleRemainder
        1 radialLeftScale repeatedPositiveLeg (xiSpectralPoint q) = 0 := by
  apply d4BMDerivativeAmputatedCompletedBalancedSpinTwoSamePoleRemainder_xi_eq_zero
  have hm := xiSupportMultiplicity_pos q.1
  have hm1 : 1 ≤ d4BMXiProjectingLegMultiplicity q := hm
  calc
    1 < 2 * 1 := by norm_num
    _ ≤ 2 * d4BMXiProjectingLegMultiplicity q := Nat.mul_le_mul_left 2 hm1

theorem d4BMDerivativeAmputatedCompletedBalancedSpinTwoSamePoleRemainder_ne_forcedCounterterm
    {amplitude : ℂ} (hamplitude : amplitude ≠ 0)
    (k : ℕ) (radialLeftScale repeatedPositiveLeg : ℂ → ℂ) (q : XiZeroCopy)
    (hk : k < 2 * d4BMXiProjectingLegMultiplicity q) :
    d4BMDerivativeAmputatedCompletedBalancedSpinTwoSamePoleRemainder
        k radialLeftScale repeatedPositiveLeg (xiSpectralPoint q) ≠
      -d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) := by
  rw [d4BMDerivativeAmputatedCompletedBalancedSpinTwoSamePoleRemainder_xi_eq_zero
    k radialLeftScale repeatedPositiveLeg q hk]
  exact (neg_ne_zero.mpr
    ((d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude q).mpr
      hamplitude)).symm

theorem d4BMDerivativeAmputatedCompletedBalancedSpinTwoPole_order_qnmMinus_xi
    {amplitude : ℂ} (hamplitude : amplitude ≠ 0)
    (k : ℕ) (radialLeftScale repeatedPositiveLeg : ℂ → ℂ) (q : XiZeroCopy)
    (hk : k < 2 * d4BMXiProjectingLegMultiplicity q) :
    meromorphicOrderAt
      (fun omega : ℂ =>
        d4FullCrossBranchPolePrincipalPart amplitude
          (d4BMDerivativeAmputatedCompletedBalancedSpinTwoSamePoleRemainder
            k radialLeftScale repeatedPositiveLeg)
          (xiSpectralPoint q) omega)
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)) =
        ((-1 : ℤ) : WithTop ℤ) := by
  exact (d4FullCrossBranchPolePrincipalPart_order_qnmMinus_xi_iff
    amplitude
    (d4BMDerivativeAmputatedCompletedBalancedSpinTwoSamePoleRemainder
      k radialLeftScale repeatedPositiveLeg) q).mpr
      (d4BMDerivativeAmputatedCompletedBalancedSpinTwoSamePoleRemainder_ne_forcedCounterterm
        hamplitude k radialLeftScale repeatedPositiveLeg q hk)

theorem d4HBDerivativeAmputatedCompletedBalancedSpinTwoSourceRouteKilled
    (k n : ℕ) {amplitude : ℂ} (hamplitude : amplitude ≠ 0)
    (q : XiZeroCopy) (radialLeftScale repeatedPositiveLeg : ℂ → ℂ)
    (hk : k < 2 * d4BMXiProjectingLegMultiplicity q)
    (hline : (q.1 : ℂ).re = 1 / 2) :
    d4FullCrossBranchProjectedResidue amplitude
        (d4BMDerivativeAmputatedCompletedBalancedSpinTwoSamePoleRemainder
          k radialLeftScale repeatedPositiveLeg)
        (xiSpectralPoint q) ≠
      d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q := by
  intro hmatch
  have hremainder :=
    d4FullCrossBranch_samePoleSourceRemainder_ne_zero_of_unitBMTarget_of_criticalLine
      n hamplitude
      (d4BMDerivativeAmputatedCompletedBalancedSpinTwoSamePoleRemainder
        k radialLeftScale repeatedPositiveLeg)
      q hline hmatch
  exact hremainder
    (d4BMDerivativeAmputatedCompletedBalancedSpinTwoSamePoleRemainder_xi_eq_zero
      k radialLeftScale repeatedPositiveLeg q hk)

theorem d4HBFirstDerivativeAmputatedCompletedBalancedSpinTwoSourceRouteKilled :
    ∀ (n : ℕ) {amplitude : ℂ}, amplitude ≠ 0 →
      ∀ (q : XiZeroCopy) (radialLeftScale repeatedPositiveLeg : ℂ → ℂ),
        (q.1 : ℂ).re = 1 / 2 →
        d4FullCrossBranchProjectedResidue amplitude
            (d4BMDerivativeAmputatedCompletedBalancedSpinTwoSamePoleRemainder
              1 radialLeftScale repeatedPositiveLeg)
            (xiSpectralPoint q) ≠
          d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q := by
  intro n amplitude hamplitude q radialLeftScale repeatedPositiveLeg hline
  apply d4HBDerivativeAmputatedCompletedBalancedSpinTwoSourceRouteKilled
    1 n hamplitude q radialLeftScale repeatedPositiveLeg
  · have hm := xiSupportMultiplicity_pos q.1
    have hm1 : 1 ≤ d4BMXiProjectingLegMultiplicity q := hm
    calc
      1 < 2 * 1 := by norm_num
      _ ≤ 2 * d4BMXiProjectingLegMultiplicity q := Nat.mul_le_mul_left 2 hm1
  · exact hline

end

end RHTower
