import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedDensityDeBrangesNoGo
import GaloisForLFunctions.RHTower.XiHurwitzFEAnchorCircuitCollision
import GaloisForLFunctions.RHTower.XiHadamardFactorization
import GaloisForLFunctions.RHTower.XiFirstDividedSourceNumericalSector

/-!
# Analytic--monodromy source-circuit fracture

The natural analytic and Hurwitz-monodromy realizations do not make an off-critical Xi zero into
a common circuit.  The completed-density realization has the fixed coefficient relation
`E + E# = 0` at every Xi divisor point, whereas the FE--Schwarz continued-Hurwitz pair is
differentially dependent exactly on the critical line.  Thus an off-critical zero is precisely a
failure to transport the represented analytic relation into the monodromy circuit.

This module formalizes the positive replacement for the false common-circuit proposal:
source-relation preservation is equivalent to absence of circuit fracture, and both are
equivalent to RH.  The theorem is a bridge, not a source proof: constructing the comparison from
the Euler--Gamma--theta source remains the open producer.
-/

open Complex

namespace RHTower

noncomputable section

/-- The centered spectral coordinate has imaginary part `1/2 - Re rho`. -/
theorem xiSpectralPointSupport_im_eq_half_sub_re (rho : XiDivisorSupport) :
    (xiSpectralPointSupport rho).im = 1 / 2 - (rho : ℂ).re := by
  simp [xiSpectralPointSupport, Complex.mul_im]

/-- Every Xi divisor point maps into the open strip where the completed-density split is valid. -/
theorem abs_im_xiSpectralPointSupport_lt_one (rho : XiDivisorSupport) :
    |(xiSpectralPointSupport rho).im| < 1 := by
  rw [xiSpectralPointSupport_im_eq_half_sub_re, abs_lt]
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  constructor <;> linarith

/-- XiC vanishes at the centered spectral coordinate of every Xi divisor point. -/
theorem XiC_xiSpectralPointSupport_eq_zero_sourceCircuit
    (rho : XiDivisorSupport) :
    XiC (xiSpectralPointSupport rho) = 0 :=
  XiC_xiSpectralPointSupport_eq_zero rho

/-- The coefficient-bearing completed-density relation at an Xi divisor point.  It is called a
relation rather than a matroid circuit because minimality and nonvanishing of the two coordinates
are not asserted. -/
def XiCompletedDensityReflectionRelationAt (rho : XiDivisorSupport) : Prop :=
  thetaCuspTailSecondDensityDeBrangesE (xiSpectralPointSupport rho) +
      thetaCuspTailSecondDensityDeBrangesESharp (xiSpectralPointSupport rho) = 0

/-- The Hurwitz-monodromy circuit selected by functional-equation and Schwarz reflection. -/
def XiHurwitzMonodromyCircuitAt (rho : XiDivisorSupport) : Prop :=
  ContinuedHurwitzPairDifferentiallyDependent
    (1 - (rho : ℂ)) ((starRingEnd ℂ) (rho : ℂ))

/-- A source-comparison fracture: the analytic relation exists but its Hurwitz monodromy image is
not a circuit. -/
def XiSourceCircuitFractureAt (rho : XiDivisorSupport) : Prop :=
  XiCompletedDensityReflectionRelationAt rho ∧
    ¬ XiHurwitzMonodromyCircuitAt rho

/-- Every represented analytic zero relation transports to the Hurwitz monodromy circuit. -/
def XiSourceCircuitComparisonPreserving : Prop :=
  ∀ rho : XiDivisorSupport,
    XiCompletedDensityReflectionRelationAt rho →
      XiHurwitzMonodromyCircuitAt rho

/-- No Xi divisor point carries an analytic--monodromy source-circuit fracture. -/
def XiSourceCircuitFractureFree : Prop :=
  ∀ rho : XiDivisorSupport, ¬ XiSourceCircuitFractureAt rho

/-- Every Xi divisor point carries the fixed completed-density reflection relation. -/
theorem xiCompletedDensityReflectionRelationAt_all (rho : XiDivisorSupport) :
    XiCompletedDensityReflectionRelationAt rho := by
  unfold XiCompletedDensityReflectionRelationAt
  calc
    thetaCuspTailSecondDensityDeBrangesE (xiSpectralPointSupport rho) +
        thetaCuspTailSecondDensityDeBrangesESharp (xiSpectralPointSupport rho) =
      4 * (xiSpectralPointSupport rho) ^ 2 *
        XiC (xiSpectralPointSupport rho) :=
      thetaCuspTailSecondDensityDeBrangesE_add_sharp
        (abs_im_xiSpectralPointSupport_lt_one rho)
    _ = 0 := by rw [XiC_xiSpectralPointSupport_eq_zero_sourceCircuit, mul_zero]

/-- The monodromy circuit occurs exactly on the critical line. -/
theorem xiHurwitzMonodromyCircuitAt_iff_re_eq_half (rho : XiDivisorSupport) :
    XiHurwitzMonodromyCircuitAt rho ↔ (rho : ℂ).re = 1 / 2 := by
  unfold XiHurwitzMonodromyCircuitAt
  exact continuedHurwitzFESchwarzPairDifferentiallyDependent_iff_re_eq_half
    (xi_divisor_support_re_mem_open_unit rho)

/-- **Pointwise fracture law.**  An Xi divisor point is a source-circuit fracture exactly when it
is off the critical line. -/
theorem xiSourceCircuitFractureAt_iff_re_ne_half (rho : XiDivisorSupport) :
    XiSourceCircuitFractureAt rho ↔ (rho : ℂ).re ≠ 1 / 2 := by
  constructor
  · rintro ⟨_, hnot⟩ hre
    exact hnot ((xiHurwitzMonodromyCircuitAt_iff_re_eq_half rho).mpr hre)
  · intro hne
    refine ⟨xiCompletedDensityReflectionRelationAt_all rho, ?_⟩
    intro hcircuit
    exact hne ((xiHurwitzMonodromyCircuitAt_iff_re_eq_half rho).mp hcircuit)

/-- Relation preservation is exactly absence of source-circuit fractures. -/
theorem xiSourceCircuitComparisonPreserving_iff_fractureFree :
    XiSourceCircuitComparisonPreserving ↔ XiSourceCircuitFractureFree := by
  constructor
  · intro hpres rho hfracture
    exact hfracture.2 (hpres rho hfracture.1)
  · intro hfree rho hrelation
    by_contra hnot
    exact hfree rho ⟨hrelation, hnot⟩

/-- **Global transport criterion.**  Preservation of every completed-density zero relation in
the Hurwitz monodromy realization is equivalent to RH. -/
theorem xiSourceCircuitComparisonPreserving_iff_riemannHypothesis :
    XiSourceCircuitComparisonPreserving ↔ RiemannHypothesis := by
  constructor
  · intro hpres
    apply xiHurwitzFESchwarzPairCircuit_iff_riemannHypothesis.mp
    intro rho
    exact hpres rho (xiCompletedDensityReflectionRelationAt_all rho)
  · intro hRH rho _
    exact (xiHurwitzFESchwarzPairCircuit_iff_riemannHypothesis.mpr hRH) rho

/-- **Global fracture criterion.**  The analytic--monodromy source comparison is fracture-free
exactly when RH holds. -/
theorem xiSourceCircuitFractureFree_iff_riemannHypothesis :
    XiSourceCircuitFractureFree ↔ RiemannHypothesis :=
  xiSourceCircuitComparisonPreserving_iff_fractureFree.symm.trans
    xiSourceCircuitComparisonPreserving_iff_riemannHypothesis

/-- The positive derivative-drop mass canonically orients the analytic odd boundary channel while
the global comparison remains exactly the fracture-free/RH condition. -/
theorem xiSourceCircuitFractureOrientationLaw :
    0 < thetaCuspTailThirdDerivativeDropMass ∧
      (XiSourceCircuitFractureFree ↔ RiemannHypothesis) :=
  ⟨thetaCuspTailThirdDerivativeDropMass_pos,
    xiSourceCircuitFractureFree_iff_riemannHypothesis⟩

end

end RHTower
