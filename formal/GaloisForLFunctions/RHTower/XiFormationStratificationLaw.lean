import GaloisForLFunctions.RHTower.XiFormationEscapePrincipalClassLaw
import GaloisForLFunctions.RHTower.XiStableClassCentralAnomalyTransgression
import GaloisForLFunctions.HTGeometry.ConstitutiveExchangeableFormationSelection

/-!
# Xi formation stratification and reflected-work properness

The centered modular class is represented here in four coordinate systems:

* an additive stable source class;
* its exponential cofinal holonomy;
* three-slot functional-equation formation work;
* a positive singular escape index reconstructed by four analytic organs.

Functional-equation reflection negates the additive reporter.  Three-slot exchange therefore
creates exactly twice its square, and independent formation depth makes that work grow linearly.
This proves one route-independent mechanism: bounded formation work, stable-class triviality,
central-holonomy triviality, and zero principal escape are the same stratum.  The global boundedness
statement remains RH-equivalent; this module does not assume or produce it.
-/

open Complex Filter
open scoped BigOperators Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open HedenmalmThetaSource

/-- The centered modular reporter law on one separating coordinate. -/
def xiFormationForwardReporterLaw (q : XiZeroCopy) : Fin 1 → ℝ :=
  fun _ => primeDepthBVWoldXiCenteredRate q.1

/-- Its literal functional-equation reflected reporter law. -/
def xiFormationReflectedReporterLaw (q : XiZeroCopy) : Fin 1 → ℝ :=
  fun _ => primeDepthBVWoldXiCenteredRate (xiZeroCopyReflectEquiv q).1

theorem xiFormationReflectedReporterLaw_eq_neg
    (q : XiZeroCopy) :
    xiFormationReflectedReporterLaw q = -xiFormationForwardReporterLaw q := by
  funext i
  change primeDepthBVWoldXiCenteredRate (xiZeroCopyReflectEquiv q).1 =
    -primeDepthBVWoldXiCenteredRate q.1
  exact primeDepthBVWoldXiCenteredRate_copyReflect q

/-- Three-slot exchange exposes twice the squared centered modular charge. -/
theorem xiFormationThreeSlotExchangeDefect_eq
    (q : XiZeroCopy) :
    finiteExchangeDefect (xiFormationForwardReporterLaw q)
        (xiFormationReflectedReporterLaw q) =
      2 * primeDepthBVWoldXiCenteredRate q.1 ^ (2 : ℕ) := by
  rw [xiFormationReflectedReporterLaw_eq_neg]
  simp [finiteExchangeDefect, threeSlotExchangeDefect_eq,
    xiFormationForwardReporterLaw]
  ring

/-- Work of independent reflected three-slot formation blocks. -/
def xiFormationIndependentWork (n : ℕ) (q : XiZeroCopy) : ℝ :=
  finiteExchangeWork n (xiFormationForwardReporterLaw q)
    (xiFormationReflectedReporterLaw q)

theorem xiFormationIndependentWork_eq
    (n : ℕ) (q : XiZeroCopy) :
    xiFormationIndependentWork n q =
      2 * (n : ℝ) * primeDepthBVWoldXiCenteredRate q.1 ^ (2 : ℕ) := by
  rw [xiFormationIndependentWork, finiteExchangeWork,
    xiFormationThreeSlotExchangeDefect_eq]
  ring

/-- Properness means uniform boundedness through arbitrary independent formation depth. -/
def XiFormationIndependentWorkProperAt (q : XiZeroCopy) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, xiFormationIndependentWork n q ≤ C

theorem xiFormationIndependentWorkProperAt_iff_centeredRate_eq_zero
    (q : XiZeroCopy) :
    XiFormationIndependentWorkProperAt q ↔
      primeDepthBVWoldXiCenteredRate q.1 = 0 := by
  change (∃ C : ℝ, ∀ n : ℕ,
      finiteExchangeWork n (xiFormationForwardReporterLaw q)
        (xiFormationReflectedReporterLaw q) ≤ C) ↔ _
  rw [finiteExchangeWork_bounded_iff]
  rw [xiFormationReflectedReporterLaw_eq_neg]
  constructor
  · intro h
    have h0 := congrFun h (0 : Fin 1)
    simp [xiFormationForwardReporterLaw] at h0
    linarith
  · intro h
    funext i
    simp [xiFormationForwardReporterLaw, h]

/-- The zero stratum of the singular escape index is exactly the zero stratum of the additive
stable class. -/
theorem thetaKakutaniHarmonicEscapeIndex_eq_zero_iff_stableClass_eq_zero
    (q : XiZeroCopy) :
    thetaKakutaniHarmonicEscapeIndex q = 0 ↔
      sourceChartClass (q.1 : ℂ) = 0 := by
  rw [thetaKakutaniHarmonicEscapeIndex_eq_zero_iff_centeredRate_eq_zero,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff,
    sourceChartClass_eq_zero_iff]

/-- Every nonzero stable class tropicalizes to one full singular escape unit. -/
theorem thetaKakutaniHarmonicEscapeIndex_eq_one_iff_stableClass_ne_zero
    (q : XiZeroCopy) :
    thetaKakutaniHarmonicEscapeIndex q = 1 ↔
      sourceChartClass (q.1 : ℂ) ≠ 0 := by
  constructor
  · intro hone hclass
    have hzero :=
      (thetaKakutaniHarmonicEscapeIndex_eq_zero_iff_stableClass_eq_zero q).2 hclass
    linarith
  · intro hclass
    have hrate : primeDepthBVWoldXiCenteredRate q.1 ≠ 0 := by
      intro hzero
      exact hclass
        ((thetaKakutaniHarmonicEscapeIndex_eq_zero_iff_stableClass_eq_zero q).1
          ((thetaKakutaniHarmonicEscapeIndex_eq_zero_iff_centeredRate_eq_zero q).2 hzero))
    have hflux : thetaXiRankTwoBoundaryFlux q ≠ 0 := by
      exact mt (thetaXiRankTwoBoundaryFlux_eq_zero_iff_centeredRate_eq_zero q).1 hrate
    simp [thetaKakutaniHarmonicEscapeIndex, hflux]

/-- Additive stable class, central holonomy anomaly, formation properness, and singular escape
are four coordinates of the same zero stratum. -/
theorem xiFormationStratification_zeroLaw
    {n : ℕ} (hn : 2 ≤ n) (m : ℕ) (p : Nat.Primes) (q : XiZeroCopy) :
    XiFormationIndependentWorkProperAt q ↔
      sourceChartClass (q.1 : ℂ) = 0 ∧
      thetaInternalJetNormalizedCofinalAnomalyMatrix n m q.1 p = 0 ∧
      thetaKakutaniHarmonicEscapeIndex q = 0 := by
  rw [xiFormationIndependentWorkProperAt_iff_centeredRate_eq_zero,
    thetaInternalJetNormalizedCofinalAnomalyMatrix_eq_zero_iff_sourceChartClass hn,
    thetaKakutaniHarmonicEscapeIndex_eq_zero_iff_centeredRate_eq_zero]
  constructor
  · intro hrate
    have hline := (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1 hrate
    have hclass := (sourceChartClass_eq_zero_iff (q.1 : ℂ)).2 hline
    exact ⟨hclass, hclass, hrate⟩
  · exact fun h => h.2.2

/-- The boundary-flux factor `M(q)` in `B(q) = -M(q) a(q)` is strictly positive. -/
theorem thetaXiFluxMassEnergy_pos (q : XiZeroCopy) :
    0 < thetaSource.mass * thetaXiRootEnergy q :=
  mul_pos thetaSource.mass_pos (thetaXiRootEnergy_pos q)

/-- The principal escape class is the indicator of nonzero centered modular rate. -/
theorem thetaKakutaniHarmonicEscapeIndex_eq_indicator (q : XiZeroCopy) :
    thetaKakutaniHarmonicEscapeIndex q =
      if primeDepthBVWoldXiCenteredRate q.1 = 0 then 0 else 1 := by
  simp only [thetaKakutaniHarmonicEscapeIndex,
    thetaXiRankTwoBoundaryFlux_eq_zero_iff_centeredRate_eq_zero]

/-- Functional-equation reflection preserves the principal escape class. -/
theorem thetaKakutaniHarmonicEscapeIndex_reflect (q : XiZeroCopy) :
    thetaKakutaniHarmonicEscapeIndex (xiZeroCopyReflectEquiv q) =
      thetaKakutaniHarmonicEscapeIndex q := by
  simp [thetaKakutaniHarmonicEscapeIndex, thetaXiRankTwoBoundaryFlux_reflect]

/-- Vanishing of the principal escape class at every Xi copy is exactly RH. -/
theorem forall_thetaKakutaniHarmonicEscapeIndex_eq_zero_iff_riemannHypothesis :
    (∀ q : XiZeroCopy, thetaKakutaniHarmonicEscapeIndex q = 0) ↔ RiemannHypothesis := by
  rw [← thetaGreenBoundaryNeutral_iff_riemannHypothesis]
  unfold ThetaGreenBoundaryNeutral
  exact forall_congr' fun q =>
    (thetaKakutaniHarmonicEscapeIndex_eq_zero_iff_centeredRate_eq_zero q).trans
      (thetaXiRankTwoBoundaryFlux_eq_zero_iff_centeredRate_eq_zero q).symm

/-- Global reflected formation-work properness is exactly RH. -/
theorem forall_xiFormationIndependentWorkProperAt_iff_riemannHypothesis :
    (∀ q : XiZeroCopy, XiFormationIndependentWorkProperAt q) ↔
      RiemannHypothesis := by
  rw [← thetaGreenBoundaryNeutral_iff_riemannHypothesis]
  unfold ThetaGreenBoundaryNeutral
  exact forall_congr' fun q =>
    (xiFormationIndependentWorkProperAt_iff_centeredRate_eq_zero q).trans
      (thetaXiRankTwoBoundaryFlux_eq_zero_iff_centeredRate_eq_zero q).symm

end

end RHTower
