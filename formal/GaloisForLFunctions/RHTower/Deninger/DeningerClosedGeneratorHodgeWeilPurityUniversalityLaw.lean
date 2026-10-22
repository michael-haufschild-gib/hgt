import GaloisForLFunctions.RHTower.Deninger.DeningerDivisorClosedGenerator
import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticFiniteHodgePackets
import GaloisForLFunctions.RHTower.XiHedenmalmThetaJetSource
import GaloisForLFunctions.RHTower.XiWeilPositivityCriterion

/-!
# Deninger closed-generator/Hodge/Weil purity universality

The maximal divisor generator, source-local Hodge forms, finite positive Hodge packets, and the
complete Weil square cone are already constructed independently in the corpus.  This module
identifies their common purity law.

Every local Hodge form commutes with Frobenius exactly when its centered support point is real.
Thus RH makes every local form commute and, by linearity, makes every strictly positive finite
Hodge exhaustion commute.  Conversely, one positive exhaustion detects every support point.
The complete Weil square cone detects the same reality condition.  Consequently local Hodge
invariance, universal finite-packet invariance, full Weil positivity, and RH are equivalent for
the same closed dense multiplicity-exact divisor generator.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- Every canonical source-local rank-one Hodge form intertwines the two Frobenius actions. -/
def DeningerLocalJetHodgeFrobeniusInvariant : Prop :=
  ∀ (rho : XiDivisorSupport)
    (x : DeningerArithmeticCompactOpenH1),
    deningerCompactOpenThetaCompact
        (deningerCompactOpenLocalJetHodge rho x) =
      deningerCompactOpenLocalJetHodge rho
        (deningerCompactOpenTheta x)

/--
Every strictly positive weighting of every geometric finite Hodge window intertwines Frobenius.
-/
def DeningerFiniteJetHodgeExhaustionFrobeniusInvariant : Prop :=
  ∀ (weight : XiDivisorSupport → ℝ),
    (∀ rho, 0 < weight rho) →
    ∀ (n : ℕ) (x : DeningerArithmeticCompactOpenH1),
      deningerCompactOpenThetaCompact
          (deningerCompactOpenFiniteJetHodge
            (deningerXiSupportClosedBallFinset n) weight x) =
        deningerCompactOpenFiniteJetHodge
          (deningerXiSupportClosedBallFinset n) weight
          (deningerCompactOpenTheta x)

/-- The complete square-summable Xi Weil polarization is nonnegative. -/
def XiWeilSquareConeNonnegative : Prop :=
  ∀ F : ℂ → ℂ, XiWeilSquareSummable F →
    0 ≤ (xiWeilPolarization F F).re

/-- RH is equivalent to Frobenius invariance of every canonical local Hodge form. -/
theorem riemannHypothesis_iff_deningerLocalJetHodgeFrobeniusInvariant :
    RiemannHypothesis ↔ DeningerLocalJetHodgeFrobeniusInvariant := by
  constructor
  · intro hRH rho
    have him : (xiSpectralPointSupport rho).im = 0 := by
      rw [xiSpectralPointSupport_eq_ofReal_of_rh hRH rho, ofReal_im]
    exact
      (deningerCompactOpenLocalJetHodge_theta_commutes_iff rho).2 him
  · exact
      riemannHypothesis_of_deningerCompactOpenLocalJetHodge_theta_commutes

/--
RH is equivalent to Frobenius invariance of every strictly positive finite Hodge exhaustion.
-/
theorem riemannHypothesis_iff_deningerFiniteJetHodgeExhaustionFrobeniusInvariant :
    RiemannHypothesis ↔
      DeningerFiniteJetHodgeExhaustionFrobeniusInvariant := by
  constructor
  · intro hRH weight _hweight n x
    unfold deningerCompactOpenFiniteJetHodge
    simp only [_root_.sum_apply,
      _root_.smul_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro rho hrho
    rw [map_smul]
    congr 1
    have him : (xiSpectralPointSupport rho).im = 0 := by
      rw [xiSpectralPointSupport_eq_ofReal_of_rh hRH rho, ofReal_im]
    exact
      (deningerCompactOpenLocalJetHodge_theta_commutes_iff rho).2 him x
  · intro hfinite
    apply
      riemannHypothesis_of_deningerFiniteJetHodge_exhaustion_commutes
        (fun _ => 1) (fun _ => by norm_num)
    intro n x
    exact hfinite (fun _ => 1) (fun _ => by norm_num) n x

/-- RH is equivalent to nonnegativity of the complete Weil square cone. -/
theorem riemannHypothesis_iff_xiWeilSquareConeNonnegative :
    RiemannHypothesis ↔ XiWeilSquareConeNonnegative := by
  simpa only [XiWeilSquareConeNonnegative] using
    riemannHypothesis_iff_xiWeilPolarization_nonneg

/--
Certificate identifying the analytic operator and all three equivalent purity presentations.
-/
structure DeningerClosedGeneratorHodgeWeilPurityCertificate : Prop where
  generatorClosed : deningerDivisorClosedTheta.IsClosed
  generatorDense :
    Dense (deningerDivisorClosedTheta.domain : Set XiDivisorL2)
  generatorEigenvectors :
    ∀ q : XiZeroCopy,
      deningerDivisorClosedTheta
          (deningerDivisorClosedThetaEigenvector q) =
        deningerDivisorThetaEigen q •
          (deningerDivisorClosedThetaEigenvector q : XiDivisorL2)
  localHodgeIffFinitePackets :
    DeningerLocalJetHodgeFrobeniusInvariant ↔
      DeningerFiniteJetHodgeExhaustionFrobeniusInvariant
  finitePacketsIffWeil :
    DeningerFiniteJetHodgeExhaustionFrobeniusInvariant ↔
      XiWeilSquareConeNonnegative
  localHodgeIffRH :
    DeningerLocalJetHodgeFrobeniusInvariant ↔ RiemannHypothesis
  finitePacketsIffRH :
    DeningerFiniteJetHodgeExhaustionFrobeniusInvariant ↔ RiemannHypothesis
  weilIffRH : XiWeilSquareConeNonnegative ↔ RiemannHypothesis

/--
**Deninger closed-generator/Hodge/Weil purity universality law.**

The canonical divisor generator is closed, densely defined, and multiplicity-exact.  On this
carrier, source-local Hodge invariance, every positive finite Hodge exhaustion, full Weil
positivity, and RH are one condition.
-/
theorem deningerClosedGenerator_hodgeWeilPurityUniversality :
    DeningerClosedGeneratorHodgeWeilPurityCertificate := by
  have hlocal :=
    riemannHypothesis_iff_deningerLocalJetHodgeFrobeniusInvariant
  have hfinite :=
    riemannHypothesis_iff_deningerFiniteJetHodgeExhaustionFrobeniusInvariant
  have hweil := riemannHypothesis_iff_xiWeilSquareConeNonnegative
  exact
    { generatorClosed := deningerDivisorClosedTheta_isClosed
      generatorDense := deningerDivisorClosedTheta_dense
      generatorEigenvectors := deningerDivisorClosedTheta_eigenvector
      localHodgeIffFinitePackets := hlocal.symm.trans hfinite
      finitePacketsIffWeil := hfinite.symm.trans hweil
      localHodgeIffRH := hlocal.symm
      finitePacketsIffRH := hfinite.symm
      weilIffRH := hweil.symm }

end

end RHTower
