import GaloisForLFunctions.RHTower.EulerSquarefreeWickCompletedJetHorizontalFaithfulness
import GaloisForLFunctions.RHTower.XiCriticalLineIntegrality

/-!
# Dimension-preserving EWQ color on the Xi divisor

The full primitive mod-12 jet gives a nonzero countable color directly on each point of the
original Xi divisor support.  Functional-equation/Schwarz reflection acts on this same fibre by
root-number graded conjugation.  Horizontal projective faithfulness proves that the color
separates every free orbit of the critical-line involution.

Thus EWQ no longer needs an auxiliary finite tensor cell, unbounded divisibility, or a post-divisor
choice of one nonzero interaction derivative.  Global color fixation remains equivalent to RH;
this module constructs and classifies the original-divisor action but does not force its fixation.
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Dimension-preserving EWQ color on the original Xi divisor support. -/
def eulerWickXiDivisorCompletedJetColor
    (rho : _root_.RHTower.XiDivisorSupport) : ℕ → ℂ :=
  eulerWickPrimitiveCompletedInteractionJet (rho : ℂ)

theorem eulerWickXiDivisorCompletedJetColor_ne_zero
    (rho : _root_.RHTower.XiDivisorSupport) :
    eulerWickXiDivisorCompletedJetColor rho ≠ 0 :=
  eulerWickPrimitiveCompletedInteractionJet_ne_zero (rho : ℂ)

/-- Critical-line reflection acts on the same divisor color by root-number graded conjugation. -/
theorem eulerWickXiDivisorCompletedJetColor_lineConj
    (rho : _root_.RHTower.XiDivisorSupport) (n : ℕ) :
    eulerWickXiDivisorCompletedJetColor
        (_root_.RHTower.xiZeroLineConjEquiv rho) n =
      quadraticCharacterTwelve.rootNumber * (-1 : ℂ) ^ n *
        (starRingEnd ℂ) (eulerWickXiDivisorCompletedJetColor rho n) := by
  rw [eulerWickXiDivisorCompletedJetColor,
    eulerWickXiDivisorCompletedJetColor,
    eulerWickPrimitiveCompletedInteractionJet,
    eulerWickPrimitiveCompletedInteractionJet,
    _root_.RHTower.xiZeroLineConjEquiv_apply,
    eulerWickPrimitiveCompletedInteraction_iteratedDeriv_one_sub,
    eulerWickPrimitiveCompletedInteraction_iteratedDeriv_conj]

/-- The EWQ color separates every free horizontal orbit of the critical-line involution. -/
theorem eulerWickXiDivisorCompletedJetColor_lineConj_eq_iff
    (rho : _root_.RHTower.XiDivisorSupport) :
    eulerWickXiDivisorCompletedJetColor
        (_root_.RHTower.xiZeroLineConjEquiv rho) =
      eulerWickXiDivisorCompletedJetColor rho ↔
        ((rho : ℂ).re = 1 / 2) := by
  constructor
  · intro hcolor
    have hprojective : EulerWickPrimitiveCompletedJetsProjectivelyAgree
        (_root_.RHTower.xiZeroLineConjEquiv rho : ℂ) (rho : ℂ) := by
      refine ⟨1, one_ne_zero, ?_⟩
      intro n
      have hn := congrFun hcolor n
      simpa [eulerWickXiDivisorCompletedJetColor,
        eulerWickPrimitiveCompletedInteractionJet] using hn
    have hre := re_eq_of_eulerWickPrimitiveCompletedJetsProjectivelyAgree hprojective
    rw [_root_.RHTower.xiZeroLineConjEquiv_apply] at hre
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    linarith
  · intro hre
    have hpoint : _root_.RHTower.xiZeroLineConjEquiv rho = rho := by
      apply Subtype.ext
      apply Complex.ext
      · rw [_root_.RHTower.xiZeroLineConjEquiv_apply]
        simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
        linarith
      · rw [_root_.RHTower.xiZeroLineConjEquiv_apply]
        simp
    rw [hpoint]

/-- The constructed dimension-preserving EWQ divisor color has no free reflection orbit exactly
when RH holds. -/
theorem everyEulerWickXiDivisorCompletedJetColor_lineConj_fixed_iff_rh :
    (∀ rho : _root_.RHTower.XiDivisorSupport,
      eulerWickXiDivisorCompletedJetColor
          (_root_.RHTower.xiZeroLineConjEquiv rho) =
        eulerWickXiDivisorCompletedJetColor rho) ↔ RiemannHypothesis := by
  constructor
  · intro hall
    apply _root_.RHTower.riemannHypothesis_iff_xiZeroLineConj_fixed.mpr
    intro rho
    have hre :=
      (eulerWickXiDivisorCompletedJetColor_lineConj_eq_iff rho).mp (hall rho)
    apply Subtype.ext
    apply Complex.ext
    · rw [_root_.RHTower.xiZeroLineConjEquiv_apply]
      simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · rw [_root_.RHTower.xiZeroLineConjEquiv_apply]
      simp
  · intro hRH rho
    have hfixed :=
      _root_.RHTower.riemannHypothesis_iff_xiZeroLineConj_fixed.mp hRH rho
    rw [hfixed]

end

end GaloisForLFunctions.RHTower
