import GaloisForLFunctions.RHTower.EulerSquarefreeWickCompletedFockOperatorLanding
import GaloisForLFunctions.HTGeometry.PureStateProjectorDifferenceInertia
import GaloisForLFunctions.RHTower.FiniteRankOperatorAlgebra

/-!
# EWQ completed-Fock rank quantum

The two line-conjugate completed Euler--Wick Fock colors define a difference of positive
rank-one projectors.  This operator always has rank at most two.  Its rank drops to at most one
exactly on the critical line; away from the line its two images are linearly independent, so the
rank is exactly two.

Thus every off-line Xi divisor packet carries a discrete algebraic quantum of size two even when
its trace norm is arbitrarily small.  This is the operator-theoretic interface needed to compare
the EWQ interaction with reflection-collision censuses.
-/

open Complex Matrix
open scoped ENNReal InnerProductSpace Matrix

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

local instance eulerSquarefreeWickCompletedFockRankQuantumLocalInst1 : Module ℂ EulerWickCompletedFockSpace :=
  lp.instInnerProductSpace.toModule

theorem eulerWickXiDivisorFockVector_lineConj_linearIndependent_iff
    (rho : _root_.RHTower.XiDivisorSupport) :
    LinearIndependent ℂ ![
      eulerWickPrimitiveCompletedInteractionFockVector (rho : ℂ),
      eulerWickPrimitiveCompletedInteractionFockVector
        (_root_.RHTower.xiZeroLineConjEquiv rho : ℂ)] ↔
      (rho : ℂ).re ≠ 1 / 2 := by
  constructor
  · intro hli hre
    have hpoint : _root_.RHTower.xiZeroLineConjEquiv rho = rho := by
      apply Subtype.ext
      apply Complex.ext
      · rw [_root_.RHTower.xiZeroLineConjEquiv_apply]
        simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
        linarith
      · rw [_root_.RHTower.xiZeroLineConjEquiv_apply]
        simp
    rw [hpoint] at hli
    have hvec : eulerWickPrimitiveCompletedInteractionFockVector (rho : ℂ) ≠ 0 :=
      eulerWickPrimitiveCompletedInteractionFockVector_ne_zero (rho : ℂ)
    have hnot := (LinearIndependent.pair_iff' hvec).mp hli (1 : ℂ)
    exact hnot (by simp)
  · intro hoff
    let u := eulerWickPrimitiveCompletedInteractionFockVector (rho : ℂ)
    let v := eulerWickPrimitiveCompletedInteractionFockVector
      (_root_.RHTower.xiZeroLineConjEquiv rho : ℂ)
    apply (LinearIndependent.pair_iff'
      (eulerWickPrimitiveCompletedInteractionFockVector_ne_zero (rho : ℂ))).2
    intro a ha
    have ha0 : a ≠ 0 := by
      intro hzero
      subst a
      have hvzero :
          eulerWickPrimitiveCompletedInteractionFockVector
              (_root_.RHTower.xiZeroLineConjEquiv rho : ℂ) = 0 := by
        simpa only [zero_smul] using ha.symm
      exact (eulerWickPrimitiveCompletedInteractionFockVector_ne_zero
        (_root_.RHTower.xiZeroLineConjEquiv rho : ℂ)) hvzero
    have hprojective : EulerWickPrimitiveCompletedJetsProjectivelyAgree
        (_root_.RHTower.xiZeroLineConjEquiv rho : ℂ) (rho : ℂ) := by
      refine ⟨a, ha0, ?_⟩
      intro n
      have hn := congrArg (fun w : EulerWickCompletedFockSpace => w n) ha
      change a * (iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction (rho : ℂ) /
          (Real.sqrt (n.factorial : ℝ) : ℂ)) =
        iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction
            (_root_.RHTower.xiZeroLineConjEquiv rho : ℂ) /
          (Real.sqrt (n.factorial : ℝ) : ℂ) at hn
      have hfac : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
      field_simp at hn
      exact hn.symm
    have hre := re_eq_of_eulerWickPrimitiveCompletedJetsProjectivelyAgree hprojective
    rw [_root_.RHTower.xiZeroLineConjEquiv_apply] at hre
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    exfalso
    apply hoff
    linarith

/-- Algebraic operator difference of the two line-conjugate EWQ Fock colors. -/
def eulerWickXiDivisorCompletedFockRankDefect
    (rho : _root_.RHTower.XiDivisorSupport) :
    EulerWickCompletedFockSpace →L[ℂ] EulerWickCompletedFockSpace :=
  HTGeometry.pureStateProjectorDifference
    (eulerWickPrimitiveCompletedInteractionFockVector (rho : ℂ))
    (eulerWickPrimitiveCompletedInteractionFockVector
      (_root_.RHTower.xiZeroLineConjEquiv rho : ℂ))

theorem eulerWickXiDivisorCompletedFockRankDefect_eq_traceDefect_coe
    (rho : _root_.RHTower.XiDivisorSupport) :
    eulerWickXiDivisorCompletedFockRankDefect rho =
      ((eulerWickXiDivisorCompletedFockColor
          (_root_.RHTower.xiZeroLineConjEquiv rho) -
        eulerWickXiDivisorCompletedFockColor rho :
          _root_.RHTower.SchattenOneOperator EulerWickCompletedFockSpace) :
        EulerWickCompletedFockSpace →L[ℂ] EulerWickCompletedFockSpace) := by
  rfl

theorem eulerWickXiDivisorCompletedFockRankDefect_hasRankLE_two
    (rho : _root_.RHTower.XiDivisorSupport) :
    _root_.RHTower.HasRankLE
      (eulerWickXiDivisorCompletedFockRankDefect rho) 2 := by
  let u := eulerWickPrimitiveCompletedInteractionFockVector (rho : ℂ)
  let v := eulerWickPrimitiveCompletedInteractionFockVector
    (_root_.RHTower.xiZeroLineConjEquiv rho : ℂ)
  have hv : _root_.RHTower.HasRankLE
      (InnerProductSpace.rankOne ℂ v v) 1 := by
    simpa [InnerProductSpace.rankOne_def] using
      _root_.RHTower.deningerSmulRight_hasRankLE_one (innerSL ℂ v) v
  have hu : _root_.RHTower.HasRankLE
      (InnerProductSpace.rankOne ℂ u u) 1 := by
    simpa [InnerProductSpace.rankOne_def] using
      _root_.RHTower.deningerSmulRight_hasRankLE_one (innerSL ℂ u) u
  simpa [eulerWickXiDivisorCompletedFockRankDefect,
    HTGeometry.pureStateProjectorDifference, u, v, sub_eq_add_neg] using
      hv.add hu.neg

theorem eulerWickXiDivisorCompletedFockRankDefect_not_hasRankLE_one_of_offLine
    (rho : _root_.RHTower.XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    ¬ _root_.RHTower.HasRankLE
      (eulerWickXiDivisorCompletedFockRankDefect rho) 1 := by
  intro hrank
  obtain ⟨V, hVfd, hVrank, hmem⟩ := hrank
  letI : FiniteDimensional ℂ V := hVfd
  let u := eulerWickPrimitiveCompletedInteractionFockVector (rho : ℂ)
  let v := eulerWickPrimitiveCompletedInteractionFockVector
    (_root_.RHTower.xiZeroLineConjEquiv rho : ℂ)
  let D := eulerWickXiDivisorCompletedFockRankDefect rho
  have huv : LinearIndependent ℂ ![u, v] := by
    simpa [u, v] using
      (eulerWickXiDivisorFockVector_lineConj_linearIndependent_iff rho).2 hoff
  have himages : LinearIndependent ℂ ![D u, D v] := by
    simpa [D, eulerWickXiDivisorCompletedFockRankDefect, u, v] using
      HTGeometry.linearIndependent_pureStateProjectorDifference_images huv
  let Du : V := ⟨D u, hmem u⟩
  let Dv : V := ⟨D v, hmem v⟩
  have hsub : LinearIndependent ℂ ![Du, Dv] := by
    have hDuAmbient : D u ≠ 0 := by
      simpa using himages.ne_zero (0 : Fin 2)
    have hDu : Du ≠ 0 := by
      intro hzero
      apply hDuAmbient
      exact congrArg Subtype.val hzero
    rw [LinearIndependent.pair_iff' hDu]
    intro a ha
    have hnot := (LinearIndependent.pair_iff' hDuAmbient).mp himages a
    apply hnot
    have haAmbient := congrArg Subtype.val ha
    simpa only [Du, Dv, Submodule.coe_smul_of_tower] using haAmbient
  have hdim := hsub.fintype_card_le_finrank
  norm_num at hdim
  omega

/-- Rank at most one is equivalent to critical-line fixedness. -/
theorem eulerWickXiDivisorCompletedFockRankDefect_hasRankLE_one_iff
    (rho : _root_.RHTower.XiDivisorSupport) :
    _root_.RHTower.HasRankLE
        (eulerWickXiDivisorCompletedFockRankDefect rho) 1 ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hrank
    by_contra hoff
    exact
      (eulerWickXiDivisorCompletedFockRankDefect_not_hasRankLE_one_of_offLine
        rho hoff) hrank
  · intro hre
    have hpoint : _root_.RHTower.xiZeroLineConjEquiv rho = rho := by
      apply Subtype.ext
      apply Complex.ext
      · rw [_root_.RHTower.xiZeroLineConjEquiv_apply]
        simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
        linarith
      · rw [_root_.RHTower.xiZeroLineConjEquiv_apply]
        simp
    rw [eulerWickXiDivisorCompletedFockRankDefect_eq_traceDefect_coe, hpoint]
    simp
    exact _root_.RHTower.hasRankLE_zero 1

theorem eulerWickXiDivisorCompletedFockRankDefect_exactRankTwo_iff
    (rho : _root_.RHTower.XiDivisorSupport) :
    (_root_.RHTower.HasRankLE
        (eulerWickXiDivisorCompletedFockRankDefect rho) 2 ∧
      ¬ _root_.RHTower.HasRankLE
        (eulerWickXiDivisorCompletedFockRankDefect rho) 1) ↔
      (rho : ℂ).re ≠ 1 / 2 := by
  constructor
  · rintro ⟨_, hnotone⟩ hre
    have hpoint : _root_.RHTower.xiZeroLineConjEquiv rho = rho := by
      apply Subtype.ext
      apply Complex.ext
      · rw [_root_.RHTower.xiZeroLineConjEquiv_apply]
        simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
        linarith
      · rw [_root_.RHTower.xiZeroLineConjEquiv_apply]
        simp
    apply hnotone
    rw [eulerWickXiDivisorCompletedFockRankDefect_eq_traceDefect_coe, hpoint]
    simp
    exact _root_.RHTower.hasRankLE_zero 1
  · intro hoff
    exact ⟨eulerWickXiDivisorCompletedFockRankDefect_hasRankLE_two rho,
      eulerWickXiDivisorCompletedFockRankDefect_not_hasRankLE_one_of_offLine rho hoff⟩

end

end GaloisForLFunctions.RHTower
