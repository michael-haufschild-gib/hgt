import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticCompletedCohomology

/-!
# Green transport on the completed Xi-divisor comparison model

The compact-support/ordinary Poincare pairing and the completed odd cup form determine a canonical
linear Green map

`G : H¹_c → H¹_Hilb`.

Start with the conjugate-linear Fréchet--Riesz representative of a compact-support class and apply
minus the conjugate-linear odd Hodge operator.  The two conjugations cancel, so `G` is complex
linear.  It has dense range and represents source Poincare evaluation exactly through the
completed alternating cup:

`cup (G ell) x = ell(x)`.

On finite source jets, `G` is the explicit oriented functional-equation reflection

`(G a)_q = epsilon_q a_(R q)`.

This module operates on `XiDivisorL2`; despite the historical declaration names, it is not the
global Green operator of an independently constructed arithmetic complex.  Its linear transport is
Frobenius-natural for the Xi-jet associated graded unconditionally.  The source-native
Calderón--Green construction and its comparison with this model remain open; on this comparison
model the residual anti-linear Riesz/Hodge naturality is equivalent to RH.
-/

open Complex Function Set Topology
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- The completed odd Hodge operator as a continuous conjugate-linear isometry. -/
def deningerArithmeticOrientedHodgeContinuous :
    XiDivisorL2 →L⋆[ℂ] XiDivisorL2 where
  toFun := deningerArithmeticOrientedHodgeLp
  map_add' := deningerArithmeticOrientedHodgeLpSigma.map_add
  map_smul' := deningerArithmeticOrientedHodgeLpSigma.map_smul'
  cont := by
    exact
      (AddMonoidHomClass.isometry_of_norm
        deningerArithmeticOrientedHodgeLpSigma
        norm_deningerArithmeticOrientedHodgeLp).continuous

/--
Linear source Green operator.  The leading minus sign is the odd-parity correction making cup
with the Green representative equal, rather than opposite, to Poincare evaluation.
-/
def deningerArithmeticSourceGreen :
    DeningerArithmeticTopologicalH1Compact →L[ℂ]
      DeningerArithmeticCompletedH1 where
  toFun ell :=
    -deningerArithmeticOrientedHodgeLp
      (deningerArithmeticJetCompactToHilbert ell)
  map_add' ell eta := by
    rw [deningerArithmeticJetCompactToHilbert.map_add]
    rw [show
      deningerArithmeticOrientedHodgeLp
          (deningerArithmeticJetCompactToHilbert ell +
            deningerArithmeticJetCompactToHilbert eta) =
        deningerArithmeticOrientedHodgeLp
            (deningerArithmeticJetCompactToHilbert ell) +
          deningerArithmeticOrientedHodgeLp
            (deningerArithmeticJetCompactToHilbert eta) from
      deningerArithmeticOrientedHodgeLpSigma.map_add _ _]
    abel
  map_smul' c ell := by
    rw [map_smulₛₗ deningerArithmeticJetCompactToHilbert]
    have hJ :
        deningerArithmeticOrientedHodgeLp
            ((starRingEnd ℂ) c •
              deningerArithmeticJetCompactToHilbert ell) =
          c • deningerArithmeticOrientedHodgeLp
            (deningerArithmeticJetCompactToHilbert ell) := by
      simpa only [starRingEnd_self_apply] using!
        (map_smulₛₗ deningerArithmeticOrientedHodgeLpSigma
          ((starRingEnd ℂ) c)
          (deningerArithmeticJetCompactToHilbert ell))
    rw [hJ]
    simp
  cont :=
    Continuous.neg
      (deningerArithmeticOrientedHodgeContinuous.continuous.comp
        deningerArithmeticJetCompactToHilbert.continuous)

@[simp]
theorem deningerArithmeticSourceGreen_apply
    (ell : DeningerArithmeticTopologicalH1Compact) :
    deningerArithmeticSourceGreen ell =
      -deningerArithmeticOrientedHodgeLp
        (deningerArithmeticJetCompactToHilbert ell) :=
  rfl

/--
Oriented functional-equation reflection on algebraic source jets.  This is the finite-test form of
the Green operator.
-/
def deningerArithmeticOrientedGreenJetTest :
    Module.End ℂ DeningerArithmeticJetTest :=
  (finsuppDiagonal deningerArithmeticFEOrientation).comp
    (Finsupp.domLCongr xiZeroCopyReflectEquiv).toLinearMap

@[simp]
theorem deningerArithmeticOrientedGreenJetTest_apply
    (a : DeningerArithmeticJetTest)
    (q : DeningerArithmeticJetCoordinate) :
    deningerArithmeticOrientedGreenJetTest a q =
      deningerArithmeticFEOrientation q *
        a (xiZeroCopyReflectEquiv q) := by
  change
    finsuppDiagonal deningerArithmeticFEOrientation
        ((Finsupp.domLCongr xiZeroCopyReflectEquiv) a) q =
      deningerArithmeticFEOrientation q *
        a (xiZeroCopyReflectEquiv q)
  rw [finsuppDiagonal_apply]
  change
    deningerArithmeticFEOrientation q *
        a (xiZeroCopyReflectEquiv.symm q) =
      deningerArithmeticFEOrientation q *
        a (xiZeroCopyReflectEquiv q)
  rw [xiZeroCopyReflectEquiv_symm_apply]

/-- Odd oriented Green reflection squares to minus the identity on finite source jets. -/
theorem deningerArithmeticOrientedGreenJetTest_sq
    (a : DeningerArithmeticJetTest) :
    deningerArithmeticOrientedGreenJetTest
        (deningerArithmeticOrientedGreenJetTest a) = -a := by
  ext q
  rw [deningerArithmeticOrientedGreenJetTest_apply,
    deningerArithmeticOrientedGreenJetTest_apply,
    xiZeroCopyReflectEquiv_apply_apply,
    deningerArithmeticFEOrientation_reflect]
  have heps := deningerArithmeticFEOrientation_sq q
  change
    deningerArithmeticFEOrientation q *
        (-deningerArithmeticFEOrientation q * a q) =
      -a q
  linear_combination -a q * heps

/-- On compact-support finite jets, the analytic Green map is the explicit oriented reflection. -/
theorem deningerArithmeticSourceGreen_test
    (a : DeningerArithmeticJetTest) :
    deningerArithmeticSourceGreen
        (deningerArithmeticJetTestToCompact a) =
      deningerArithmeticJetTestToHilbert
        (deningerArithmeticOrientedGreenJetTest a) := by
  rw [deningerArithmeticSourceGreen_apply,
    deningerArithmeticJetCompactToHilbert_test]
  ext q
  change
    -(-deningerArithmeticFEOrientation q *
        (starRingEnd ℂ)
          ((starRingEnd ℂ)
            (deningerArithmeticJetTestToHilbert a
              (xiZeroCopyReflectEquiv q)))) =
      deningerArithmeticJetTestToHilbert
        (deningerArithmeticOrientedGreenJetTest a) q
  rw [starRingEnd_self_apply,
    deningerArithmeticJetTestToHilbert_apply,
    deningerArithmeticJetTestToHilbert_apply,
    deningerArithmeticOrientedGreenJetTest_apply]
  ring

/--
The source Green representative realizes compact-support Poincare evaluation exactly through the
completed alternating cup.
-/
theorem deningerArithmeticSourceGreen_cup
    (ell : DeningerArithmeticTopologicalH1Compact)
    (x : DeningerArithmeticCompletedH1) :
    deningerArithmeticOrientedHilbertCup
        (deningerArithmeticSourceGreen ell) x =
      ell (deningerArithmeticJetHilbertToH1 x) := by
  rw [deningerArithmeticOrientedHilbertCup_apply,
    deningerArithmeticSourceGreen_apply]
  change
    inner ℂ
        (deningerArithmeticOrientedHodgeLpSigma
          (-deningerArithmeticOrientedHodgeLpSigma
            (deningerArithmeticJetCompactToHilbert ell))) x =
      ell (deningerArithmeticJetHilbertToH1 x)
  rw [map_neg]
  have hsq :
      deningerArithmeticOrientedHodgeLpSigma
          (deningerArithmeticOrientedHodgeLpSigma
            (deningerArithmeticJetCompactToHilbert ell)) =
        -deningerArithmeticJetCompactToHilbert ell := by
    simpa only [kRealParityAction, if_true] using!
      deningerArithmeticOrientedHilbertHodge.sq
        (deningerArithmeticJetCompactToHilbert ell)
  have hgreen :
      -deningerArithmeticOrientedHodgeLpSigma
          (deningerArithmeticOrientedHodgeLpSigma
            (deningerArithmeticJetCompactToHilbert ell)) =
        deningerArithmeticJetCompactToHilbert ell := by
    calc
      -deningerArithmeticOrientedHodgeLpSigma
            (deningerArithmeticOrientedHodgeLpSigma
              (deningerArithmeticJetCompactToHilbert ell)) =
          -(-deningerArithmeticJetCompactToHilbert ell) :=
        congrArg Neg.neg hsq
      _ = deningerArithmeticJetCompactToHilbert ell :=
        neg_neg _
  rw [hgreen]
  exact deningerArithmeticJetCompactToHilbert_pairing ell x

/-- Odd Hodge is surjective, with inverse `-J`. -/
theorem deningerArithmeticOrientedHodgeLp_surjective :
    Function.Surjective deningerArithmeticOrientedHodgeLp := by
  intro y
  refine ⟨-deningerArithmeticOrientedHodgeLp y, ?_⟩
  change
    deningerArithmeticOrientedHodgeLpSigma
      (-deningerArithmeticOrientedHodgeLpSigma y) = y
  rw [map_neg]
  have hsq :
      deningerArithmeticOrientedHodgeLpSigma
          (deningerArithmeticOrientedHodgeLpSigma y) = -y := by
    simpa only [kRealParityAction, if_true] using!
      deningerArithmeticOrientedHilbertHodge.sq y
  calc
    -deningerArithmeticOrientedHodgeLpSigma
          (deningerArithmeticOrientedHodgeLpSigma y) =
        -(-y) :=
      congrArg Neg.neg hsq
    _ = y := neg_neg _

/-- Compact-support arithmetic cohomology has dense image under the source Green operator. -/
theorem deningerArithmeticSourceGreen_dense :
    DenseRange deningerArithmeticSourceGreen := by
  have hcomp :
      DenseRange
        (deningerArithmeticOrientedHodgeLp ∘
          deningerArithmeticJetCompactToHilbert) :=
    DenseRange.comp
      deningerArithmeticOrientedHodgeLp_surjective.denseRange
      deningerArithmeticJetCompactToHilbert_dense
      deningerArithmeticOrientedHodgeContinuous.continuous
  have hneg :
      DenseRange
        (fun ell : DeningerArithmeticTopologicalH1Compact =>
          -deningerArithmeticOrientedHodgeLp
            (deningerArithmeticJetCompactToHilbert ell)) := by
    exact
      DenseRange.comp
        (show DenseRange
            (fun x : DeningerArithmeticCompletedH1 => -x) from
          (Equiv.neg DeningerArithmeticCompletedH1).surjective.denseRange)
        hcomp
        continuous_neg
  simpa only [deningerArithmeticSourceGreen_apply, Function.comp_apply] using! hneg

/-- Weight-one compact-support Frobenius on the source associated graded. -/
def deningerArithmeticGradedThetaCompact :
    Module.End ℂ DeningerArithmeticJetTest :=
  finsuppDiagonal fun q => 1 - deningerDivisorThetaEigen q

@[simp]
theorem deningerArithmeticGradedThetaCompact_apply
    (a : DeningerArithmeticJetTest)
    (q : DeningerArithmeticJetCoordinate) :
    deningerArithmeticGradedThetaCompact a q =
      (1 - deningerDivisorThetaEigen q) * a q :=
  finsuppDiagonal_apply _ _ _

/--
The linear source Green transport intertwines ordinary and compact-support associated-graded
Frobenius unconditionally.
-/
theorem deningerArithmeticGradedTheta_greenJetTest
    (a : DeningerArithmeticJetTest) :
    deningerArithmeticGradedTheta
        (deningerArithmeticOrientedGreenJetTest a) =
      deningerArithmeticOrientedGreenJetTest
        (deningerArithmeticGradedThetaCompact a) := by
  ext q
  rw [show deningerArithmeticGradedTheta
        (deningerArithmeticOrientedGreenJetTest a) q =
      deningerDivisorThetaEigen q *
        deningerArithmeticOrientedGreenJetTest a q by
    exact finsuppDiagonal_apply _ _ _]
  rw [deningerArithmeticOrientedGreenJetTest_apply]
  have hrhs :
      deningerArithmeticOrientedGreenJetTest
          (deningerArithmeticGradedThetaCompact a) q =
        deningerArithmeticFEOrientation q *
          ((1 -
            deningerDivisorThetaEigen
              (xiZeroCopyReflectEquiv q)) *
            a (xiZeroCopyReflectEquiv q)) := by
    rw [deningerArithmeticOrientedGreenJetTest_apply,
      deningerArithmeticGradedThetaCompact_apply]
  have hweight := deningerDivisorThetaEigen_add_reflect q
  calc
    deningerDivisorThetaEigen q *
          (deningerArithmeticFEOrientation q *
            a (xiZeroCopyReflectEquiv q)) =
        deningerArithmeticFEOrientation q *
          ((1 -
            deningerDivisorThetaEigen
              (xiZeroCopyReflectEquiv q)) *
            a (xiZeroCopyReflectEquiv q)) := by
      linear_combination
        deningerArithmeticFEOrientation q *
          a (xiZeroCopyReflectEquiv q) * hweight
    _ = deningerArithmeticOrientedGreenJetTest
          (deningerArithmeticGradedThetaCompact a) q :=
      hrhs.symm

end

end RHTower
