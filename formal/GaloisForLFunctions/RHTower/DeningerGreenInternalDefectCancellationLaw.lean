import GaloisForLFunctions.RHTower.DeningerArithmeticSourceGreen
import GaloisForLFunctions.RHTower.RiemannBoundaryGreenFractureLaw

/-!
# Internal defect cancellation in the Deninger source Green map

The finite source Green map is the composite of coefficientwise conjugate Riesz representation
and the odd anti-linear Hodge map.  This file proves that its unconditional Frobenius covariance
is exact cancellation of the two internal boundary-fracture defects.  No claim of source-native
graph landing or zero exclusion is made.
-/

open Complex

namespace RHTower

noncomputable section

/-- Coefficientwise conjugate Riesz map on multiplicity-exact finite jets. -/
def deningerArithmeticGradedRieszConjugation :
    DeningerArithmeticGradedH1 ≃ₛₗ[starRingEnd ℂ]
      DeningerArithmeticGradedH1 :=
  Finsupp.mapRange.linearEquiv (starLinearEquiv ℂ)

@[simp]
theorem deningerArithmeticGradedRieszConjugation_apply
    (a : DeningerArithmeticGradedH1) (q : XiZeroCopy) :
    deningerArithmeticGradedRieszConjugation a q =
      (starRingEnd ℂ) (a q) := by
  rfl

/-- Compact-support weight-one Frobenius on the multiplicity-exact copy model. -/
def deningerArithmeticGradedCompactTheta :
    Module.End ℂ DeningerArithmeticGradedH1 :=
  finsuppDiagonal fun q => 1 - deningerDivisorThetaEigen q

@[simp]
theorem deningerArithmeticGradedCompactTheta_apply
    (a : DeningerArithmeticGradedH1) (q : XiZeroCopy) :
    deningerArithmeticGradedCompactTheta a q =
      (1 - deningerDivisorThetaEigen q) * a q :=
  finsuppDiagonal_apply _ _ _

/-- Covariance defect of the conjugate Riesz factor. -/
def deningerArithmeticGradedRieszCovarianceDefect
    (a : DeningerArithmeticGradedH1) : DeningerArithmeticGradedH1 :=
  deningerArithmeticGradedTheta
      (deningerArithmeticGradedRieszConjugation a) -
    deningerArithmeticGradedRieszConjugation
      (deningerArithmeticGradedCompactTheta a)

/-- Covariance defect of the odd Hodge factor. -/
def deningerArithmeticGradedHodgeCovarianceDefect
    (a : DeningerArithmeticGradedH1) : DeningerArithmeticGradedH1 :=
  deningerArithmeticGradedTheta
      (deningerArithmeticGradedOrientedHodge.sigma a) -
    deningerArithmeticGradedOrientedHodge.sigma
      (deningerArithmeticGradedTheta a)

/-- The conjugate Riesz defect is multiplication by the signed boundary fracture. -/
theorem deningerArithmeticGradedRieszCovarianceDefect_apply
    (a : DeningerArithmeticGradedH1) (q : XiZeroCopy) :
    deningerArithmeticGradedRieszCovarianceDefect a q =
      xiNearbyPoleDualityAdjunctionFracture (q.1 : ℂ) *
        deningerArithmeticGradedRieszConjugation a q := by
  simp only [deningerArithmeticGradedRieszCovarianceDefect,
    deningerArithmeticGradedTheta, deningerDivisorTheta,
    deningerArithmeticGradedRieszConjugation_apply]
  rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  apply Complex.ext <;> simp [deningerDivisorThetaEigen] <;> ring

/-- The odd Hodge defect is the same boundary-fracture multiplier. -/
theorem deningerArithmeticGradedHodgeCovarianceDefect_apply
    (a : DeningerArithmeticGradedH1) (q : XiZeroCopy) :
    deningerArithmeticGradedHodgeCovarianceDefect a q =
      xiNearbyPoleDualityAdjunctionFracture (q.1 : ℂ) *
        deningerArithmeticGradedOrientedHodge.sigma a q := by
  exact
    deningerArithmeticOrientedHodge_commutator_apply_eq_boundaryFracture a q

/-- Functional-equation reflection reverses the signed boundary fracture. -/
theorem xiNearbyPoleDualityAdjunctionFracture_reflect
    (q : XiZeroCopy) :
    xiNearbyPoleDualityAdjunctionFracture
        ((xiZeroCopyReflectEquiv q).1 : ℂ) =
      -xiNearbyPoleDualityAdjunctionFracture (q.1 : ℂ) := by
  rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re,
    xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  have hreflect :
      ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) := rfl
  rw [hreflect]
  apply Complex.ext
  · simp
    ring
  · simp

/-- The two internal anti-linear covariance defects cancel before the composite Green map is
read.  This is the exact information loss hidden by unconditional total covariance. -/
theorem deningerArithmeticGreen_internalDefects_cancel
    (a : DeningerArithmeticGradedH1) :
    deningerArithmeticGradedHodgeCovarianceDefect
          (deningerArithmeticGradedRieszConjugation a) +
        deningerArithmeticGradedOrientedHodge.sigma
          (deningerArithmeticGradedRieszCovarianceDefect a) =
      0 := by
  ext q
  have hfractureReal :
      (starRingEnd ℂ)
          (xiNearbyPoleDualityAdjunctionFracture (q.1 : ℂ)) =
        xiNearbyPoleDualityAdjunctionFracture (q.1 : ℂ) := by
    rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
    exact Complex.conj_ofReal _
  change
    deningerArithmeticGradedHodgeCovarianceDefect
          (deningerArithmeticGradedRieszConjugation a) q +
        deningerArithmeticGradedOrientedHodge.sigma
          (deningerArithmeticGradedRieszCovarianceDefect a) q = 0
  rw [deningerArithmeticGradedHodgeCovarianceDefect_apply,
    deningerArithmeticGradedOrientedHodge_apply,
    deningerArithmeticGradedOrientedHodge_apply,
    deningerArithmeticGradedRieszCovarianceDefect_apply,
    xiNearbyPoleDualityAdjunctionFracture_reflect]
  simp only [map_mul, map_neg,
    deningerArithmeticGradedRieszConjugation_apply,
    starRingEnd_self_apply]
  rw [hfractureReal]
  ring

/-- Linear oriented Green composite on the multiplicity-exact finite copy model. -/
def deningerArithmeticGradedGreenComposite :
    Module.End ℂ DeningerArithmeticGradedH1 :=
  (finsuppDiagonal deningerArithmeticFEOrientation).comp
    (Finsupp.domLCongr xiZeroCopyReflectEquiv).toLinearMap

@[simp]
theorem deningerArithmeticGradedGreenComposite_apply
    (a : DeningerArithmeticGradedH1) (q : XiZeroCopy) :
    deningerArithmeticGradedGreenComposite a q =
      deningerArithmeticFEOrientation q *
        a (xiZeroCopyReflectEquiv q) := by
  change
    finsuppDiagonal deningerArithmeticFEOrientation
        ((Finsupp.domLCongr xiZeroCopyReflectEquiv) a) q = _
  rw [finsuppDiagonal_apply]
  change
    deningerArithmeticFEOrientation q *
        a (xiZeroCopyReflectEquiv.symm q) = _
  rw [xiZeroCopyReflectEquiv_symm_apply]

/-- The linear Green map is exactly minus odd Hodge after conjugate Riesz representation. -/
theorem deningerArithmeticGradedGreenComposite_factor
    (a : DeningerArithmeticGradedH1) :
    deningerArithmeticGradedGreenComposite a =
      -deningerArithmeticGradedOrientedHodge.sigma
        (deningerArithmeticGradedRieszConjugation a) := by
  ext q
  rw [deningerArithmeticGradedGreenComposite_apply]
  change
    deningerArithmeticFEOrientation q * a (xiZeroCopyReflectEquiv q) =
      -(deningerArithmeticGradedOrientedHodge.sigma
        (deningerArithmeticGradedRieszConjugation a) q)
  rw [deningerArithmeticGradedOrientedHodge_apply,
    deningerArithmeticGradedRieszConjugation_apply,
    starRingEnd_self_apply]
  ring

/-- Despite the generally nonzero internal defects, their linear Green composite intertwines
compact-support and ordinary Frobenius unconditionally. -/
theorem deningerArithmeticGradedTheta_greenComposite
    (a : DeningerArithmeticGradedH1) :
    deningerArithmeticGradedTheta
        (deningerArithmeticGradedGreenComposite a) =
      deningerArithmeticGradedGreenComposite
        (deningerArithmeticGradedCompactTheta a) := by
  ext q
  simp only [deningerArithmeticGradedTheta, deningerDivisorTheta,
    finsuppDiagonal_apply, deningerArithmeticGradedGreenComposite_apply,
    deningerArithmeticGradedCompactTheta_apply]
  have hweight := deningerDivisorThetaEigen_add_reflect q
  linear_combination
    deningerArithmeticFEOrientation q *
      a (xiZeroCopyReflectEquiv q) * hweight

/-- One basis coordinate already detects whether the hidden Riesz defect vanishes: it does so
exactly on the critical line. -/
theorem deningerArithmeticGradedRieszCovarianceDefect_single_apply_eq_zero_iff
    (q : XiZeroCopy) :
    deningerArithmeticGradedRieszCovarianceDefect
        (Finsupp.single q 1) q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [deningerArithmeticGradedRieszCovarianceDefect_apply]
  simp only [deningerArithmeticGradedRieszConjugation_apply,
    Finsupp.single_eq_same, map_one, mul_one]
  exact xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff (q.1 : ℂ)

/-- **Grade-separated Green criterion.**  If the two internal defects of the already-covariant
Green composite land in disjoint retained grades, then the odd Hodge defect vanishes before
composition and RH follows. -/
theorem riemannHypothesis_of_greenInternalDefectGradeSeparation
    (P Q : Submodule ℂ DeningerArithmeticGradedH1)
    (hdisjoint : Disjoint P Q)
    (hHodgeGrade : ∀ a,
      deningerArithmeticGradedHodgeCovarianceDefect
          (deningerArithmeticGradedRieszConjugation a) ∈ P)
    (hRieszGrade : ∀ a,
      deningerArithmeticGradedOrientedHodge.sigma
          (deningerArithmeticGradedRieszCovarianceDefect a) ∈ Q) :
    RiemannHypothesis := by
  rw [← deningerArithmeticGradedTheta_orientedHodge_iff_riemannHypothesis]
  intro b
  obtain ⟨a, rfl⟩ :=
    deningerArithmeticGradedRieszConjugation.surjective b
  apply sub_eq_zero.mp
  change
    deningerArithmeticGradedHodgeCovarianceDefect
      (deningerArithmeticGradedRieszConjugation a) = 0
  have hcancel := deningerArithmeticGreen_internalDefects_cancel a
  have hHodgeQ :
      deningerArithmeticGradedHodgeCovarianceDefect
          (deningerArithmeticGradedRieszConjugation a) ∈ Q := by
    have heq :
        deningerArithmeticGradedHodgeCovarianceDefect
            (deningerArithmeticGradedRieszConjugation a) =
          -deningerArithmeticGradedOrientedHodge.sigma
            (deningerArithmeticGradedRieszCovarianceDefect a) :=
      eq_neg_of_add_eq_zero_left hcancel
    rw [heq]
    exact Q.neg_mem (hRieszGrade a)
  exact
    (Submodule.disjoint_def.mp hdisjoint)
      _ (hHodgeGrade a) hHodgeQ

end

end RHTower
