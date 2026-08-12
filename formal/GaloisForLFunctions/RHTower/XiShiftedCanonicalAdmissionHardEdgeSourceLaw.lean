import GaloisForLFunctions.RHTower.XiShiftedHardEdgeHausdorffDiagonalLanding
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionConnection

/-!
# Canonical admission hard-edge arithmetic source law

The hard-edge producer becomes genuinely admission-sensitive by inserting the actual inverse-Hankel
monic admission before completed arithmetic formation.  Its coefficients need not have one sign.
Nevertheless, on every finite positive chamber its complete scaled-Hausdorff diagonal aggregate is
exactly twice the current orthogonal norm times adaptive Jacobi energy, hence is strictly positive.

This is a source identity, not a fixed linear report: both the polynomial producer and the weights
of its one-diagonal landing change with the shifted-Xi moment admission.
-/

open Complex Matrix Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Actual source-first hard-edge producer selected by shifted-Xi inverse-Hankel admission. -/
def xiShiftedCanonicalAdmissionHardEdgeSource (w : ℝ) (n : ℕ) : Polynomial ℝ :=
  let A := HTGeometry.monicMomentAdmissionPolynomial
    (xiShiftedRealMomentSequence w) n
  xiShiftedHardEdgeAdaptiveBilinearSource (w ^ 2) n n A A

/-- The literal completed mixed `P^sharp` arithmetic source is exactly the moment landing of the
canonical hard-edge producer. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_canonicalAdmission_eq_hardEdgeLanding
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) :
    xiShiftedAdaptiveMixedCompletedArithmeticSource w
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n) =
      HTGeometry.momentFunctional (xiShiftedRealMomentSequence w)
        (xiShiftedHardEdgeReciprocalUnclearing (w ^ 2) (2 * n + 2)
          (xiShiftedCanonicalAdmissionHardEdgeSource w n)) := by
  have hA :
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence w) n).natDegree ≤ n := by
    rw [HTGeometry.monicMomentAdmissionPolynomial_natDegree]
  simpa only [xiShiftedCanonicalAdmissionHardEdgeSource] using
    xiShiftedAdaptiveMixedCompletedArithmeticSource_eq_hardEdgeLanding hw hA

/-- **Admission-sensitive complete-diagonal source/energy law.**  The mixed-sign coefficients of
the actual hard-edge producer aggregate on one complete scaled-Hausdorff diagonal to the positive
Jacobi energy selected by the same current admission. -/
theorem xiShiftedCanonicalAdmissionHardEdgeSource_completeHausdorffDiagonal_eq_jacobiEnergy
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w)
      (n + 2)).PosDef) :
    let T := xiShiftedCanonicalAdmissionHardEdgeSource w n
    T.support.sum (fun j =>
      T.coeff j * ((w ^ 2) ^ j *
        scaledHausdorffMomentDifference (1 / (w ^ 2))
          (xiShiftedRealMomentSequence w) (2 * n + 2 - j) j)) =
      2 * HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) n *
        HTGeometry.adaptiveOrthoJacobiEnergy (xiShiftedRealMomentSequence w) n := by
  dsimp only [xiShiftedCanonicalAdmissionHardEdgeSource]
  have hA :
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence w) n).natDegree ≤ n := by
    rw [HTGeometry.monicMomentAdmissionPolynomial_natDegree]
  rw [← xiShiftedAdaptiveMixedCompletedArithmeticSource_eq_completeHausdorffDiagonal
      hw hA,
    xiShiftedAdaptiveMixedCompletedArithmeticSource_canonicalAdmission_eq_jacobiEnergy
      hw hn hH]

/-- Current admission forces strict positivity of the complete-diagonal aggregate even though
neither the hard-edge source coefficients nor individual Hausdorff diagonal entries have a
universal sign. -/
theorem xiShiftedCanonicalAdmissionHardEdgeSource_completeHausdorffDiagonal_pos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w)
      (n + 2)).PosDef) :
    let T := xiShiftedCanonicalAdmissionHardEdgeSource w n
    0 < T.support.sum (fun j =>
      T.coeff j * ((w ^ 2) ^ j *
        scaledHausdorffMomentDifference (1 / (w ^ 2))
          (xiShiftedRealMomentSequence w) (2 * n + 2 - j) j)) := by
  dsimp only
  rw [xiShiftedCanonicalAdmissionHardEdgeSource_completeHausdorffDiagonal_eq_jacobiEnergy
    hw hn hH]
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  exact mul_pos
    (mul_pos (by norm_num) (HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)))
    (HTGeometry.adaptiveOrthoJacobiEnergy_pos_below hbelow hn le_rfl)

/-- A nonpositive actual complete-diagonal source aggregate certifies that the next two-degree
Hankel chamber has already failed.  There is no admission-mismatch alternative because the source
polynomial is built from current inverse-Hankel admission by definition. -/
theorem not_hankelPosDef_of_canonicalAdmissionHardEdgeSource_completeHausdorffDiagonal_nonpos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hsource :
      let T := xiShiftedCanonicalAdmissionHardEdgeSource w n
      T.support.sum (fun j =>
        T.coeff j * ((w ^ 2) ^ j *
          scaledHausdorffMomentDifference (1 / (w ^ 2))
            (xiShiftedRealMomentSequence w) (2 * n + 2 - j) j)) ≤ 0) :
    ¬(HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w)
      (n + 2)).PosDef := by
  intro hH
  exact (not_lt_of_ge hsource)
    (xiShiftedCanonicalAdmissionHardEdgeSource_completeHausdorffDiagonal_pos hw hn hH)

end

end RHTower
