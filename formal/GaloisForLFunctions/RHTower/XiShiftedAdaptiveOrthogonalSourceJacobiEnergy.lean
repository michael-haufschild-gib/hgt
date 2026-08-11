import GaloisForLFunctions.HTGeometry.AdaptiveOrthogonalSourceJacobiEnergy
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryAdaptiveArithmeticSourceLaw

/-!
# Jacobi energy of the adaptive completed shifted-Xi source

This module connects the generic orthogonal-source theorem to the literal completed `P^sharp`
arithmetic source.  When the shifted-Xi moments lie in a positive moment chamber, the moving monic
admission is chosen before formation and its completed mixed amplitude is exactly twice its positive
Jacobi energy.  This is not a fixed reporter and no post-aggregation orientation is used.
-/

open Complex Matrix MeasureTheory Set Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Shifted-Xi real moment sequence at square-root mass `w`. -/
def xiShiftedRealMomentSequence (w : ℝ) : ℕ → ℝ :=
  fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re

theorem xiShiftedBoundaryAdaptiveShearPolynomial_monicOrtho
    (w : ℝ) (n : ℕ) :
    xiShiftedBoundaryAdaptiveShearPolynomial
        (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n) =
      HTGeometry.adaptiveOrthoSourcePolynomial (xiShiftedRealMomentSequence w) n := by
  simp only [xiShiftedBoundaryAdaptiveShearPolynomial,
    xiShiftedBoundaryShiftedEuler, HTGeometry.adaptiveOrthoSourcePolynomial, C_1, one_mul]

/-- Exact source-first arithmetic law in a positive shifted-Xi moment chamber. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_monicOrtho_eq_jacobiEnergy
    {w : ℝ} (hw : 1 / 2 < w)
    (hpos : HTGeometry.PositiveMomentForm (xiShiftedRealMomentSequence w))
    {n : ℕ} (hn : 0 < n) :
    xiShiftedAdaptiveMixedCompletedArithmeticSource w
        (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n) =
      2 * HTGeometry.monicOrthoNorm (xiShiftedRealMomentSequence w) n *
        HTGeometry.adaptiveOrthoJacobiEnergy (xiShiftedRealMomentSequence w) n := by
  let P := HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n
  have hsquare : 0 < w ^ 2 := sq_pos_of_pos (by linarith : 0 < w)
  have haggregate := xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_arithmeticSource hw P
  have hshear := xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_two_shear hsquare P
  have hsource :=
    HTGeometry.momentFunctional_adaptiveOrthoSourcePolynomial_eq_jacobiEnergy hpos hn
  rw [← haggregate, hshear]
  change 2 * HTGeometry.momentFunctional (xiShiftedRealMomentSequence w)
      (xiShiftedBoundaryAdaptiveShearPolynomial P) = _
  rw [xiShiftedBoundaryAdaptiveShearPolynomial_monicOrtho,
    hsource]
  ring

/-- Positive-chamber moving admission produces a strictly positive completed arithmetic source. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_monicOrtho_pos
    {w : ℝ} (hw : 1 / 2 < w)
    (hpos : HTGeometry.PositiveMomentForm (xiShiftedRealMomentSequence w))
    {n : ℕ} (hn : 0 < n) :
    0 < xiShiftedAdaptiveMixedCompletedArithmeticSource w
      (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n) := by
  rw [xiShiftedAdaptiveMixedCompletedArithmeticSource_monicOrtho_eq_jacobiEnergy
    hw hpos hn]
  exact mul_pos
    (mul_pos (by norm_num) (HTGeometry.monicOrthoNorm_pos hpos n))
    (HTGeometry.adaptiveOrthoJacobiEnergy_pos hpos hn)

/-- Finite-block exact law: no positivity assumption beyond the `(n+2)` Hankel face. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_monicOrtho_eq_jacobiEnergy_of_hankelPosDef
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    xiShiftedAdaptiveMixedCompletedArithmeticSource w
        (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n) =
      2 * HTGeometry.monicOrthoNorm (xiShiftedRealMomentSequence w) n *
        HTGeometry.adaptiveOrthoJacobiEnergy (xiShiftedRealMomentSequence w) n := by
  let P := HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hsquare : 0 < w ^ 2 := sq_pos_of_pos (by linarith : 0 < w)
  have haggregate := xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_arithmeticSource hw P
  have hshear := xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_two_shear hsquare P
  have hsource :=
    HTGeometry.momentFunctional_adaptiveOrthoSourcePolynomial_eq_jacobiEnergy_below
      hbelow hn (le_refl (n + 2))
  rw [← haggregate, hshear]
  change 2 * HTGeometry.momentFunctional (xiShiftedRealMomentSequence w)
      (xiShiftedBoundaryAdaptiveShearPolynomial P) = _
  rw [xiShiftedBoundaryAdaptiveShearPolynomial_monicOrtho, hsource]
  ring

/-- One finite positive shifted-Xi Hankel block forces the admitted completed source positive. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_monicOrtho_pos_of_hankelPosDef
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    0 < xiShiftedAdaptiveMixedCompletedArithmeticSource w
      (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n) := by
  rw [xiShiftedAdaptiveMixedCompletedArithmeticSource_monicOrtho_eq_jacobiEnergy_of_hankelPosDef
    hw hn hH]
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  exact mul_pos
    (mul_pos (by norm_num) (HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)))
    (HTGeometry.adaptiveOrthoJacobiEnergy_pos_below hbelow hn le_rfl)

/-- Exact obstruction locus for any negative fixed-amplitude event.  Either the next two-degree
Hankel block has already left the positive chamber, or the fixed flag is no longer the moving
admission. -/
theorem neg_adaptiveArithmeticSource_forces_hankelFailure_or_admissionMismatch
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n) (A : Polynomial ℝ)
    (hneg : xiShiftedAdaptiveMixedCompletedArithmeticSource w A < 0) :
    ¬(HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w) (n + 2)).PosDef ∨
      A ≠ HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n := by
  by_cases hH :
      (HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w) (n + 2)).PosDef
  · right
    intro hA
    rw [hA] at hneg
    exact (not_lt_of_ge
      (xiShiftedAdaptiveMixedCompletedArithmeticSource_monicOrtho_pos_of_hankelPosDef
        hw hn hH).le) hneg
  · exact Or.inl hH

end

end RHTower
