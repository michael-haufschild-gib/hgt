import GaloisForLFunctions.RHTower.MassShiftedThreePointOrbitPolarity
import GaloisForLFunctions.RHTower.PreDivisorCyclicSourceSector
import GaloisForLFunctions.RHTower.XiKoszulMutualStatisticsSuperselection

/-!
# Mixed Xi defects: direct-source curvature and reciprocal Krein charge

The nodal/BV description and the confluent Hankel description use reciprocal spectral
polarizations.  The former reads the imaginary part of the squared centered Xi node through the
mixed arithmetic source jet.  The latter reads the imaginary part of its inverse through a
negative confluent minor.

This file proves that they are not merely zero-set-equivalent.  Their charges obey the exact
transduction law

`minor = -mixedJet² / (4 * normSq(squaredNode)³)`.

Consequently one hypothetical off-critical Xi copy has a falsifiable four-part passport: nonzero
mixed source curvature, strict reciprocal-Hankel negativity, death of the pre-divisor cyclic
source class, and failure of order-independent Koszul descent.  Separated-point orbit positivity
still holds, so it is explicitly excluded as a detector of this defect.

This is a structural identification, not a producer of nodal purity or an RH proof.
-/

open Complex Matrix

namespace RHTower

noncomputable section

/-- **Exact direct/reciprocal charge transduction.**  Confluent Krein charge is the square of the
mixed nodal source curvature, transported through the inverse squared-node polarization. -/
theorem xiOrbitConfluentMinor_eq_neg_mixedSourceJet_sq_div (q : XiZeroCopy) :
    xiOrbitConfluentMinor q =
      -(xiReflectedPhaseNeutralMixedJet q ^ (2 : ℕ)) /
        (4 * Complex.normSq (xiSquaredNode q) ^ (3 : ℕ)) := by
  rw [xiOrbitConfluentMinor_eq,
    xiZeroCopyReciprocalSquare_eq_inv_node,
    Complex.inv_im, Complex.normSq_inv,
    xiSquaredNode_im_eq_neg_half_mul_reflectedPhaseNeutralMixedJet]
  have hnorm : Complex.normSq (xiSquaredNode q) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr (xiSquaredNode_ne_zero q))
  field_simp [hnorm]
  ring

/-- Denominator-free form: direct mixed curvature and reciprocal negative charge differ only by
the strictly positive sixth-power radial transport. -/
theorem four_mul_nodeNormSq_cube_mul_xiOrbitConfluentMinor_eq_neg_mixedSourceJet_sq
    (q : XiZeroCopy) :
    4 * Complex.normSq (xiSquaredNode q) ^ (3 : ℕ) * xiOrbitConfluentMinor q =
      -(xiReflectedPhaseNeutralMixedJet q ^ (2 : ℕ)) := by
  rw [xiOrbitConfluentMinor_eq_neg_mixedSourceJet_sq_div]
  have hnorm : Complex.normSq (xiSquaredNode q) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr (xiSquaredNode_ne_zero q))
  field_simp [hnorm]

/-- Pure nodal curvature is exactly the null wall of the confluent Krein detector. -/
theorem xiOrbitConfluentMinor_eq_zero_iff_mixedSourceJet_eq_zero (q : XiZeroCopy) :
    xiOrbitConfluentMinor q = 0 ↔
      xiReflectedPhaseNeutralMixedJet q = 0 := by
  rw [xiOrbitConfluentMinor_eq_zero_iff,
    ← xiNodalDefectSuperselected_iff_re_eq_half,
    xiNodalDefectSuperselected_iff_mixedSourceJet_eq_zero]

/-- A nonzero mixed source curvature is exactly a strict negative confluent charge. -/
theorem xiOrbitConfluentMinor_neg_iff_mixedSourceJet_ne_zero (q : XiZeroCopy) :
    xiOrbitConfluentMinor q < 0 ↔
      xiReflectedPhaseNeutralMixedJet q ≠ 0 := by
  constructor
  · intro hneg hzero
    exact (ne_of_lt hneg)
      ((xiOrbitConfluentMinor_eq_zero_iff_mixedSourceJet_eq_zero q).2 hzero)
  · intro hjet
    exact lt_of_le_of_ne (xiOrbitConfluentMinor_nonpos q)
      (fun hzero => hjet
        ((xiOrbitConfluentMinor_eq_zero_iff_mixedSourceJet_eq_zero q).1 hzero))

/-- Strict confluent negativity detects precisely failure of nodal superselection. -/
theorem xiOrbitConfluentMinor_neg_iff_not_nodalDefectSuperselected (q : XiZeroCopy) :
    xiOrbitConfluentMinor q < 0 ↔
      ¬ XiNodalDefectSuperselected q := by
  rw [xiOrbitConfluentMinor_neg_iff_mixedSourceJet_ne_zero]
  exact not_congr (xiNodalDefectSuperselected_iff_mixedSourceJet_eq_zero q).symm

/-- The reciprocal detector is null exactly where the universal pre-divisor cyclic source atom
survives.  This comparison is valid at every cyclic degree at least two. -/
theorem xiOrbitConfluentMinor_eq_zero_iff_preDivisorSourceClass_survives
    {n : ℕ} (hn : 2 ≤ n) (q : XiZeroCopy) :
    xiOrbitConfluentMinor q = 0 ↔
      preDivisorCyclicSourceSectorClass n (q.1 : ℂ) ≠ 0 := by
  rw [xiOrbitConfluentMinor_eq_zero_iff,
    preDivisorCyclicSourceSectorClass_ne_zero_iff hn]

/-- Strict negative charge is exactly the obstruction to order-independent graded-skew source
descent. -/
theorem xiOrbitConfluentMinor_neg_iff_no_orderIndependentKoszulLift (q : XiZeroCopy) :
    xiOrbitConfluentMinor q < 0 ↔
      ¬ Nonempty (XiOrderIndependentKoszulLift q) := by
  rw [xiOrbitConfluentMinor_neg_iff_not_nodalDefectSuperselected]
  exact not_congr (nonempty_xiOrderIndependentKoszulLift_iff q).symm

/-- Four independent corpus observables predicted for one mixed Xi defect. -/
def XiMixedDefectPassport (n : ℕ) (q : XiZeroCopy) : Prop :=
  xiReflectedPhaseNeutralMixedJet q ≠ 0 ∧
    xiOrbitConfluentMinor q < 0 ∧
    preDivisorCyclicSourceSectorClass n (q.1 : ℂ) = 0 ∧
    ¬ Nonempty (XiOrderIndependentKoszulLift q)

/-- **Falsifiable synthesis.**  The four-part passport is neither stronger nor weaker than being
a mixed nodal defect: any disagreement among its source, cohomological, statistical, and Krein
components would refute the proposed identification. -/
theorem xiMixedDefectPassport_iff_not_nodalDefectSuperselected
    {n : ℕ} (hn : 2 ≤ n) (q : XiZeroCopy) :
    XiMixedDefectPassport n q ↔ ¬ XiNodalDefectSuperselected q := by
  constructor
  · intro h
    exact (xiOrbitConfluentMinor_neg_iff_not_nodalDefectSuperselected q).1 h.2.1
  · intro hpure
    have hminor : xiOrbitConfluentMinor q < 0 :=
      (xiOrbitConfluentMinor_neg_iff_not_nodalDefectSuperselected q).2 hpure
    have hjet : xiReflectedPhaseNeutralMixedJet q ≠ 0 :=
      (xiOrbitConfluentMinor_neg_iff_mixedSourceJet_ne_zero q).1 hminor
    have hclass : preDivisorCyclicSourceSectorClass n (q.1 : ℂ) = 0 := by
      by_contra hne
      have hminorzero :=
        (xiOrbitConfluentMinor_eq_zero_iff_preDivisorSourceClass_survives hn q).2 hne
      exact (ne_of_lt hminor) hminorzero
    have hlift : ¬ Nonempty (XiOrderIndependentKoszulLift q) :=
      (xiOrbitConfluentMinor_neg_iff_no_orderIndependentKoszulLift q).1 hminor
    exact ⟨hjet, hminor, hclass, hlift⟩

/-- The passport is exactly off-critical placement, but its four components give independently
checkable failure modes rather than one repeated coordinate equality. -/
theorem xiMixedDefectPassport_iff_re_ne_half
    {n : ℕ} (hn : 2 ≤ n) (q : XiZeroCopy) :
    XiMixedDefectPassport n q ↔ (q.1 : ℂ).re ≠ 1 / 2 := by
  rw [xiMixedDefectPassport_iff_not_nodalDefectSuperselected hn,
    not_congr (xiNodalDefectSuperselected_iff_re_eq_half q)]

/-- **Hostile polarization test.**  A hypothetical off-critical Xi copy would pass the separated
positive-definite orbit test while simultaneously carrying the complete mixed-defect passport.
Thus positivity without source-selected confluent polarization cannot prove purity. -/
theorem xiOffCriticalZeroCopy_separatedPositive_mixedDefectFalsifier
    {n : ℕ} (hn : 2 ≤ n) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    Matrix.PosDef (orbitMatrix (xiOrbitDetuning q) (xiOrbitCoupling q)) ∧
      XiMixedDefectPassport n q :=
  ⟨xiOrbitMatrix_posDef q,
    (xiMixedDefectPassport_iff_re_ne_half hn q).2 hoff⟩

end


end RHTower
