import GaloisForLFunctions.RHTower.SPEQuantileRieszTerminalZeroAtomConnection
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantileParabolicNormalizedVarianceFlow

/-!
# Prime-power support of the SP-E strict-cross history

The physical moving-wall transport and its canonical terminal connection are
not independently controlled errors.  Their cumulative signed current is
exactly supported on literal prime-power admissions.  Every retained summand
contains the admitted atom's exterior interaction with full two-moment history
and both orientations of the displacement-debt admission.

This is an identity only.  It creates no positivity, scalarization, or
cofinal bound; the resulting prime-power history is the exact object that a
source-faithful SP-E/P transport must control.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace RHTower

/-- The literal signed curvature carried by the admission at `K + 3`. -/
noncomputable def speQuantileRieszPrimePowerHistoryCurvature (K : ℕ) : ℝ :=
  -2 * criticalMellinAtomWeight (K + 3) *
      (ccmActualHeadTwoMomentExteriorPairing
          (ccmActualHeadMatchedQuantileAtomExteriorDirection (K + 3))
          (ccmActualHeadMatchedQuantileCentroidDisplacementMomentVector K) +
        ccmActualHeadMatchedPolarCentroid (K + 3) *
          ccmActualHeadTwoMomentExteriorPairing
            (ccmActualHeadMatchedQuantileDisplacementMomentVector K)
            (ccmActualHeadMatchedQuantileAtomExteriorDirection (K + 3))) -
    ∑ m ∈ Finset.range (K + 1),
      (ccmActualHeadMatchedQuantileParabolicDisplacementDebt (m + 2) (K + 3) +
        ccmActualHeadMatchedQuantileParabolicDisplacementDebt (K + 3) (m + 2))

/-- The one-step physical transport plus terminal connection is the exact
prime-power history curvature, retaining the signed exterior and both debt
orientations. -/
theorem speQuantileRieszPhysicalWallDynamicSourceTransport_add_terminalConnectionIncrement_eq_primePowerHistoryCurvature
    (K : ℕ) :
    speQuantileRieszPhysicalWallDynamicSourceTransport K +
      (speQuantileRieszCanonicalTerminalConnection (K + 1) -
        speQuantileRieszCanonicalTerminalConnection K) =
      speQuantileRieszPrimePowerHistoryCurvature K := by
  exact speQuantileRieszPhysicalWallDynamicSourceTransport_add_terminalConnectionIncrement_eq_exteriorHistory_sub_debtAdmission K

/-- At a non-prime-power admission the complete signed history curvature is
exactly zero. -/
theorem speQuantileRieszPrimePowerHistoryCurvature_eq_zero_of_not_isPrimePow
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    speQuantileRieszPrimePowerHistoryCurvature K = 0 := by
  rw [← speQuantileRieszPhysicalWallDynamicSourceTransport_add_terminalConnectionIncrement_eq_primePowerHistoryCurvature]
  rw [speQuantileRieszPhysicalWallDynamicSourceTransport_add_terminalConnectionIncrement_eq_strictCross_increment,
    ccmActualHeadMatchedQuantileParabolicStrictCross_succ_eq_of_not_isPrimePow K hK]
  ring

/-- Cumulative physical transport and terminal connection reduce exactly to
the literal prime-power support; no zero-atom, endpoint, or gauge term remains. -/
theorem sum_speQuantileRieszDynamicSourceTransport_add_terminalConnectionIncrement_eq_primePowerHistory
    (K : ℕ) :
    (∑ n ∈ Finset.range K,
      (speQuantileRieszPhysicalWallDynamicSourceTransport n +
        (speQuantileRieszCanonicalTerminalConnection (n + 1) -
          speQuantileRieszCanonicalTerminalConnection n))) =
      ∑ n ∈ (Finset.range K).filter (fun n => IsPrimePow (n + 3)),
        speQuantileRieszPrimePowerHistoryCurvature n := by
  rw [Finset.sum_congr rfl
    (fun n _ => speQuantileRieszPhysicalWallDynamicSourceTransport_add_terminalConnectionIncrement_eq_primePowerHistoryCurvature n)]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnf
  apply speQuantileRieszPrimePowerHistoryCurvature_eq_zero_of_not_isPrimePow
  intro hp
  exact hnf (Finset.mem_filter.mpr ⟨hn,hp⟩)

/-- The strict-cross covariance--debt source itself is its initial value plus
the complete signed prime-power history. -/
theorem ccmActualHeadMatchedQuantileParabolicStrictCross_sub_zero_eq_primePowerHistory
    (K : ℕ) :
    ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) -
      ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal 0)
        (ccmActualHeadMatchedQuantileParabolicSourceBoundary 0) =
      ∑ n ∈ (Finset.range K).filter (fun n => IsPrimePow (n + 3)),
        speQuantileRieszPrimePowerHistoryCurvature n := by
  rw [← sum_speQuantileRieszDynamicSourceTransport_add_terminalConnectionIncrement_eq_primePowerHistory]
  rw [Finset.sum_congr rfl
    (fun n _ => speQuantileRieszPhysicalWallDynamicSourceTransport_add_terminalConnectionIncrement_eq_strictCross_increment n)]
  symm
  exact Finset.sum_range_sub (fun n =>
    ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal n)
      (ccmActualHeadMatchedQuantileParabolicSourceBoundary n)) K

/-- **Scalar prime-power history law.**  The complete signed exterior-history-minus-debt
curvature is not an irreducibly two-vector control problem.  It is the newly admitted literal
mass times one scalar discrete barrier: previous normalized variance defect minus the preceding
physical mass times the full centred affine displacement jet.  Every prime, polar, terminal and
debt coefficient is retained. -/
theorem speQuantileRieszPrimePowerHistoryCurvature_eq_scalarVarianceBarrier
    (K : ℕ) :
    speQuantileRieszPrimePowerHistoryCurvature K =
      criticalMellinAtomWeight (K + 3) *
        (ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K -
          ccmActualHeadParabolicMass K *
            (2 * ccmActualHeadMatchedQuantileParabolicCenteredMatchedOffset K *
                ccmActualHeadMatchedQuantileParabolicCenteredDisplacement K +
              ccmActualHeadMatchedQuantileParabolicCenteredDisplacement K ^ (2 : ℕ))) := by
  have hmass : ccmActualHeadParabolicMass (K + 1) =
      ccmActualHeadParabolicMass K + criticalMellinAtomWeight (K + 3) := by
    unfold ccmActualHeadParabolicMass
    rw [Finset.sum_range_succ]
  have hM : ccmActualHeadParabolicMass K ≠ 0 :=
    (ccmActualHeadParabolicMass_pos K).ne'
  have hMnext : ccmActualHeadParabolicMass (K + 1) ≠ 0 :=
    (ccmActualHeadParabolicMass_pos (K + 1)).ne'
  rw [← speQuantileRieszPhysicalWallDynamicSourceTransport_add_terminalConnectionIncrement_eq_primePowerHistoryCurvature]
  rw [speQuantileRieszPhysicalWallDynamicSourceTransport_add_terminalConnectionIncrement_eq_strictCross_increment]
  have hsource (j : ℕ) :
      ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal j)
          (ccmActualHeadMatchedQuantileParabolicSourceBoundary j) =
        ccmActualHeadParabolicMass j *
          ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect j := by
    rw [ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect_eq_sourceCurrent]
    field_simp [(ccmActualHeadParabolicMass_pos j).ne']
  rw [hsource (K + 1), hsource K]
  rw [show ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect (K + 1) =
      ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K +
        ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux K by
      linarith [ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect_succ_sub_eq_flux K]]
  rw [ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux_eq_centered_signed_increment,
    hmass]
  have hMsum : ccmActualHeadParabolicMass K + criticalMellinAtomWeight (K + 3) ≠ 0 := by
    rw [← hmass]
    exact hMnext
  field_simp [hM, hMsum]
  ring

/-- On a literal prime-power admission, nonnegative full history curvature is exactly the scalar
variance barrier from `speQuantileRieszPrimePowerHistoryCurvature_eq_scalarVarianceBarrier`.
Thus the remaining uniform prime-power-history problem has one sign-bearing datum per active
admission, rather than separate exterior and debt inequalities. -/
theorem speQuantileRieszPrimePowerHistoryCurvature_nonneg_iff_scalarVarianceBarrier
    (K : ℕ) (hK : IsPrimePow (K + 3)) :
    0 ≤ speQuantileRieszPrimePowerHistoryCurvature K ↔
      0 ≤ ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K -
        ccmActualHeadParabolicMass K *
          (2 * ccmActualHeadMatchedQuantileParabolicCenteredMatchedOffset K *
              ccmActualHeadMatchedQuantileParabolicCenteredDisplacement K +
            ccmActualHeadMatchedQuantileParabolicCenteredDisplacement K ^ (2 : ℕ)) := by
  rw [speQuantileRieszPrimePowerHistoryCurvature_eq_scalarVarianceBarrier]
  exact mul_nonneg_iff_of_pos_left (criticalMellinAtomWeight_pos hK)

end RHTower
