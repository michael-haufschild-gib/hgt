import GaloisForLFunctions.RHTower.SPEQuantileRieszTerminalZeroAtomConnection

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

end RHTower
