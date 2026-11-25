import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # The measurable clock of successive low visits from the first robust crossing -/

open Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
open PrescribedTimes PrecisionReturns
noncomputable section

/-- Starting at any measurable date on a finite prefix, waiting until
the first affordable endpoint is a measurable operation. -/
theorem measurable_first_tenth (n s : ℕ) (a : (PrefixIndex n → ℝ) → ℝ) (ha : Measurable a) :
    Measurable (fun x => firstVisit (prefixGenerator n x) (a x) s (1/10)) := by
  let v x := firstVisit (prefixGenerator n x) (a x) s (1/10)
  have hwait : Measurable (fun x => v x-a x) := by
    apply measurable_of_Iic
    intro b
    have he : (fun x => v x-a x) ⁻¹' Iic b =
        {x | ∃ t∈Icc (a x) (a x+b), pathGateDistance n s x t≤1/10} := by
      ext x
      have hv := firstVisit_isLeast (prefixGenerator n x) (a x) s (by norm_num : (0:ℝ)<1/10)
      change v x-a x≤b ↔ _
      rw [sub_le_iff_le_add']
      constructor
      · intro hb
        exact ⟨v x,⟨hv.1.1,hb⟩,(hasProjectiveCircuitApproximation_iff_infDist _ s _).mp hv.1.2⟩
      · rintro ⟨t,ht,hfit⟩
        exact (hv.2 ⟨ht.1,(hasProjectiveCircuitApproximation_iff_infDist _ s _).mpr hfit⟩).trans ht.2
    rw [he]
    simpa only [add_zero] using measurable_shifted_window n s a ha 0 b
  simpa only [sub_add_cancel] using hwait.add ha

/-- Index zero is the first s-gate dip after the P-gate crossing at 9/80.
Each subsequent observation is the earliest affordable date at least one
time unit after the preceding observation. All visits use error 1/10. -/
def returnClock (n P s : ℕ) (x : PrefixIndex n → ℝ) : ℕ → ℝ
  | 0 => firstVisit (prefixGenerator n x) (crossingOrigin n P (9/80) x) s (1/10)
  | m+1 => firstVisit (prefixGenerator n x) (returnClock n P s x m+1) s (1/10)

theorem measurable_returnClock (n P s : ℕ) (m : ℕ) : Measurable (fun x => returnClock n P s x m) := by
  induction m with
  | zero => exact measurable_first_tenth _ _ _ (measurable_crossingOrigin _ _ _)
  | succ m ih => exact measurable_first_tenth _ _ _ (ih.add_const 1)

theorem returnClock_separated (n P s : ℕ) (x : PrefixIndex n → ℝ) (m : ℕ) :
    returnClock n P s x m+1≤returnClock n P s x (m+1) :=
  (firstVisit_isLeast _ _ _ (by norm_num : (0:ℝ)<1/10)).1.1

#print axioms measurable_returnClock
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
