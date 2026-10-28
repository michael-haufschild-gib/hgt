import GaloisForLFunctions.ArithmeticIndexDescent.TheSectionProjectionHasACanonicalLimit
import GaloisForLFunctions.ArithmeticIndexDescent.TheSourceWorkHasAClosedQuantumThreshold

/-!
# Source work detects negative squares after arithmetic completion

The canonical section complement is defined by an infinite source refinement,
but each finite negative subspace is already witnessed by actual smooth residual
tests at a finite stage. Its index therefore retains the strict transverse-energy
cost and the ordered damping/taper source-work detection law.
-/

open Filter RHTower Zeta23
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics HTGeometry

variable {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw0 : 0 < w)
  (hw : w ≤ fullSectionRatio * atomSpacing N)

/-- Completion creates no finite negative-index witness beyond actual smooth Weil tests. -/
theorem exists_actual_weilGram_dominating_completion_index {m : ℕ} (g : Fin m → realTests) :
    ∃ q : Fin m → realTests,
      hermNegIndex (completedSectionResidualGram hN hw0 hw g) ≤
        hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (fun j => cx (q j).1)) := by
  obtain ⟨S, hS⟩ := (eventually_negIndex_completedSectionResidual_le hN hw0 hw g).exists
  refine ⟨fun j => g j - finiteSectionProjection hN hw0 hw S (g j), ?_⟩
  simpa only [complexWeilMixed_eq_weilGram] using hS

/-- A positive completed residual index retains the strict global transverse-energy surplus. -/
theorem completedSectionIndex_eq_zero_or_lt_transverseEnergy {m : ℕ} (g : Fin m → realTests) :
    hermNegIndex (completedSectionResidualGram hN hw0 hw g) = 0 ∨
      (hermNegIndex (completedSectionResidualGram hN hw0 hw g) : ℝ≥0∞) <
        divisorTransverseEnergy := by
  obtain ⟨q, hq⟩ := exists_actual_weilGram_dominating_completion_index hN hw0 hw g
  rcases negIndex_eq_zero_or_lt_divisorTransverseEnergy (fun j => cx (q j).1)
      (fun j => cx_contDiff (q j).2.1) (fun j => cx_hasCompactSupport (q j).2.2) with hz | hE
  · left
    rw [hz] at hq
    exact le_antisymm hq (Nat.zero_le _)
  · right
    have hcast : (hermNegIndex (completedSectionResidualGram hN hw0 hw g) : ℝ≥0∞) ≤
        (hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (fun j => cx (q j).1)) : ℝ≥0∞) := by exact_mod_cast hq
    exact hcast.trans_lt hE

/-- Ordered finite arithmetic source work eventually exceeds every positive completed index. -/
theorem completedSectionIndex_eq_zero_or_eventually_sourceWork_gt {m : ℕ}
    (g : Fin m → realTests) :
    hermNegIndex (completedSectionResidualGram hN hw0 hw g) = 0 ∨
      ∀ᶠ n : ℕ in atTop, ∀ᶠ T : ℕ in atTop,
        (hermNegIndex (completedSectionResidualGram hN hw0 hw g) : ℝ≥0∞) <
          ENNReal.ofReal (xiTaperedSourceWork ((n : ℝ) + 4) T) := by
  obtain ⟨q, hq⟩ := exists_actual_weilGram_dominating_completion_index hN hw0 hw g
  rcases negIndex_eq_zero_or_eventually_sourceWork_gt_index (fun j => cx (q j).1)
      (fun j => cx_contDiff (q j).2.1) (fun j => cx_hasCompactSupport (q j).2.2) with hz | hwork
  · left
    rw [hz] at hq
    exact le_antisymm hq (Nat.zero_le _)
  · right
    have hcast : (hermNegIndex (completedSectionResidualGram hN hw0 hw g) : ℝ≥0∞) ≤
        (hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (fun j => cx (q j).1)) : ℝ≥0∞) := by exact_mod_cast hq
    filter_upwards [hwork] with n hn
    filter_upwards [hn] with T hT
    exact hcast.trans_lt hT

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.completedSectionIndex_eq_zero_or_lt_transverseEnergy
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.completedSectionIndex_eq_zero_or_eventually_sourceWork_gt
