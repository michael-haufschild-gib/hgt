import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFullTimeCollision
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionHausdorffSource

/-! # The positive Hausdorff source of the entire thermal collision history -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory

def egbFixedChargeAGibbsFullCollisionErasedMass (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : NNReal :=
  ⟨egbFixedChargeAGibbsDiscardedModeEnergy n β E, egbFixedChargeAGibbsDiscardedModeEnergy_nonneg n β E⟩

def egbFixedChargeAGibbsFullCollisionSlowMass (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : NNReal :=
  ⟨egbFixedChargeAGibbsSlowModeEnergy n β E, egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E⟩

def egbFixedChargeAGibbsFullCollisionFastMass (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : NNReal :=
  ⟨egbFixedChargeAGibbsFastModeEnergy n β E, egbFixedChargeAGibbsFastModeEnergy_nonneg n β E⟩

/-- The endpoint atom represents modes annihilated in one transition. -/
def egbFixedChargeAGibbsCollisionZeroNode : HausdorffSourceSpace :=
  ⟨0, by constructor <;> norm_num⟩

/-- A finite positive source at exactly the three possible full-history rates. -/
def egbFixedChargeAGibbsFullCollisionHausdorffSource (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : Measure HausdorffSourceSpace :=
  hausdorffAtomSource (egbFixedChargeAGibbsFullCollisionErasedMass n β E) egbFixedChargeAGibbsCollisionZeroNode +
  hausdorffAtomSource (egbFixedChargeAGibbsFullCollisionSlowMass n β E) egbFixedChargeAGibbsCollisionSlowNode +
  hausdorffAtomSource (egbFixedChargeAGibbsFullCollisionFastMass n β E) egbFixedChargeAGibbsCollisionFastNode

instance (n : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) :
    IsFiniteMeasure (egbFixedChargeAGibbsFullCollisionHausdorffSource n β E) := by
  unfold egbFixedChargeAGibbsFullCollisionHausdorffSource
  infer_instance

private theorem moment_add (μ ν : Measure HausdorffSourceSpace)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (m : ℕ) :
    hausdorffMoment (μ + ν) m = hausdorffMoment μ m + hausdorffMoment ν m := by
  exact MeasureTheory.integral_add_measure
    (by simpa using integrable_hausdorffDifferenceIntegrand μ 0 m)
    (by simpa using integrable_hausdorffDifferenceIntegrand ν 0 m)

/-- Every collision observation, including time zero, is a moment of the explicit positive source. -/
theorem egbFixedChargeAGibbsFullCollisionHausdorffSource_moment (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    hausdorffMoment (egbFixedChargeAGibbsFullCollisionHausdorffSource n β E) m =
      egbFixedChargeAGibbsCollisionExcess n m β E := by
  rw [egbFixedChargeAGibbsFullCollisionHausdorffSource, moment_add, moment_add,
    hausdorffMoment_atom, hausdorffMoment_atom, hausdorffMoment_atom,
    egbFixedChargeAGibbsCollisionExcess_full_time_three_rate]
  change egbFixedChargeAGibbsDiscardedModeEnergy n β E * (0 : ℝ) ^ m +
    egbFixedChargeAGibbsSlowModeEnergy n β E * (4 / 9 : ℝ) ^ m +
    egbFixedChargeAGibbsFastModeEnergy n β E * (1 / 36 : ℝ) ^ m = _
  ring

/-- The full history lies in the Hausdorff positivity cone, without removing its initial observation. -/
theorem egbFixedChargeAGibbsCollisionExcess_full_completelyMonotone (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    HausdorffCompletelyMonotone (fun m : ℕ => egbFixedChargeAGibbsCollisionExcess n m β E) := by
  have he : hausdorffMoment (egbFixedChargeAGibbsFullCollisionHausdorffSource n β E) =
      (fun m : ℕ => egbFixedChargeAGibbsCollisionExcess n m β E) := by
    funext m
    exact egbFixedChargeAGibbsFullCollisionHausdorffSource_moment n m β E
  rw [← he]
  exact hausdorffMoment_isCompletelyMonotone _

/-- The complete collision history has a unique finite positive Hausdorff source. -/
theorem egbFixedChargeAGibbsCollisionExcess_unique_full_hausdorff_source (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    ∃! ν : { μ : Measure HausdorffSourceSpace // IsFiniteMeasure μ },
      hausdorffMoment ν.1 = (fun m : ℕ => egbFixedChargeAGibbsCollisionExcess n m β E) := by
  exact existsUnique_hausdorffSource_of_completelyMonotone
    (egbFixedChargeAGibbsCollisionExcess_full_completelyMonotone n β E)

/-- Three observations determine the entire positive source, including its erased atom. -/
theorem egbFixedChargeAGibbsFullCollisionHausdorffSource_eq_iff_three_values (n : ℕ) (β γ : ℝ)
    (E F : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsFullCollisionHausdorffSource n β E =
      egbFixedChargeAGibbsFullCollisionHausdorffSource n γ F ↔
      egbFixedChargeAGibbsCollisionExcess n 0 β E = egbFixedChargeAGibbsCollisionExcess n 0 γ F ∧
      egbFixedChargeAGibbsCollisionExcess n 1 β E = egbFixedChargeAGibbsCollisionExcess n 1 γ F ∧
      egbFixedChargeAGibbsCollisionExcess n 2 β E = egbFixedChargeAGibbsCollisionExcess n 2 γ F := by
  rw [← egbFixedChargeAGibbsCollisionExcess_full_history_iff_three_values]
  constructor
  · intro h m
    rw [← egbFixedChargeAGibbsFullCollisionHausdorffSource_moment,
      ← egbFixedChargeAGibbsFullCollisionHausdorffSource_moment, h]
  · intro h
    apply hausdorffSource_eq_of_moments_eq
    intro m
    rw [egbFixedChargeAGibbsFullCollisionHausdorffSource_moment,
      egbFixedChargeAGibbsFullCollisionHausdorffSource_moment, h m]

/-- Positive shifts of the full moment sequence recover exactly the previously constructed two-atom histories. -/
theorem egbFixedChargeAGibbsFullCollisionHausdorffSource_positive_shift_moment (n o m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    hausdorffMoment (egbFixedChargeAGibbsFullCollisionHausdorffSource n β E) (m + o + 1) =
      hausdorffMoment (egbFixedChargeAGibbsCollisionHausdorffSource n o β E) m := by
  rw [egbFixedChargeAGibbsFullCollisionHausdorffSource_moment,
    egbFixedChargeAGibbsCollisionHausdorffSource_moment]

end
end GaloisForLFunctions.HTGeometry
