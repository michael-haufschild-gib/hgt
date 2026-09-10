import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionFisherBounds
import GaloisForLFunctions.HTGeometry.HausdorffMomentTheorem

/-!
# The positive Hausdorff source of a thermal collision history

The two surviving collision rates are nodes in the unit interval. Their
nonnegative weighted energies define a literal finite measure whose moments
are every shifted positive-time collision value. Existing Hausdorff
positivity and moment determinacy therefore apply without extra hypotheses.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory

/-- Positive source mass of the slow collision sector at a chosen time offset. -/
def egbFixedChargeAGibbsCollisionSlowSourceMass (n o : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : NNReal :=
  ⟨(4 / 9 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E,
    mul_nonneg (pow_nonneg (by norm_num) _) (egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E)⟩

/-- Positive source mass of the fast collision sector at a chosen time offset. -/
def egbFixedChargeAGibbsCollisionFastSourceMass (n o : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : NNReal :=
  ⟨(1 / 36 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E,
    mul_nonneg (pow_nonneg (by norm_num) _) (egbFixedChargeAGibbsFastModeEnergy_nonneg n β E)⟩

/-- The slow temporal collision rate, viewed as a Hausdorff node. -/
def egbFixedChargeAGibbsCollisionSlowNode : HausdorffSourceSpace :=
  ⟨4 / 9, by constructor <;> norm_num⟩

/-- The fast temporal collision rate, viewed as a Hausdorff node. -/
def egbFixedChargeAGibbsCollisionFastNode : HausdorffSourceSpace :=
  ⟨1 / 36, by constructor <;> norm_num⟩

/-- A concrete positive measure with exactly the two possible collision atoms. -/
def egbFixedChargeAGibbsCollisionHausdorffSource (n o : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : Measure HausdorffSourceSpace :=
  hausdorffAtomSource (egbFixedChargeAGibbsCollisionSlowSourceMass n o β E)
      egbFixedChargeAGibbsCollisionSlowNode +
    hausdorffAtomSource (egbFixedChargeAGibbsCollisionFastSourceMass n o β E)
      egbFixedChargeAGibbsCollisionFastNode

instance (n o : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) :
    IsFiniteMeasure (egbFixedChargeAGibbsCollisionHausdorffSource n o β E) := by
  unfold egbFixedChargeAGibbsCollisionHausdorffSource
  infer_instance

private theorem hausdorffMoment_add (μ ν : Measure HausdorffSourceSpace)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (m : ℕ) :
    hausdorffMoment (μ + ν) m = hausdorffMoment μ m + hausdorffMoment ν m := by
  exact MeasureTheory.integral_add_measure
    (by simpa using integrable_hausdorffDifferenceIntegrand μ 0 m)
    (by simpa using integrable_hausdorffDifferenceIntegrand ν 0 m)

/-- Every positive-time collision value is a moment of the explicit two-atom source. -/
theorem egbFixedChargeAGibbsCollisionHausdorffSource_moment (n o m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    hausdorffMoment (egbFixedChargeAGibbsCollisionHausdorffSource n o β E) m =
      egbFixedChargeAGibbsCollisionExcess n (m + o + 1) β E := by
  rw [egbFixedChargeAGibbsCollisionHausdorffSource, hausdorffMoment_add,
    hausdorffMoment_atom, hausdorffMoment_atom]
  change ((4 / 9 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E) * (4 / 9 : ℝ) ^ m +
    ((1 / 36 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) * (1 / 36 : ℝ) ^ m = _
  rw [egbFixedChargeAGibbsCollisionExcess_two_rate n (m + o) β E]
  have he : m + o + 1 = (o + 1) + m := by omega
  rw [he, pow_add (4 / 9 : ℝ) (o + 1) m, pow_add (1 / 36 : ℝ) (o + 1) m]
  ring

/-- Every shifted positive-time collision sequence is Hausdorff completely monotone. -/
theorem egbFixedChargeAGibbsCollisionExcess_hausdorff_completelyMonotone (n o : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    HausdorffCompletelyMonotone (fun m : ℕ => egbFixedChargeAGibbsCollisionExcess n (m + o + 1) β E) := by
  have he : hausdorffMoment (egbFixedChargeAGibbsCollisionHausdorffSource n o β E) =
      (fun m : ℕ => egbFixedChargeAGibbsCollisionExcess n (m + o + 1) β E) := by
    funext m
    exact egbFixedChargeAGibbsCollisionHausdorffSource_moment n o m β E
  rw [← he]
  exact hausdorffMoment_isCompletelyMonotone _

/-- There is exactly one finite positive Hausdorff measure with the shifted collision moments. -/
theorem egbFixedChargeAGibbsCollisionExcess_unique_hausdorff_source (n o : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    ∃! ν : { μ : Measure HausdorffSourceSpace // IsFiniteMeasure μ },
      hausdorffMoment ν.1 =
        (fun m : ℕ => egbFixedChargeAGibbsCollisionExcess n (m + o + 1) β E) := by
  exact existsUnique_hausdorffSource_of_completelyMonotone
    (egbFixedChargeAGibbsCollisionExcess_hausdorff_completelyMonotone n o β E)

/-- The positive source vanishes exactly at equilibrium, with both surviving sector energies zero. -/
theorem egbFixedChargeAGibbsCollisionHausdorffSource_zero_iff (n o : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionHausdorffSource n o β E = 0 ↔
      egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 := by
  constructor
  · intro hs
    have hm := egbFixedChargeAGibbsCollisionHausdorffSource_moment n o 0 β E
    rw [hs] at hm
    have hc : egbFixedChargeAGibbsCollisionExcess n (o + 1) β E = 0 := by
      simpa [hausdorffMoment] using hm.symm
    exact (egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n o β E).mp hc
  · rintro ⟨ha, hb⟩
    have hA : egbFixedChargeAGibbsCollisionSlowSourceMass n o β E = 0 := by
      apply Subtype.ext
      change (4 / 9 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E = 0
      rw [ha, mul_zero]
    have hB : egbFixedChargeAGibbsCollisionFastSourceMass n o β E = 0 := by
      apply Subtype.ext
      change (1 / 36 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E = 0
      rw [hb, mul_zero]
    simp only [egbFixedChargeAGibbsCollisionHausdorffSource, hA, hB,
      hausdorffAtomSource, zero_smul, add_zero]

/-- Equality of the concrete sources is exactly equality of their entire shifted collision histories. -/
theorem egbFixedChargeAGibbsCollisionHausdorffSource_eq_iff_history (n o : ℕ) (β γ : ℝ)
    (E F : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionHausdorffSource n o β E =
      egbFixedChargeAGibbsCollisionHausdorffSource n o γ F ↔
      ∀ m : ℕ, egbFixedChargeAGibbsCollisionExcess n (m + o + 1) β E =
        egbFixedChargeAGibbsCollisionExcess n (m + o + 1) γ F := by
  constructor
  · intro hs m
    rw [← egbFixedChargeAGibbsCollisionHausdorffSource_moment n o m β E,
      ← egbFixedChargeAGibbsCollisionHausdorffSource_moment n o m γ F, hs]
  · intro hm
    apply hausdorffSource_eq_of_moments_eq
    intro m
    rw [egbFixedChargeAGibbsCollisionHausdorffSource_moment,
      egbFixedChargeAGibbsCollisionHausdorffSource_moment]
    exact hm m

end
end GaloisForLFunctions.HTGeometry
