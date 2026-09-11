import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFullConeSource

/-! # The initial moment repairs exactly the information erased from all later moments -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory

/-- The first three moments reconstruct every prescribed mass by explicit linear formulas. -/
theorem egbFixedChargeAGibbsFullConeSource_masses_from_moments (R A B : NNReal) :
    (R : ℝ) = hausdorffMoment (egbFixedChargeAGibbsFullConeSource R A B) 0 -
      (153 / 4 : ℝ) * hausdorffMoment (egbFixedChargeAGibbsFullConeSource R A B) 1 +
      81 * hausdorffMoment (egbFixedChargeAGibbsFullConeSource R A B) 2 ∧
    (A : ℝ) = (27 / 5 : ℝ) * (hausdorffMoment (egbFixedChargeAGibbsFullConeSource R A B) 2 -
      (1 / 36 : ℝ) * hausdorffMoment (egbFixedChargeAGibbsFullConeSource R A B) 1) ∧
    (B : ℝ) = (432 / 5 : ℝ) * ((4 / 9 : ℝ) * hausdorffMoment (egbFixedChargeAGibbsFullConeSource R A B) 1 -
      hausdorffMoment (egbFixedChargeAGibbsFullConeSource R A B) 2) := by
  simp only [egbFixedChargeAGibbsFullConeSource_moment]
  constructor
  · norm_num <;> ring
  · constructor <;> norm_num <;> ring

/-- Three consecutive initial moments distinguish all points of the full source cone. -/
theorem egbFixedChargeAGibbsFullConeSource_three_moments_iff (R A B T C D : NNReal) :
    (hausdorffMoment (egbFixedChargeAGibbsFullConeSource R A B) 0 =
        hausdorffMoment (egbFixedChargeAGibbsFullConeSource T C D) 0 ∧
      hausdorffMoment (egbFixedChargeAGibbsFullConeSource R A B) 1 =
        hausdorffMoment (egbFixedChargeAGibbsFullConeSource T C D) 1 ∧
      hausdorffMoment (egbFixedChargeAGibbsFullConeSource R A B) 2 =
        hausdorffMoment (egbFixedChargeAGibbsFullConeSource T C D) 2) ↔ R = T ∧ A = C ∧ B = D := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    have h := egbFixedChargeAGibbsFullConeSource_masses_from_moments R A B
    have g := egbFixedChargeAGibbsFullConeSource_masses_from_moments T C D
    rw [h0, h1, h2] at h
    exact ⟨Subtype.ext (h.1.trans g.1.symm), Subtype.ext (h.2.1.trans g.2.1.symm),
      Subtype.ext (h.2.2.trans g.2.2.symm)⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩

/-- Equality of full positive sources is exactly equality of all three atom masses. -/
theorem egbFixedChargeAGibbsFullConeSource_eq_iff (R A B T C D : NNReal) :
    egbFixedChargeAGibbsFullConeSource R A B = egbFixedChargeAGibbsFullConeSource T C D ↔
      R = T ∧ A = C ∧ B = D := by
  constructor
  · intro h
    apply (egbFixedChargeAGibbsFullConeSource_three_moments_iff R A B T C D).1
    exact ⟨congrArg (fun μ => hausdorffMoment μ 0) h,
      congrArg (fun μ => hausdorffMoment μ 1) h, congrArg (fun μ => hausdorffMoment μ 2) h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- The three-mass cone has no nontrivial source that is the zero measure. -/
theorem egbFixedChargeAGibbsFullConeSource_zero_iff (R A B : NNReal) :
    egbFixedChargeAGibbsFullConeSource R A B = 0 ↔ R = 0 ∧ A = 0 ∧ B = 0 := by
  have hz : egbFixedChargeAGibbsFullConeSource 0 0 0 = 0 := by
    simp [egbFixedChargeAGibbsFullConeSource, egbFixedChargeAGibbsConeSource, hausdorffAtomSource]
  rw [← hz, egbFixedChargeAGibbsFullConeSource_eq_iff]

/-- The entire positive-time history determines precisely the surviving pair and leaves the erased mass free. -/
theorem egbFixedChargeAGibbsFullConeSource_positive_history_iff (R A B T C D : NNReal) :
    (∀ m : ℕ, hausdorffMoment (egbFixedChargeAGibbsFullConeSource R A B) (m + 1) =
      hausdorffMoment (egbFixedChargeAGibbsFullConeSource T C D) (m + 1)) ↔ A = C ∧ B = D := by
  constructor
  · intro h
    have h1 := h 0
    have h2 := h 1
    norm_num [egbFixedChargeAGibbsFullConeSource_moment] at h1 h2
    have ha : (A : ℝ) = (C : ℝ) := by linarith
    have hb : (B : ℝ) = (D : ℝ) := by linarith
    exact ⟨Subtype.ext ha, Subtype.ext hb⟩
  · rintro ⟨rfl, rfl⟩ m
    simp [egbFixedChargeAGibbsFullConeSource_moment]

/-- Adding the initial moment is a complete and exact repair for positive-history information loss. -/
theorem egbFixedChargeAGibbsFullConeSource_initial_moment_repairs (R A B T C D : NNReal) :
    (hausdorffMoment (egbFixedChargeAGibbsFullConeSource R A B) 0 =
        hausdorffMoment (egbFixedChargeAGibbsFullConeSource T C D) 0 ∧
      ∀ m : ℕ, hausdorffMoment (egbFixedChargeAGibbsFullConeSource R A B) (m + 1) =
        hausdorffMoment (egbFixedChargeAGibbsFullConeSource T C D) (m + 1)) ↔
      egbFixedChargeAGibbsFullConeSource R A B = egbFixedChargeAGibbsFullConeSource T C D := by
  rw [egbFixedChargeAGibbsFullConeSource_positive_history_iff, egbFixedChargeAGibbsFullConeSource_eq_iff]
  constructor
  · rintro ⟨h0, rfl, rfl⟩
    norm_num [egbFixedChargeAGibbsFullConeSource_moment] at h0
    exact ⟨Subtype.ext (show (R : ℝ) = (T : ℝ) by linarith), rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩

end
end GaloisForLFunctions.HTGeometry
