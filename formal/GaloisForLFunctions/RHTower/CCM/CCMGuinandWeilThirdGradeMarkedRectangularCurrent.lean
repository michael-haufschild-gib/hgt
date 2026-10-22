import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilThirdGradeFixedRectangularMixture

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- Literal von Mangoldt-minus-polar current after assembling a positive marked family of
rectangular interval heads, but before taking any norm or absolute value. -/
def ccmThirdGradeCesaroMarkedRectangularPrimePolarCurrent (b H : ℝ) : ℝ :=
  ccmGuinandWeilPrimePolarWeightedWindow b H
    (ccmThirdGradeCesaroFixedRectangularMixture b H)

/-- The marked rectangular current is coefficient-faithful: it is exactly the literal
third-grade prime-minus-polar triangular window. -/
theorem ccmThirdGradeCesaroMarkedRectangularPrimePolarCurrent_eq_window
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ccmThirdGradeCesaroMarkedRectangularPrimePolarCurrent b H =
      ccmGuinandWeilPrimePolarWeightedWindow b H
        (ccmGuinandWeilThirdGradeCesaroTriangularWeight H) := by
  have hprime :
      (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          if b < Real.log k then
            criticalMellinAtomWeight k *
              ccmThirdGradeCesaroFixedRectangularMixture b H (Real.log k)
          else 0) =
        ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          if b < Real.log k then
            criticalMellinAtomWeight k *
              ccmGuinandWeilThirdGradeCesaroTriangularWeight H (Real.log k)
          else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hbk : b < Real.log k
    · have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkpos : (0 : ℝ) < k := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hk2)
      have hkexp : (k : ℝ) ≤ Real.exp H :=
        (Nat.le_floor_iff (Real.exp_pos H).le).mp (Finset.mem_Icc.mp hk).2
      have hkH : Real.log k ≤ H := (Real.log_le_iff_le_exp hkpos).mpr hkexp
      rw [if_pos hbk, if_pos hbk]
      rw [← ccmGuinandWeilThirdGradeCesaroTriangularWeight_eq_fixedRectangularMixture
        hb hbk.le hkH]
    · simp [hbk]
  have hpolar :
      (∫ h in b..H,
        ccmThirdGradeCesaroFixedRectangularMixture b H h *
          (2 * Real.cosh (h / 2))) =
      ∫ h in b..H,
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
          (2 * Real.cosh (h / 2)) := by
    apply intervalIntegral.integral_congr
    intro h hh
    rw [Set.uIcc_of_le hbH] at hh
    change ccmThirdGradeCesaroFixedRectangularMixture b H h *
        (2 * Real.cosh (h / 2)) =
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
        (2 * Real.cosh (h / 2))
    rw [← ccmGuinandWeilThirdGradeCesaroTriangularWeight_eq_fixedRectangularMixture
      hb hh.1 hh.2]
  unfold ccmThirdGradeCesaroMarkedRectangularPrimePolarCurrent
    ccmGuinandWeilPrimePolarWeightedWindow
  rw [hprime, hpolar]

/-- Exact RH-bearing landing: anchored signed moment is the pre-scalar marked rectangular current.
Positive and negative arithmetic regions remain coupled inside one scalar readout. -/
theorem ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_markedRectangularCurrent
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H =
      ccmThirdGradeCesaroMarkedRectangularPrimePolarCurrent b H := by
  rw [ccmThirdGradeCesaroMarkedRectangularPrimePolarCurrent_eq_window hb hbH]
  exact ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_primePolarTriangularWindow
    hb hbH

/-- After all reporter and carrier infrastructure is closed, the exact remaining datum is uniform
boundedness of the single signed marked rectangular current. -/
theorem uniformlyBounded_thirdGradeCesaroAnchoredErrorMoment_iff_markedRectangularCurrent
    {b : ℝ} (hb : 0 < b) :
    (∃ C : ℝ, ∀ H : ℝ, b ≤ H →
      |ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H| ≤ C) ↔
    (∃ C : ℝ, ∀ H : ℝ, b ≤ H →
      |ccmThirdGradeCesaroMarkedRectangularPrimePolarCurrent b H| ≤ C) := by
  constructor <;> rintro ⟨C, hC⟩ <;> refine ⟨C, ?_⟩ <;>
    intro H hbH
  · rw [← ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_markedRectangularCurrent hb hbH]
    exact hC H hbH
  · rw [ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_markedRectangularCurrent hb hbH]
    exact hC H hbH

end GaloisForLFunctions.RHTower
