import GaloisForLFunctions.RHTower.ChenGuptaLiWeightedCharacterGram

noncomputable section

namespace RHTower

/-- Every weighted CGL finite large-value set is empty, or has an internally constructed
nonempty packet whose rows are all large and obey the centered weighted-Gram bound. -/
theorem cglCharacterDyadicWeightedLargeValues_empty_or_exists_centeredGramPacket
    (N q R : ℕ) (weight : Fin N → ℂ) (w : Fin R → CGLCharacterDyadicRowData q)
    (a : CGLCharacterDyadicBoundedCoefficients N) (V : NNReal) :
    cglCharacterDyadicWeightedLargeValues N q R weight w a.value V = ∅ ∨
      ∃ (K : ℕ) (selected : Fin (K + 1) → CGLCharacterDyadicRowData q),
        (∀ i, (V : ℝ) ≤ ‖cglCharacterDyadicWeightedPolynomial N q weight (selected i) a.value‖) ∧
          ((cglCharacterDyadicWeightedLargeValues N q R weight w a.value V).card : ℝ) *
              (V : ℝ) ^ 2 ≤
            (N : ℝ) *
              (2 * (((cglCharacterDyadicWeightedGram N q (K + 1) weight selected) ^ 3).trace.re -
                ((cglCharacterDyadicWeightedGram N q (K + 1) weight selected).trace.re ^ 3) /
                  (K + 1 : ℝ) ^ 2) ^ (1 / 6 : ℝ) +
                2 * √((cglCharacterDyadicWeightedGram N q (K + 1) weight selected).trace.re /
                  (K + 1 : ℝ))) ^ 2 := by
  classical
  let S := cglCharacterDyadicWeightedLargeValues N q R weight w a.value V
  by_cases hS : S.Nonempty
  · right
    obtain ⟨K, hK⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Finset.card_pos.mpr hS))
    let e : Fin (K + 1) ≃ {r : Fin R // r ∈ S} :=
      Fintype.equivOfCardEq (by
        simp only [Fintype.card_fin, Fintype.card_coe]
        omega)
    let selected : Fin (K + 1) → CGLCharacterDyadicRowData q := fun i => w (e i).val
    have hselected : ∀ i : Fin (K + 1),
        (V : ℝ) ≤ ‖cglCharacterDyadicWeightedPolynomial N q weight (selected i) a.value‖ := by
      intro i
      have hiS : (e i).val ∈ cglCharacterDyadicWeightedLargeValues N q R weight w a.value V := by
        change (e i).val ∈ S
        exact (e i).property
      exact (Finset.mem_filter.mp hiS).2
    refine ⟨K, selected, hselected, ?_⟩
    have hall : cglCharacterDyadicWeightedLargeValues N q (K + 1) weight selected a.value V =
        Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro i
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hselected i⟩
    have hbound := card_cglCharacterDyadicWeightedLargeValues_mul_sq_le_centeredGramTrace
      N q K weight selected a V
    rw [hall] at hbound
    simp only [Finset.card_univ, Fintype.card_fin] at hbound
    change (S.card : ℝ) * (V : ℝ) ^ 2 ≤ _
    simpa [hK, Nat.succ_eq_add_one] using hbound
  · left
    exact Finset.not_nonempty_iff_eq_empty.mp hS

end RHTower
