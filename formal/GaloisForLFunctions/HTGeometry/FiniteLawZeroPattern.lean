import GaloisForLFunctions.HTGeometry.FiniteLawBoundaryLogProfile

/-! # Exact image of the zero-weight indicator of a finite probability law -/

namespace GaloisForLFunctions.HTGeometry.FourierLLogL.Law

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem zeroMassIndicator_eq_zero_or_one (Q : Law α) (i : α) :
    Q.zeroMassIndicator i = 0 ∨ Q.zeroMassIndicator i = 1 := by
  classical
  by_cases hi : Q i = 0 <;> simp only [zeroMassIndicator, hi, if_true, if_false, or_true, true_or]

theorem exists_zeroMassIndicator_eq_zero (Q : Law α) :
    ∃ i, Q.zeroMassIndicator i = 0 := by
  obtain ⟨i, hi⟩ := Q.mem_nonempty
  exact ⟨i, by simp only [zeroMassIndicator, hi.ne', if_false]⟩

theorem exists_law_zeroMassIndicator_iff (v : α → ℝ) :
    (∃ Q : Law α, Q.zeroMassIndicator = v) ↔
      (∀ i, v i = 0 ∨ v i = 1) ∧ ∃ i, v i = 0 := by
  classical
  constructor
  · rintro ⟨Q, rfl⟩
    exact ⟨Q.zeroMassIndicator_eq_zero_or_one, Q.exists_zeroMassIndicator_eq_zero⟩
  · rintro ⟨hvalues, i₀, hi₀⟩
    have hw (i : α) : 0 ≤ 1 - v i := by
      rcases hvalues i with hi | hi <;> simp only [hi, sub_zero, sub_self, zero_le_one, le_refl]
    have htotal : 0 < ∑ i, (1 - v i) := by
      have hi : 0 < 1 - v i₀ := by rw [hi₀, sub_zero]; exact zero_lt_one
      exact hi.trans_le (Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i₀))
    let Q : Law α := proportional (fun i => 1 - v i) hw htotal
    have hQ (i : α) : Q i = (1 - v i) / ∑ j, (1 - v j) := rfl
    refine ⟨Q, ?_⟩
    funext i
    rcases hvalues i with hi | hi
    · have hpos : 0 < Q i := by
        rw [hQ, hi, sub_zero]
        exact div_pos zero_lt_one htotal
      simp only [zeroMassIndicator, hpos.ne', if_false, hi]
    · have hzero : Q i = 0 := by rw [hQ, hi, sub_self, zero_div]
      simp only [zeroMassIndicator, hzero, if_pos, hi]

end GaloisForLFunctions.HTGeometry.FourierLLogL.Law
