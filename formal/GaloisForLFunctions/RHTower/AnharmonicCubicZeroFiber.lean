import GaloisForLFunctions.RHTower.AnharmonicChebyshevOrientationCasimir

namespace RHTower

/-- Lean's totalized division adds the two poles to the zero fiber of `q`. -/
theorem chebyshevAnharmonicQ_eq_zero_iff_totalized (s : ℂ) :
    chebyshevAnharmonicQ s = 0 ↔
      s = 0 ∨ s = 1 ∨ s = 2 ∨ s = -1 ∨ s = 1 / 2 := by
  unfold chebyshevAnharmonicQ
  rw [div_eq_zero_iff]
  constructor
  · rintro (hnum | hden)
    · rcases mul_eq_zero.mp hnum with hpair | hhalf
      · rcases mul_eq_zero.mp hpair with htwo | hminus
        · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp htwo)))
        · right; right; right; left
          linear_combination hminus
      · right; right; right; right
        linear_combination (1 / 2 : ℂ) * hhalf
    · rcases mul_eq_zero.mp hden with hleft | hone
      · rcases mul_eq_zero.mp hleft with htwo | hzero
        · norm_num at htwo
        · exact Or.inl hzero
      · exact Or.inr (Or.inl (sub_eq_zero.mp hone))
  · rintro (rfl | rfl | rfl | rfl | rfl) <;> norm_num

/-- The paper's three-point zero fiber, stated on the natural domain. -/
theorem chebyshevAnharmonicQ_eq_zero_iff_orbit (s : ℂ) :
    (s ≠ 0 ∧ s ≠ 1 ∧ chebyshevAnharmonicQ s = 0) ↔
      s = 2 ∨ s = -1 ∨ s = 1 / 2 := by
  rw [chebyshevAnharmonicQ_eq_zero_iff_totalized]
  constructor
  · rintro ⟨hs0, hs1, h⟩
    rcases h with h0 | h1 | h2 | hm1 | hhalf
    · exact (hs0 h0).elim
    · exact (hs1 h1).elim
    · exact Or.inl h2
    · exact Or.inr (Or.inl hm1)
    · exact Or.inr (Or.inr hhalf)
  · rintro (rfl | rfl | rfl) <;> norm_num

end RHTower
