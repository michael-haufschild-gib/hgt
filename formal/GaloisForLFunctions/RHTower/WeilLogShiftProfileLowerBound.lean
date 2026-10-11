import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalMassProfile

/-! Reverse local distortion prevents loss of normalization at quadratic starts. -/

open scoped BigOperators

namespace RHTower

theorem finiteWeilCanonicalMassProfile_ge_half_arithmetic (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) (i : Fin (r + 2)) :
    finiteWeilArithmeticAbsProfile r i / 2 ≤ finiteWeilCanonicalMassProfile r k i := by
  let c := finiteWeilArithmeticCenter r
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  have hn : 0 < n := by dsimp [n]; positivity
  have hb (j : Fin (r + 2)) : (0 : ℝ) ≤ ((j : ℕ) : ℝ) ∧ ((j : ℕ) : ℝ) ≤ n := by
    refine ⟨Nat.cast_nonneg _, ?_⟩
    dsimp [n]
    exact_mod_cast (show (j : ℕ) ≤ r + 1 by have := j.isLt; omega)
  have hd : |((c : ℕ) : ℝ) - ((i : ℕ) : ℝ)| ≤ n :=
    abs_le.mpr ⟨by linarith only [(hb c).1, (hb i).2], by linarith only [(hb c).2, (hb i).1]⟩
  have hm := finiteWeilCanonicalRawDistortion_index_modulus r k hwidth c i
  have hratio : finiteWeilCanonicalRawDistortion r k c / finiteWeilCanonicalRawDistortion r k i ≤ 2 := by
    have he : |finiteWeilCanonicalRawDistortion r k c / finiteWeilCanonicalRawDistortion r k i - 1| ≤ 1 := by
      exact hm.trans ((div_le_iff₀ hn).mpr (by simpa only [one_mul] using hd))
    have hu := (abs_le.mp he).2
    linarith only [hu]
  have ha := finiteWeilCanonicalRawDistortion_pos r k i
  have hc := finiteWeilCanonicalRawDistortion_pos r k c
  have hl : (1 : ℝ) / 2 ≤ finiteWeilCanonicalRawDistortion r k i / finiteWeilCanonicalRawDistortion r k c := by
    have hu := (div_le_iff₀ ha).mp hratio
    apply (le_div_iff₀ hc).mpr
    linarith only [hu]
  have hp := mul_le_mul_of_nonneg_left hl (finiteWeilArithmeticAbsProfile_pos r i).le
  simpa only [finiteWeilCanonicalMassProfile, mul_one_div] using hp

theorem finiteWeilCanonicalMassProfile_sum_ge_half (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    finiteWeilArithmeticMass r / 2 ≤ ∑ i, finiteWeilCanonicalMassProfile r k i := by
  calc
    _ = ∑ i, finiteWeilArithmeticAbsProfile r i / 2 := by
      rw [← Finset.sum_div, finiteWeilArithmeticAbsProfile_sum]
    _ ≤ _ := Finset.sum_le_sum fun i _ => finiteWeilCanonicalMassProfile_ge_half_arithmetic r k hwidth i

end RHTower
