import GaloisForLFunctions.RHTower.WeilLogShiftProfileLowerBound
import GaloisForLFunctions.RHTower.WeilLogShiftMidpointProfile

/-! Uniform binomial domination of the actual midpoint probability at quadratic starts. -/

open scoped BigOperators

namespace RHTower

theorem finiteWeilCanonicalMixture_midpoint_binomial_domination
    (r t : ℕ) (i : Fin (r + 2)) :
    finiteWeilCanonicalMixture r (2 * (r + 1) ^ 2 + t) (1 / 2) i ≤
      4 * (((r + 1).choose (i : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1)) := by
  let k := 2 * (r + 1) ^ 2 + t
  have hw : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ) := by
    dsimp [k]
    push_cast
    nlinarith only [Nat.cast_nonneg (α := ℝ) t]
  have hn : (0 : ℝ) < (r + 1 : ℕ) := by positivity
  have hpos := (finiteWeilArithmeticAbsProfile_pos r i).le
  have hb (j : Fin (r + 2)) : (0 : ℝ) ≤ (j : ℕ) ∧ ((j : ℕ) : ℝ) ≤ (r + 1 : ℕ) := by
    refine ⟨Nat.cast_nonneg _, ?_⟩
    exact_mod_cast (show (j : ℕ) ≤ r + 1 by omega)
  have hd : |((i : ℕ) : ℝ) - ((finiteWeilArithmeticCenter r : Fin (r + 2)) : ℕ)| ≤
      (r + 1 : ℕ) := by
    apply abs_le.mpr
    constructor <;> linarith [(hb i).1, (hb i).2,
      (hb (finiteWeilArithmeticCenter r)).1, (hb (finiteWeilArithmeticCenter r)).2]
  have herr := finiteWeilCanonicalMassProfile_error r k hw i
  have herror : |finiteWeilCanonicalMassProfile r k i - finiteWeilArithmeticAbsProfile r i| ≤
      finiteWeilArithmeticAbsProfile r i := by
    apply herr.trans
    apply (div_le_iff₀ hn).mpr
    exact mul_le_mul_of_nonneg_left hd hpos
  have hupper : finiteWeilCanonicalMassProfile r k i ≤ 2 * finiteWeilArithmeticAbsProfile r i := by
    linarith [(abs_le.mp herror).2]
  have hmass := finiteWeilCanonicalMassProfile_sum_ge_half r k hw
  have hG : 0 < finiteWeilArithmeticMass r :=
    lt_of_lt_of_le (by norm_num) (finiteWeilArithmeticMass_ge_two r)
  have hF : 0 < ∑ j, finiteWeilCanonicalMassProfile r k j := by linarith
  rw [finiteWeilCanonicalMixture_midpoint_profile, ← finiteWeilArithmeticAbsProfile_normalized]
  change finiteWeilCanonicalMassProfile r k i / (∑ j, finiteWeilCanonicalMassProfile r k j) ≤ _
  calc
    _ ≤ (2 * finiteWeilArithmeticAbsProfile r i) / (finiteWeilArithmeticMass r / 2) := by
      gcongr
    _ = 4 * (finiteWeilArithmeticAbsProfile r i / finiteWeilArithmeticMass r) := by ring

end RHTower
