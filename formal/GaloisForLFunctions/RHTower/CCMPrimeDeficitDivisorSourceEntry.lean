import GaloisForLFunctions.RHTower.CCMPrimeDeficitDivisorSource

/-!
# The actual divisor source before its second entry

The doubled source vanishes at nonpositive time. Before `log 2` its only
contributing index is one, so its value is exactly `exp t - 1`.
-/

noncomputable section

namespace RHTower

theorem ccmPrimeDeficitDivisorSource_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    ccmPrimeDeficitDivisorSource t = 0 := by
  rcases lt_or_eq_of_le ht with ht | rfl
  · have hf : ⌊Real.exp t⌋₊ = 0 := Nat.floor_eq_zero.mpr (Real.exp_lt_one_iff.mpr ht)
    simp [ccmPrimeDeficitDivisorSource, hf]
  · simp [ccmPrimeDeficitDivisorSource]

theorem ccmPrimeDeficitDivisorSource_before_two {t : ℝ}
    (ht : 0 ≤ t) (htop : t < Real.log 2) :
    ccmPrimeDeficitDivisorSource t = Real.exp t - 1 := by
  have hf : ⌊Real.exp t⌋₊ = 1 := by
    apply (Nat.floor_eq_iff (Real.exp_pos t).le).mpr
    constructor
    · simpa only [Nat.cast_one] using Real.one_le_exp_iff.mpr ht
    · simpa only [Nat.cast_one, Nat.cast_add, one_add_one_eq_two] using
        (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)).mp htop
  simp [ccmPrimeDeficitDivisorSource, hf]

end RHTower
