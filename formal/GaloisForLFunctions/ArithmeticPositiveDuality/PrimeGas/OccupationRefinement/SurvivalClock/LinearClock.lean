import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-! # Nonnegative additive attenuation is linear on nonnegative real time -/

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SurvivalClock

open scoped NNReal

/-- Integer time bounds the attenuation at real time with an error independent
of the number of repeated observations. -/
theorem linear_attenuation (A : ℝ≥0 →+ ℝ) (positive : ∀ t, 0≤A t) (t : ℝ≥0) :
    A t=(t:ℝ)*A 1 := by
  have mono : Monotone A := by
    intro a b hab
    obtain ⟨r,rfl⟩ := exists_add_of_le hab
    simpa only [map_add] using le_add_of_nonneg_right (a:=A a) (positive r)
  have natural (n : ℕ) : A (n:ℝ≥0)=(n:ℝ)*A 1 := by
    simpa only [nsmul_eq_mul,mul_one] using map_nsmul A n (1:ℝ≥0)
  have scale (n : ℕ) : A ((n:ℝ≥0)*t)=(n:ℝ)*A t := by
    simpa only [nsmul_eq_mul] using map_nsmul A n t
  have gap (n : ℕ) : |(n:ℝ)*(A t-(t:ℝ)*A 1)|≤A 1 := by
    let k : ℕ := ⌊(n:ℝ≥0)*t⌋₊
    have low : (k:ℝ≥0)≤(n:ℝ≥0)*t := Nat.floor_le zero_le
    have high : (n:ℝ≥0)*t≤(k:ℝ≥0)+1 := (Nat.lt_floor_add_one _).le
    have al := mono low
    have ah := mono high
    rw [natural,scale] at al
    rw [map_add,natural,scale] at ah
    have l : (k:ℝ)≤(n:ℝ)*(t:ℝ) := by exact_mod_cast low
    have u : (n:ℝ)*(t:ℝ)≤(k:ℝ)+1 := by exact_mod_cast high
    have ml := mul_le_mul_of_nonneg_right l (positive 1)
    have mu := mul_le_mul_of_nonneg_right u (positive 1)
    rw [abs_le]
    constructor <;> linarith only [al,ah,ml,mu]
  by_contra ne
  have d := abs_pos.mpr (sub_ne_zero.mpr ne)
  obtain ⟨n,hn⟩ := exists_nat_gt (A 1 / |A t-(t:ℝ)*A 1|)
  have g := gap n
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)] at g
  exact (not_lt_of_ge g) ((div_lt_iff₀ d).mp hn)

#print axioms linear_attenuation

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SurvivalClock
