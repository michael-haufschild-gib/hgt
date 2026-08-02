import GaloisForLFunctions.RHTower.DeningerKotheSpace
import GaloisForLFunctions.RHTower.DeningerFourierBridge

/-!
# The Köthe space of rapidly decreasing Fourier coefficients

Weighting the coefficients indexed by the integers by `(1 + |n|)^k` gives a Köthe datum, and each
weight is summable against the weight two steps later, because `∑ (1+|n|)^{-2}` converges over the
integers.  So that Köthe space is nuclear.

It is the coefficient model of a smooth periodic test space: the decay estimates say the
coefficients of a smooth function lie in it, and the summation theorem says the function is
recovered from them.

* `deningerFourierWeights` : the weights `(1 + |n|)^k` on the integers.
* `deningerFourierWeights_isNuclear` : each weight is summable against a later one.
* `deningerFourierKothe_isNuclearSpace` : **the coefficient model is nuclear.**
-/

namespace RHTower

section FourierKothe

/-- The Köthe datum of the weights `(1 + |n|)^k` on the integers. -/
noncomputable def deningerFourierWeights : DeningerKotheData ℤ where
  w k n := (1 + |(n : ℝ)|) ^ k
  pos k n := by positivity
  mono k n := by
    have h1 : (1 : ℝ) ≤ 1 + |(n : ℝ)| := by linarith [abs_nonneg ((n : ℝ))]
    calc (1 + |(n : ℝ)|) ^ k = (1 + |(n : ℝ)|) ^ k * 1 := by ring
      _ ≤ (1 + |(n : ℝ)|) ^ k * (1 + |(n : ℝ)|) := by
          refine mul_le_mul_of_nonneg_left h1 ?_
          positivity
      _ = (1 + |(n : ℝ)|) ^ (k + 1) := by ring

theorem deningerFourierWeights_w (k : ℕ) (n : ℤ) :
    deningerFourierWeights.w k n = (1 + |(n : ℝ)|) ^ k := rfl

theorem deningerFourier_summable_inv_sq :
    Summable fun n : ℤ => (1 + |(n : ℝ)|) ^ (-(2 : ℤ)) := by
  have hnat : Summable fun n : ℕ => (1 + (n : ℝ)) ^ (-(2 : ℤ)) := by
    have h1 : Summable fun n : ℕ => 1 / ((n : ℝ)) ^ 2 :=
      Real.summable_one_div_nat_pow.mpr one_lt_two
    have h2 : Summable fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) ^ 2 := (summable_nat_add_iff 1).mpr h1
    refine h2.congr fun n => ?_
    push_cast
    rw [zpow_neg, zpow_two, ← one_div]
    ring_nf
  refine Summable.of_nat_of_neg ?_ ?_
  · refine hnat.congr fun n => ?_
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)]
  · refine hnat.congr fun n => ?_
    rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]

/-- **Each weight is summable against the weight two steps later.** -/
theorem deningerFourierWeights_isNuclear : deningerFourierWeights.IsNuclear := by
  intro k
  refine ⟨k + 2, by omega, ?_⟩
  refine deningerFourier_summable_inv_sq.congr fun n => ?_
  rw [deningerFourierWeights_w, deningerFourierWeights_w]
  have hpos : (0 : ℝ) < 1 + |(n : ℝ)| := by positivity
  rw [zpow_neg, zpow_two, pow_add]
  field_simp

/-- **The coefficient model is nuclear.** -/
theorem deningerFourierKothe_isNuclearSpace :
    DeningerIsNuclearSpace (deningerKotheSeminorm (𝕜 := ℂ) deningerFourierWeights) :=
  deningerKothe_isNuclearSpace deningerFourierWeights deningerFourierWeights_isNuclear

end FourierKothe

end RHTower
