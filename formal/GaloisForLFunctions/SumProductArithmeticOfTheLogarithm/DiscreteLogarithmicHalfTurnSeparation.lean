import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.EffectiveLogarithmicHalfTurn
import GaloisForLFunctions.RHTower.Sieve.PerronTruncationError

/-!
# Lower separation and an attained window for logarithmic half-turns

Odd powers of three remain a half-integer away from powers of four after
rescaling. Half-integer logarithmic separation gives
`|k * (log 3 / log 4) - ell - 1/2| >= 1 / ((3^k + 1) * log 4)`.

A return of precision `1/Q` must therefore start after an explicit logarithm
of `Q`. Combining this exclusion with the effective upper return theorem
gives lower and upper bounds for an attained discrete half-turn index.
-/

noncomputable section
namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

private theorem half_turn_log_identity (k m : ℕ) :
    Real.log (((3 : ℝ) ^ k / 2) / (4 : ℝ) ^ m) =
      ((k : ℝ) * threeFourRotation - m - 1 / 2) * Real.log 4 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by norm_num), Real.log_pow, Real.log_pow]
  have hpos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  rw [show Real.log 2 = Real.log 4 / 2 by linarith only [h4]]
  dsimp only [threeFourRotation]
  field_simp
  ring

/-- Odd powers of three stay a definite logarithmic distance from every half-turn. -/
theorem threeFourRotation_half_turn_gap {k : ℕ} (hk : 1 ≤ k) (ℓ : ℤ) :
    1 / (((3 : ℝ) ^ k + 1) * Real.log 4) ≤
      |(k : ℝ) * threeFourRotation - ℓ - 1 / 2| := by
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hpowNat : 3 ≤ (3 : ℕ) ^ k := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 3) hk
  have hpow : (3 : ℝ) ≤ (3 : ℝ) ^ k := by exact_mod_cast hpowNat
  by_cases hℓ : 0 ≤ ℓ
  · let N := (3 : ℕ) ^ k / 2
    have hmod : (3 : ℕ) ^ k % 2 = 1 := by norm_num [Nat.pow_mod]
    have hrep : (3 : ℕ) ^ k = 2 * N + 1 := by dsimp only [N]; omega
    have hN : 1 ≤ N := by omega
    have hrepR : (3 : ℝ) ^ k = 2 * (N : ℝ) + 1 := by exact_mod_cast hrep
    have hhalf : (N : ℝ) + 1 / 2 = (3 : ℝ) ^ k / 2 := by linarith only [hrepR]
    have hm : ((ℓ.toNat : ℕ) : ℝ) = (ℓ : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hℓ
    have h := RHTower.Sieve.inv_le_abs_log_div_half_integer hN
      (show 1 ≤ (4 : ℕ) ^ ℓ.toNat from pow_pos (by norm_num : (0 : ℕ) < 4) ℓ.toNat)
    rw [hhalf] at h
    simp only [Nat.cast_pow, Nat.cast_ofNat] at h
    rw [half_turn_log_identity, hm, abs_mul, abs_of_pos h4] at h
    have hden : 2 * ((N : ℝ) + 1) = (3 : ℝ) ^ k + 1 := by linarith only [hrepR]
    rw [hden] at h
    have hd := div_le_div_of_nonneg_right h h4.le
    calc
      _ = (1 / ((3 : ℝ) ^ k + 1)) / Real.log 4 := by rw [div_div]
      _ ≤ (|(k : ℝ) * threeFourRotation - ℓ - 1 / 2| * Real.log 4) / Real.log 4 := hd
      _ = _ := by field_simp
  · have hℓR : (ℓ : ℝ) ≤ -1 := by exact_mod_cast (show ℓ ≤ -1 by omega)
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hα := threeFourRotation_bounds.1
    have hka : 1 / 2 ≤ (k : ℝ) * threeFourRotation := by
      have h := mul_le_mul_of_nonneg_right hkR (by linarith only [hα] : 0 ≤ threeFourRotation)
      simp only [one_mul] at h
      linarith only [hα, h]
    have hraw : 1 / 2 ≤ (k : ℝ) * threeFourRotation - ℓ - 1 / 2 := by
      linarith only [hka, hℓR]
    have hphase : 1 / 2 ≤ |(k : ℝ) * threeFourRotation - ℓ - 1 / 2| :=
      hraw.trans (le_abs_self _)
    have hlog := _root_.HTGeometry.one_sub_inv_le_log (by norm_num : (0 : ℝ) < 4)
    norm_num at hlog
    apply le_trans ?_ hphase
    apply (div_le_iff₀ (by positivity : 0 < ((3 : ℝ) ^ k + 1) * Real.log 4)).mpr
    have h := mul_le_mul_of_nonneg_right hpow h4.le
    nlinarith only [h, hlog]

/-- Precision forces the return index beyond an explicit exponential separation threshold. -/
theorem threeFourRotation_half_turn_precision {k : ℕ} (hk : 1 ≤ k)
    {Q : ℝ} (hQ : 0 < Q) {ℓ : ℤ}
    (hclose : |(k : ℝ) * threeFourRotation - ℓ - 1 / 2| < 1 / Q) :
    Q < ((3 : ℝ) ^ k + 1) * Real.log 4 := by
  have h := (threeFourRotation_half_turn_gap hk ℓ).trans_lt hclose
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hd : 0 < ((3 : ℝ) ^ k + 1) * Real.log 4 := by positivity
  have hh := (div_lt_div_iff₀ hd hQ).mp h
  simpa only [one_mul] using hh

/-- Any return of precision `1/Q` has index larger than an explicit logarithm of `Q`. -/
theorem threeFourRotation_half_turn_index_lower {k : ℕ} (hk : 1 ≤ k)
    {Q : ℝ} (hQ : 0 < Q) {ℓ : ℤ}
    (hclose : |(k : ℝ) * threeFourRotation - ℓ - 1 / 2| < 1 / Q) :
    (Real.log Q - Real.log (2 * Real.log 4)) / Real.log 3 < (k : ℝ) := by
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hp : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have h := threeFourRotation_half_turn_precision hk hQ hclose
  have hb : Q < (2 * Real.log 4) * (3 : ℝ) ^ k := by
    have hm := mul_le_mul_of_nonneg_right hp h4.le
    nlinarith only [h, hm]
  have hl := Real.log_lt_log hQ hb
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hl
  apply (div_lt_iff₀ h3).mpr
  linarith only [hl]

/-- Explicit lower and upper index bounds for an attained discrete half-turn return. -/
theorem exists_three_four_half_turn_window {Q : ℕ} (hQ : 2 ≤ Q) :
    ∃ k : ℕ, 1 ≤ k ∧
      (Real.log (Q : ℝ) - Real.log (2 * Real.log 4)) / Real.log 3 < (k : ℝ) ∧
      (k : ℝ) ≤ (Q : ℝ) * (4 : ℝ) ^ Q * Real.log 4 / 2 ∧
      ∃ ℓ : ℤ, |(k : ℝ) * threeFourRotation - ℓ - 1 / 2| < 1 / (Q : ℝ) := by
  obtain ⟨k, hk, hbound, ℓ, hclose⟩ := exists_effective_three_four_half_turn hQ
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  exact ⟨k, hk, threeFourRotation_half_turn_index_lower hk hQ0 hclose, hbound, ℓ, hclose⟩

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
