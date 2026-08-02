import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Powers on the unit circle

Two estimates used to turn approximate phase relations into exact ones.

Raising to an integer power multiplies distances on the unit circle by at most the exponent, so an
approximate phase identity survives finitely many multiplications; and a phase that is not a multiple
of `2π` has some multiple whose cosine is at most `1/2`, so the corresponding point of the circle is
at distance at least one from `1`.  The second is what makes a nontrivial phase detectable with a
*universal* tolerance, independent of how small the phase is.
-/

open Real

namespace GaloisForLFunctions

/-- On the unit circle, the `n`-th power is `n`-Lipschitz. -/
theorem norm_pow_sub_pow_le_of_norm_one {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (n : ℕ) :
    ‖z ^ n - w ^ n‖ ≤ (n : ℝ) * ‖z - w‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hsplit : z ^ (n + 1) - w ^ (n + 1) = z ^ n * (z - w) + w * (z ^ n - w ^ n) := by
        ring
      have hz' : ‖z ^ n‖ = 1 := by
        rw [norm_pow, hz, one_pow]
      calc ‖z ^ (n + 1) - w ^ (n + 1)‖
          ≤ ‖z ^ n * (z - w)‖ + ‖w * (z ^ n - w ^ n)‖ := by
            rw [hsplit]; exact norm_add_le _ _
        _ = ‖z - w‖ + ‖z ^ n - w ^ n‖ := by
            rw [norm_mul, norm_mul, hz', hw, one_mul, one_mul]
        _ ≤ ‖z - w‖ + (n : ℝ) * ‖z - w‖ := by linarith [ih]
        _ = ((n : ℝ) + 1) * ‖z - w‖ := by ring
        _ = ((n + 1 : ℕ) : ℝ) * ‖z - w‖ := by push_cast; ring

/-- On the unit circle, the `c`-th power is `|c|`-Lipschitz for every integer `c`. -/
theorem norm_zpow_sub_zpow_le_of_norm_one {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (c : ℤ) :
    ‖z ^ c - w ^ c‖ ≤ (c.natAbs : ℝ) * ‖z - w‖ := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact zero_ne_one hz
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    exact zero_ne_one hw
  rcases c with n | n
  · have h := norm_pow_sub_pow_le_of_norm_one hz hw n
    simpa using h
  ·
    have hpow := norm_pow_sub_pow_le_of_norm_one hz hw (n + 1)
    have hzn : ‖z ^ (n + 1)‖ = 1 := by rw [norm_pow, hz, one_pow]
    have hwn : ‖w ^ (n + 1)‖ = 1 := by rw [norm_pow, hw, one_pow]
    have hzn0 : z ^ (n + 1) ≠ 0 := pow_ne_zero _ hz0
    have hwn0 : w ^ (n + 1) ≠ 0 := pow_ne_zero _ hw0
    have hinv : (z ^ (n + 1))⁻¹ - (w ^ (n + 1))⁻¹
          = (w ^ (n + 1) - z ^ (n + 1)) / (z ^ (n + 1) * w ^ (n + 1)) := by
        field_simp
    have hval : ‖(z ^ (n + 1))⁻¹ - (w ^ (n + 1))⁻¹‖ = ‖z ^ (n + 1) - w ^ (n + 1)‖ := by
        rw [hinv, norm_div, norm_mul, hzn, hwn, one_mul, div_one, norm_sub_rev]
    have hzpow : z ^ (Int.negSucc n) = (z ^ (n + 1))⁻¹ := by
        rw [zpow_negSucc]
    have hwpow : w ^ (Int.negSucc n) = (w ^ (n + 1))⁻¹ := by
        rw [zpow_negSucc]
    rw [hzpow, hwpow, hval]
    simpa using hpow

/-- **A phase that is not a multiple of `2π` has a multiple with cosine at most `1/2`.** -/
theorem exists_nat_cos_le_half {φ : ℝ} (hφ : ∀ n : ℤ, φ ≠ 2 * Real.pi * n) :
    ∃ m : ℕ, 0 < m ∧ Real.cos (m * φ) ≤ 1 / 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set k : ℤ := round (φ / (2 * Real.pi)) with hk
  set ψ : ℝ := φ - 2 * Real.pi * k with hψ
  have hψne : ψ ≠ 0 := by
    intro h
    exact hφ k (by linarith [h, hψ])
  have hψle : |ψ| ≤ Real.pi := by
    have habs : |φ / (2 * Real.pi) - (k : ℝ)| ≤ 1 / 2 := by
      rw [hk]
      exact abs_sub_round _
    have hpos : (0 : ℝ) < 2 * Real.pi := by linarith
    have h2 : (2 * Real.pi) ≠ 0 := by positivity
    have hrw : ψ = (2 * Real.pi) * (φ / (2 * Real.pi) - (k : ℝ)) := by
      rw [hψ]
      field_simp
    rw [hrw, abs_mul, abs_of_pos hpos]
    calc (2 * Real.pi) * |φ / (2 * Real.pi) - (k : ℝ)| ≤ (2 * Real.pi) * (1 / 2) :=
          mul_le_mul_of_nonneg_left habs (le_of_lt hpos)
      _ = Real.pi := by ring
  set θ : ℝ := |ψ| with hθ
  have hθpos : 0 < θ := abs_pos.mpr hψne
  -- the multiple
  set m : ℕ := ⌈Real.pi / (3 * θ)⌉₊ with hm
  have hmpos : 0 < m := by
    refine Nat.ceil_pos.mpr ?_
    positivity
  have hlow : Real.pi / 3 ≤ (m : ℝ) * θ := by
    have hceil : Real.pi / (3 * θ) ≤ (m : ℝ) := Nat.le_ceil _
    have := mul_le_mul_of_nonneg_right hceil (le_of_lt hθpos)
    calc Real.pi / 3 = Real.pi / (3 * θ) * θ := by field_simp
      _ ≤ (m : ℝ) * θ := this
  have hhigh : (m : ℝ) * θ ≤ 4 * Real.pi / 3 := by
    have hceil : (m : ℝ) < Real.pi / (3 * θ) + 1 := by
      refine Nat.ceil_lt_add_one ?_
      positivity
    have hmul : (m : ℝ) * θ < (Real.pi / (3 * θ) + 1) * θ :=
      mul_lt_mul_of_pos_right hceil hθpos
    have hval : (Real.pi / (3 * θ) + 1) * θ = Real.pi / 3 + θ := by
      field_simp
    have hθπ : θ ≤ Real.pi := hψle
    rw [hval] at hmul
    linarith
  -- the cosine bound
  have hcosθ : Real.cos ((m : ℝ) * θ) ≤ 1 / 2 := by
    rcases le_or_gt ((m : ℝ) * θ) (Real.pi / 2) with hle | hgt
    · have h1 : Real.cos ((m : ℝ) * θ) ≤ Real.cos (Real.pi / 3) := by
        refine Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) ?_ hlow
        linarith
      rw [Real.cos_pi_div_three] at h1
      exact h1
    · have h2 : Real.cos ((m : ℝ) * θ) ≤ 0 := by
        refine Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_lt hgt) ?_
        linarith
      linarith
  refine ⟨m, hmpos, ?_⟩
  -- transport the bound back to `φ`
  have hcast : Real.cos ((m : ℝ) * φ) = Real.cos ((m : ℝ) * θ) := by
    have hφψ : φ = ψ + 2 * Real.pi * k := by rw [hψ]; ring
    have hstep : Real.cos ((m : ℝ) * φ) = Real.cos ((m : ℝ) * ψ) := by
      rw [hφψ]
      have hexp : (m : ℝ) * (ψ + 2 * Real.pi * k) = (m : ℝ) * ψ + (m * k : ℤ) * (2 * Real.pi) := by
        push_cast
        ring
      rw [hexp, Real.cos_add_int_mul_two_pi]
    rcases abs_cases ψ with ⟨habs, _⟩ | ⟨habs, _⟩
    · rw [hstep, hθ, habs]
    · rw [hstep, hθ, habs]
      have : (m : ℝ) * -ψ = -((m : ℝ) * ψ) := by ring
      rw [this, Real.cos_neg]
  rw [hcast]
  exact hcosθ

end GaloisForLFunctions
