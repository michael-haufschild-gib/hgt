import GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusQuotientTail

/-!
# Power cutoffs for the signed quotient head

The one-ninth, one-third, and one-quarter cutoffs retain the respective arithmetic
heads for the routes from seven eighths to five sixths or three quarters. All bounds
below use the actual zero abscissa; no numerical zero-free strip is assumed.
-/

noncomputable section

namespace RHTower

/-- Moving a quotient cutoff to `ceil(M^θ)` pays the tail at its exact exponent. -/
theorem mobiusDivisorQuotientPowerHead_error_subpower
    (θ : ℝ) (hθ : 0 ≤ θ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 1 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M -
          mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊| ≤
        C * (M : ℝ) ^
          (zetaZeroAbscissa + 1 / 2 - θ * (zetaZeroAbscissa - 1 / 2) + ε) := by
  obtain ⟨C, hC, hbound⟩ := mobiusDivisorQuotientHead_error_subpower ε hε
  refine ⟨C, hC, fun M hM => ?_⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hp : 0 < (M : ℝ) ^ θ := Real.rpow_pos_of_pos hM0 θ
  have hceil : (M : ℝ) ^ θ ≤ (⌈(M : ℝ) ^ θ⌉₊ : ℝ) := Nat.le_ceil _
  have hQ : 1 ≤ ⌈(M : ℝ) ^ θ⌉₊ := by
    have hpos : (0 : ℝ) < (⌈(M : ℝ) ^ θ⌉₊ : ℝ) := hp.trans_le hceil
    have hn : 0 < ⌈(M : ℝ) ^ θ⌉₊ := by exact_mod_cast hpos
    omega
  have he : 1 / 2 - zetaZeroAbscissa - ε ≤ 0 := by
    linarith [half_le_zetaZeroAbscissa]
  calc
    _ ≤ C * (M : ℝ) ^ (zetaZeroAbscissa + ε + 1 / 2) *
        (⌈(M : ℝ) ^ θ⌉₊ : ℝ) ^ (1 / 2 - zetaZeroAbscissa - ε) :=
      hbound M _ hQ
    _ ≤ C * (M : ℝ) ^ (zetaZeroAbscissa + ε + 1 / 2) *
        ((M : ℝ) ^ θ) ^ (1 / 2 - zetaZeroAbscissa - ε) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hp hceil he) (by positivity)
    _ = C * (M : ℝ) ^
        (zetaZeroAbscissa + ε + 1 / 2 + θ * (1 / 2 - zetaZeroAbscissa - ε)) := by
      rw [← Real.rpow_mul hM0.le, mul_assoc, ← Real.rpow_add hM0]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hM1
      (by nlinarith)) hC

/-- The one-ninth head has tail exponent `(8Θ + 5)/9`, where Θ is the actual abscissa. -/
theorem mobiusDivisorQuotientNinthHead_error_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 1 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M -
          mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ (1 / 9 : ℝ)⌉₊| ≤
        C * (M : ℝ) ^ ((8 / 9 : ℝ) * zetaZeroAbscissa + 5 / 9 + ε) := by
  have he : zetaZeroAbscissa + 1 / 2 - (1 / 9 : ℝ) *
      (zetaZeroAbscissa - 1 / 2) + ε =
      (8 / 9 : ℝ) * zetaZeroAbscissa + 5 / 9 + ε := by ring
  simpa only [he] using
    mobiusDivisorQuotientPowerHead_error_subpower (1 / 9) (by norm_num) ε hε

/-- The one-third head has tail exponent `2(Θ + 1)/3`. -/
theorem mobiusDivisorQuotientThirdHead_error_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 1 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M -
          mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ (1 / 3 : ℝ)⌉₊| ≤
        C * (M : ℝ) ^ ((2 / 3 : ℝ) * zetaZeroAbscissa + 2 / 3 + ε) := by
  have he : zetaZeroAbscissa + 1 / 2 - (1 / 3 : ℝ) *
      (zetaZeroAbscissa - 1 / 2) + ε =
      (2 / 3 : ℝ) * zetaZeroAbscissa + 2 / 3 + ε := by ring
  simpa only [he] using
    mobiusDivisorQuotientPowerHead_error_subpower (1 / 3) (by norm_num) ε hε

/-- The one-quarter head has tail exponent `3Θ/4 + 5/8`. -/
theorem mobiusDivisorQuotientQuarterHead_error_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 1 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M -
          mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ (1 / 4 : ℝ)⌉₊| ≤
        C * (M : ℝ) ^ ((3 / 4 : ℝ) * zetaZeroAbscissa + 5 / 8 + ε) := by
  have he : zetaZeroAbscissa + 1 / 2 - (1 / 4 : ℝ) *
      (zetaZeroAbscissa - 1 / 2) + ε =
      (3 / 4 : ℝ) * zetaZeroAbscissa + 5 / 8 + ε := by ring
  simpa only [he] using
    mobiusDivisorQuotientPowerHead_error_subpower (1 / 4) (by norm_num) ε hε

end RHTower
