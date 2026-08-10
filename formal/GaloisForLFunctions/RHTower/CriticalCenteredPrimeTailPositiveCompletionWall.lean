import GaloisForLFunctions.RHTower.CriticalCenteredPrimeTailPassivityNoGo

/-!
# Centered prime-tail positive-completion wall

The exact `Λ-1` pole cancellation from the centered Route T current cannot be repaired into a
finite-mass positive atomic source at the critical boundary.  Every integer `6(m+1)` has two
distinct prime divisors, hence is not a prime power and carries centered boundary mass exactly
`-1/(6(m+1))`.  Any coordinatewise correction making all atoms nonnegative must refund this full
harmonic subsequence.  Its total variation therefore diverges.

This closes a structural dichotomy.  Positive Hilbert completion restores the same boundary mass
whose subtraction cancelled the zeta pole; finite-mass pole cancellation must instead retain a
genuinely signed/indefinite channel.
-/

open Complex Filter Topology LSeries ArithmeticFunction

namespace RHTower

noncomputable section

private theorem not_isPrimePow_six_mul_succ (m : ℕ) :
    ¬ IsPrimePow (6 * (m + 1)) := by
  have hn2 : 2 ≤ 6 * (m + 1) := by omega
  rw [Nat.not_isPrimePow_iff_nontrivial_of_two_le hn2]
  refine ⟨2, Nat.mem_primeFactors.mpr ⟨Nat.prime_two, ?_, by omega⟩,
    3, Nat.mem_primeFactors.mpr ⟨Nat.prime_three, ?_, by omega⟩, by norm_num⟩
  · exact dvd_mul_of_dvd_left (by norm_num : 2 ∣ 6) _
  · exact dvd_mul_of_dvd_left (by norm_num : 3 ∣ 6) _

private theorem vonMangoldt_six_mul_succ (m : ℕ) :
    ArithmeticFunction.vonMangoldt (6 * (m + 1)) = 0 :=
  ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (not_isPrimePow_six_mul_succ m)

/-- Every multiple-of-six atom of the critical centered source is exactly negative harmonic mass. -/
theorem centeredPrimeTailCurrentFourierWeight_one_six_mul_succ (m : ℕ) :
    centeredPrimeTailCurrentFourierWeight 1 (6 * (m + 1)) =
      -1 / ((6 * (m + 1) : ℕ) : ℝ) := by
  rw [centeredPrimeTailCurrentFourierWeight, centeredPrimeTailCurrentRealCoeff,
    vonMangoldt_six_mul_succ, if_pos (by omega), Real.rpow_neg_one]
  simp only [zero_sub, neg_mul, one_mul, neg_div, one_div]

/-- A positive completion must repay at least the full harmonic deficit on every multiple of six. -/
theorem criticalCenteredPositiveCompletion_ge_sixth_harmonic
    (correction : ℕ → ℝ)
    (hpositive : ∀ n, 0 ≤ centeredPrimeTailCurrentFourierWeight 1 n + correction n)
    (m : ℕ) :
    1 / ((6 * (m + 1) : ℕ) : ℝ) ≤ correction (6 * (m + 1)) := by
  have h := hpositive (6 * (m + 1))
  rw [centeredPrimeTailCurrentFourierWeight_one_six_mul_succ] at h
  rw [show -1 / ((6 * (m + 1) : ℕ) : ℝ) + correction (6 * (m + 1)) =
      correction (6 * (m + 1)) - 1 / ((6 * (m + 1) : ℕ) : ℝ) by ring] at h
  exact sub_nonneg.mp h

/-- The same lower bound holds for total variation, without assuming the correction itself positive. -/
theorem criticalCenteredPositiveCompletion_abs_ge_sixth_harmonic
    (correction : ℕ → ℝ)
    (hpositive : ∀ n, 0 ≤ centeredPrimeTailCurrentFourierWeight 1 n + correction n)
    (m : ℕ) :
    1 / ((6 * (m + 1) : ℕ) : ℝ) ≤ |correction (6 * (m + 1))| :=
  (criticalCenteredPositiveCompletion_ge_sixth_harmonic correction hpositive m).trans
    (le_abs_self _)

/-- **C48 positive-completion wall.** No absolutely summable atomic correction can turn the exact
critical pole-cancelling source into a nonnegative source. -/
theorem not_summable_abs_of_criticalCenteredPositiveCompletion
    (correction : ℕ → ℝ)
    (hpositive : ∀ n, 0 ≤ centeredPrimeTailCurrentFourierWeight 1 n + correction n) :
    ¬ Summable fun n => |correction n| := by
  intro hsummable
  have hinjective : Function.Injective (fun m : ℕ => 6 * (m + 1)) := by
    intro a b hab
    exact Nat.add_right_cancel (mul_left_cancel₀ (by norm_num : (6 : ℕ) ≠ 0) hab)
  have hsubsequence : Summable fun m => |correction (6 * (m + 1))| :=
    hsummable.comp_injective hinjective
  have hsixth : Summable fun m : ℕ => 1 / ((6 * (m + 1) : ℕ) : ℝ) :=
    Summable.of_nonneg_of_le (fun _ => by positivity)
      (criticalCenteredPositiveCompletion_abs_ge_sixth_harmonic correction hpositive)
      hsubsequence
  have hshifted : Summable fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ) := by
    have hscaled := hsixth.mul_left (6 : ℝ)
    apply hscaled.congr
    intro m
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    field_simp [hm.ne']
  have hnotShifted : ¬ Summable fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ) := by
    exact mt
      (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).mp
      Real.not_summable_one_div_natCast
  exact hnotShifted hshifted

/-- Equivalent existential form: finite total variation and atomic positivity are incompatible. -/
theorem no_summable_criticalCenteredPositiveCompletion :
    ¬ ∃ correction : ℕ → ℝ,
      Summable (fun n => |correction n|) ∧
        ∀ n, 0 ≤ centeredPrimeTailCurrentFourierWeight 1 n + correction n := by
  rintro ⟨correction, hsummable, hpositive⟩
  exact not_summable_abs_of_criticalCenteredPositiveCompletion correction hpositive hsummable

end

end RHTower
