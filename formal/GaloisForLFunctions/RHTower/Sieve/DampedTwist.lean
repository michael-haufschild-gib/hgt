import GaloisForLFunctions.RHTower.Sieve.DampedFactoredBound
import GaloisForLFunctions.RHTower.Sieve.SmoothVsSharp

/-!
# The damped function, sharpened and twisted

Two steps of the `μ` chain carry over with no work.

`Sieve/SmoothVsSharp.norm_tsum_smoothWeight_sub_sum_le_of_norm_le_one` is generic in the
coefficients, so the smoothed damped sum differs from the sharp one by at most `H + 1`.

The twist `n ↦ n^{-iτ}` is a shift of the abscissa: the twisted damped series at `s` is the untwisted
one at `s + iτ`.  Since `dampedCorrBound` depends only on the real part, the factorisation of
`Sieve/DampedFactoredBound` survives the twist unchanged.
-/

namespace RHTower.Sieve

open Complex Finset GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Smoothed against sharp, for the damped coefficients.** -/
theorem norm_tsum_damped_smoothWeight_sub_sum_le {P : Finset ℕ} {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) {N H : ℝ} (hN : 0 < N) (hH : 0 < H) :
    ‖(∑' n : ℕ, dampedOmegaMoebius P t n
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.range (⌊N⌋₊ + 1), dampedOmegaMoebius P t n‖
      ≤ H + 1 :=
  norm_tsum_smoothWeight_sub_sum_le_of_norm_le_one
    (fun n => norm_dampedOmegaMoebius_le_one ht0 ht1 n) hN hH

/-- The damped coefficients, twisted by an archimedean character. -/
def dampedTwist (P : Finset ℕ) (t τ : ℝ) (n : ℕ) : ℂ :=
  dampedOmegaMoebius P t n * (n : ℂ) ^ (-((τ : ℂ) * Complex.I))

theorem norm_dampedTwist_le_one {P : Finset ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (τ : ℝ)
    (n : ℕ) : ‖dampedTwist P t τ n‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [dampedTwist, dampedOmegaMoebius_zero, zero_mul, norm_zero]
    norm_num
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hcast : ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) := by push_cast; ring
    have h1 : ‖((n : ℕ) : ℂ) ^ (-((τ : ℂ) * Complex.I))‖ = 1 := by
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
      have hre : (-((τ : ℂ) * Complex.I)).re = 0 := by simp
      rw [hre, Real.rpow_zero]
    rw [dampedTwist, norm_mul, h1, mul_one]
    exact norm_dampedOmegaMoebius_le_one ht0 ht1 n

/-- **The twist is a shift of the abscissa.** -/
theorem tsum_dampedTwist_cpow {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (τ : ℝ) {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, dampedTwist P t τ n * (n : ℂ) ^ (-s))
      = dampedInvZeta P t (s + (τ : ℂ) * Complex.I) := by
  have hshift : 1 < (s + (τ : ℂ) * Complex.I).re := by
    have : (s + (τ : ℂ) * Complex.I).re = s.re := by simp
    rw [this]
    exact hs
  rw [← tsum_damped_cpow_eq_dampedInvZeta hPprime ht0 ht1 hshift]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [dampedTwist, dampedOmegaMoebius_zero]
    ring
  · have hne : ((n : ℕ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      exact_mod_cast Nat.cast_ne_zero.2 (by omega)
    rw [dampedTwist, mul_assoc, ← Complex.cpow_add _ _ hne]
    congr 2
    ring

end

end RHTower.Sieve
