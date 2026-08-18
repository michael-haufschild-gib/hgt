import GaloisForLFunctions.RHTower.Sieve.MollifierShortRange
import GaloisForLFunctions.RHTower.SmoothAFECutoffBounds

/-!
# The long range of the mollified coefficient

Beyond the product length `X · x` the mollified coefficient is negligible: every surviving divisor
`m ≤ X` forces the cutoff argument `(k/m)/x` to exceed `k/(X x)`, and the Gaussian cutoff decays
faster than any power there.  This is what makes the effective length of the mollified Dirichlet
polynomial `X · x` and lets the mean value theorem be applied with a finite length.
-/

open Finset ArithmeticFunction GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

/-- **The long-range coefficient bound.**  For every decay exponent `A > 0` the mollified cutoff
coefficient at `k` is at most `d(k) · K · (k/(X x))^{-A}`. -/
theorem exists_norm_sum_moebius_filter_cutoff_le {A : ℝ} (hA : 0 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {x : ℝ}, 0 < x → ∀ {X k : ℕ}, 0 < X → 0 < k →
      ‖∑ m ∈ k.divisors.filter (fun m => m ≤ X), ((μ m : ℤ) : ℂ) *
          smoothAFECutoff ((((k / m : ℕ) : ℝ)) / x)‖
        ≤ (k.divisors.card : ℝ) * (K * (((k : ℝ) / ((X : ℝ) * x)) ^ (-A))) := by
  obtain ⟨K, hK, hcut⟩ := RHTower.exists_norm_smoothAFECutoff_le_neg_rpow hA
  refine ⟨K, hK, ?_⟩
  intro x hx X k hX hk
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hB : (0 : ℝ) ≤ K * (((k : ℝ) / ((X : ℝ) * x)) ^ (-A)) := by
    have : (0 : ℝ) < ((k : ℝ) / ((X : ℝ) * x)) ^ (-A) :=
      Real.rpow_pos_of_pos (by positivity) _
    positivity
  have hterm : ∀ m ∈ k.divisors.filter (fun m => m ≤ X),
      ‖((μ m : ℤ) : ℂ) * smoothAFECutoff ((((k / m : ℕ) : ℝ)) / x)‖
        ≤ K * (((k : ℝ) / ((X : ℝ) * x)) ^ (-A)) := by
    intro m hm
    obtain ⟨hmdvd, hmX⟩ := Finset.mem_filter.mp hm
    have hmpos : 0 < m := Nat.pos_of_mem_divisors hmdvd
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    have hdvd : m ∣ k := Nat.dvd_of_mem_divisors hmdvd
    have hquot : (((k / m : ℕ) : ℝ)) = (k : ℝ) / (m : ℝ) := by
      rw [Nat.cast_div hdvd (ne_of_gt hmR)]
    have hy : (0 : ℝ) < (((k / m : ℕ) : ℝ)) / x := by
      rw [hquot]; positivity
    have hmXR : (m : ℝ) ≤ (X : ℝ) := by exact_mod_cast hmX
    have hlow : (k : ℝ) / ((X : ℝ) * x) ≤ (((k / m : ℕ) : ℝ)) / x := by
      rw [hquot, div_div]
      exact div_le_div_of_nonneg_left hkR.le (by positivity)
        (by nlinarith [hx.le, hmXR])
    have hb := hcut hy
    have hmono : ((((k / m : ℕ) : ℝ)) / x) ^ (-A)
        ≤ ((k : ℝ) / ((X : ℝ) * x)) ^ (-A) := by
      have h1 : (0 : ℝ) < ((k : ℝ) / ((X : ℝ) * x)) ^ A :=
        Real.rpow_pos_of_pos (by positivity) A
      have h2 : ((k : ℝ) / ((X : ℝ) * x)) ^ A ≤ ((((k / m : ℕ) : ℝ)) / x) ^ A :=
        Real.rpow_le_rpow (by positivity) hlow hA.le
      rw [Real.rpow_neg hy.le, Real.rpow_neg (by positivity)]
      have hone := one_div_le_one_div_of_le h1 h2
      simpa [one_div] using hone
    calc ‖((μ m : ℤ) : ℂ) * smoothAFECutoff ((((k / m : ℕ) : ℝ)) / x)‖
        = ‖((μ m : ℤ) : ℂ)‖ * ‖smoothAFECutoff ((((k / m : ℕ) : ℝ)) / x)‖ := norm_mul _ _
      _ ≤ 1 * ‖smoothAFECutoff ((((k / m : ℕ) : ℝ)) / x)‖ :=
          mul_le_mul_of_nonneg_right (norm_moebius_complex_le_one m) (norm_nonneg _)
      _ = ‖smoothAFECutoff ((((k / m : ℕ) : ℝ)) / x)‖ := one_mul _
      _ ≤ K * (((((k / m : ℕ) : ℝ)) / x) ^ (-A)) := hb
      _ ≤ K * (((k : ℝ) / ((X : ℝ) * x)) ^ (-A)) := mul_le_mul_of_nonneg_left hmono hK
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
  rw [nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ hB
  exact_mod_cast Finset.card_filter_le _ _

end RHTower.Sieve
