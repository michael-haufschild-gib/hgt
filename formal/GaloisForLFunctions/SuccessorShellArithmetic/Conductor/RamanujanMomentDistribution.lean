import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.DivisorJetReciprocity

/-!
# The complete distribution of a Ramanujan mode

Gcd classes give the whole distribution, not only its quadratic energy.
A divisor `d` contributes `φ(d)` copies of `φ(M) μ(d) / φ(d)`.
Applying an arbitrary test function gives every moment and every finite
spectral statistic of the conductor mode.
-/

open Finset ArithmeticFunction
open scoped BigOperators

namespace GaloisForLFunctions.SuccessorShellArithmetic
open BezoutValuationIncidence BiScaleUncertainty
noncomputable section

/-- The exact finite distribution of the conductor-`M` mode. -/
theorem sum_range_ramanujan_distribution (M : ℕ+) (F : ℝ → ℝ) :
    (∑ n ∈ range (M : ℕ), F (ramanujanLagCoefficient M n)) =
      ∑ d ∈ (M : ℕ).divisors, (d.totient : ℝ) *
        F ((Nat.totient M : ℝ) * (moebiusReal d / (d.totient : ℝ))) := by
  have hg := sum_range_gcd_profile M.pos (fun n => F (ramanujanLagCoefficient M n))
  simp only [ramanujanLagCoefficient_gcd_period (dvd_refl (M : ℕ))] at hg
  rw [hg]
  calc
    _ = ∑ d ∈ (M : ℕ).divisors, ((M / d : ℕ).totient : ℝ) *
        F ((Nat.totient M : ℝ) *
          (moebiusReal (M / d) / ((M / d : ℕ).totient : ℝ))) := by
      apply sum_congr rfl
      intro d hd
      rw [ramanujanLagCoefficient_eq_totient_mul,
        sieveLagMultiplier_eq_moebius_totient_quotient,
        Nat.gcd_eq_right (Nat.dvd_of_mem_divisors hd)]
    _ = _ := Nat.sum_div_divisors (M : ℕ) (fun d => (d.totient : ℝ) *
      F ((Nat.totient M : ℝ) * (moebiusReal d / (d.totient : ℝ))))

/-- Every raw moment is an explicit totient-weighted divisor sum. -/
theorem sum_range_ramanujan_pow_divisors (M : ℕ+) (k : ℕ) :
    (∑ n ∈ range (M : ℕ), ramanujanLagCoefficient M n ^ k) =
      (Nat.totient M : ℝ) ^ k *
        ∑ d ∈ (M : ℕ).divisors,
          (d.totient : ℝ) * (moebiusReal d / (d.totient : ℝ)) ^ k := by
  rw [sum_range_ramanujan_distribution M (fun x => x ^ k), mul_sum]
  apply sum_congr rfl
  intro d _
  rw [mul_pow]
  ring

/-- The normalized lag multiplier has a modulus-independent value on each divisor class. -/
theorem sum_range_sieveLagMultiplier_distribution (M : ℕ+) (F : ℝ → ℝ) :
    (∑ n ∈ range (M : ℕ), F (sieveLagMultiplier M n)) =
      ∑ d ∈ (M : ℕ).divisors, (d.totient : ℝ) *
        F (moebiusReal d / (d.totient : ℝ)) := by
  have hp : (Nat.totient M : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr M.pos).ne'
  simpa only [sieveLagMultiplier, mul_div_cancel_left₀ _ hp] using
    sum_range_ramanujan_distribution M (fun x => F (x / (Nat.totient M : ℝ)))

/-- All normalized moments retain the same finite divisor measure. -/
theorem sum_range_sieveLagMultiplier_pow (M : ℕ+) (k : ℕ) :
    (∑ n ∈ range (M : ℕ), sieveLagMultiplier M n ^ k) =
      ∑ d ∈ (M : ℕ).divisors,
        (d.totient : ℝ) * (moebiusReal d / (d.totient : ℝ)) ^ k :=
  sum_range_sieveLagMultiplier_distribution M (fun x => x ^ k)

#print axioms sum_range_ramanujan_distribution
#print axioms sum_range_ramanujan_pow_divisors
#print axioms sum_range_sieveLagMultiplier_distribution
#print axioms sum_range_sieveLagMultiplier_pow

end
end GaloisForLFunctions.SuccessorShellArithmetic
