import GaloisForLFunctions.SelbergClass.Primon.KestenMcKay
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DivisorIncidencePerturbationAndLogarithmicDamping
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Log

/-!
# Positive prime-power mass after phase averaging

The negative cosine means turn the explicit-formula contribution at `p^(2m)`
into the positive weight `(p-1) log(p) / p^m`. Summing over the powers of one
prime telescopes. At the squared cutoff `N²`, the resulting mass is exactly
`θ(N)` minus `∑_{p≤N} log(p) / p^(log_p N)`. This defect is nonnegative and
at most `(log N)²`.
-/

open MeasureTheory Set Finset
open scoped BigOperators

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Averaged explicit-formula mass at the even prime power `p^(2*(m+1))`. -/
def averagedPrimePowerWeight (p m : ℕ) : ℝ :=
  ((p : ℝ) - 1) * Real.log p / (p : ℝ) ^ (m + 1)

/-- Integrated averaged mass up to the squared cutoff `N²`. -/
def averagedPrimePowerCount (N : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE N, ∑ m ∈ range (Nat.log p N), averagedPrimePowerWeight p m

/-- Exact deficit from Chebyshev's prime mass at the square-root cutoff. -/
def averagedPrimePowerDefect (N : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE N, Real.log p / (p : ℝ) ^ (Nat.log p N)

/-- The arithmetic weight is the negative phase mean of the corresponding prime-power mode. -/
theorem averagedPrimePowerWeight_eq_phaseMean (p : Nat.Primes) (m : ℕ) :
    averagedPrimePowerWeight p m =
      -2 * Real.log (p : ℝ) *
        (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t *
          Real.cos (2 * Real.pi * (m + 1) * t)) := by
  rw [integral_kestenMcKayDensity_cos_succ, averagedPrimePowerWeight]
  ring

/-- The logarithmic cutoff includes precisely the allowed positive powers of a prime. -/
theorem averagedPrimePower_cutoff_iff (p : Nat.Primes) (N m : ℕ) :
    m < Nat.log p N ↔ (p : ℕ) ^ (m + 1) ≤ N := by
  by_cases hN : N = 0
  · subst N
    simp only [Nat.log_zero_right, not_lt_zero, Nat.le_zero]
    exact iff_of_false (by simp) (ne_of_gt (pow_pos p.property.pos _))
  · exact (Nat.succ_le_iff).symm.trans (Nat.le_log_iff_pow_le p.property.one_lt hN)

/-- Each positive averaged weight is a difference of two consecutive geometric terms. -/
theorem averagedPrimePowerWeight_eq_difference (p : Nat.Primes) (m : ℕ) :
    averagedPrimePowerWeight p m = Real.log (p : ℝ) *
      (((p : ℝ)⁻¹) ^ m - ((p : ℝ)⁻¹) ^ (m + 1)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have he : ((p : ℝ) - 1) * (p : ℝ)⁻¹ = 1 - (p : ℝ)⁻¹ := by
    rw [sub_mul, mul_inv_cancel₀ hp0, one_mul]
  rw [averagedPrimePowerWeight, div_eq_mul_inv, ← inv_pow, pow_succ]
  calc
    _ = Real.log (p : ℝ) * ((p : ℝ)⁻¹) ^ m * (((p : ℝ) - 1) * (p : ℝ)⁻¹) := by ring
    _ = Real.log (p : ℝ) * ((p : ℝ)⁻¹) ^ m * (1 - (p : ℝ)⁻¹) := by rw [he]
    _ = _ := by ring

/-- Every finite tower of averaged powers has an exact telescoping sum. -/
theorem sum_averagedPrimePowerWeight (p : Nat.Primes) (M : ℕ) :
    (∑ m ∈ range M, averagedPrimePowerWeight p m) =
      Real.log (p : ℝ) * (1 - ((p : ℝ)⁻¹) ^ M) := by
  simp_rw [averagedPrimePowerWeight_eq_difference]
  rw [← Finset.mul_sum, Finset.sum_range_sub']
  simp only [pow_zero]

private theorem averagedPrimePowerWeight_nonneg_of_prime {p : ℕ} (hp : p.Prime) (m : ℕ) :
    0 ≤ averagedPrimePowerWeight p m := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  unfold averagedPrimePowerWeight
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hp1) (Real.log_nonneg hp1)) (by positivity)

/-- Phase averaging makes the integrated prime-power mass nonnegative. -/
theorem averagedPrimePowerCount_nonneg (N : ℕ) : 0 ≤ averagedPrimePowerCount N := by
  apply Finset.sum_nonneg
  intro p hp
  exact Finset.sum_nonneg fun m _ =>
    averagedPrimePowerWeight_nonneg_of_prime (Nat.mem_primesLE.mp hp).2 m

/-- The averaged prime-power mass is monotone in its cutoff. -/
theorem averagedPrimePowerCount_mono : Monotone averagedPrimePowerCount := by
  intro N M hNM
  calc
    averagedPrimePowerCount N ≤
        ∑ p ∈ Nat.primesLE N, ∑ m ∈ range (Nat.log p M), averagedPrimePowerWeight p m := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.log_mono_right hNM))
      exact fun m _ _ => averagedPrimePowerWeight_nonneg_of_prime (Nat.mem_primesLE.mp hp).2 m
    _ ≤ averagedPrimePowerCount M := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (fun p hp => Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hNM,
          (Nat.mem_primesLE.mp hp).2⟩)
      intro p hp _
      exact Finset.sum_nonneg fun m _ =>
        averagedPrimePowerWeight_nonneg_of_prime (Nat.mem_primesLE.mp hp).2 m

/-- Exact arithmetic decomposition of the integrated averaged explicit-formula mass. -/
theorem averagedPrimePowerCount_eq_theta_sub_defect (N : ℕ) :
    averagedPrimePowerCount N = Chebyshev.theta N - averagedPrimePowerDefect N := by
  rw [averagedPrimePowerCount, averagedPrimePowerDefect, Chebyshev.theta_eq_sum_primesLE,
    Nat.floor_natCast, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have h := sum_averagedPrimePowerWeight ⟨p, (Nat.mem_primesLE.mp hp).2⟩ (Nat.log p N)
  rw [h]
  simp only [inv_pow, div_eq_mul_inv]
  ring

/-- The deficit is a sum of positive prime contributions. -/
theorem averagedPrimePowerDefect_nonneg (N : ℕ) : 0 ≤ averagedPrimePowerDefect N := by
  apply Finset.sum_nonneg
  intro p hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le
  exact div_nonneg (Real.log_nonneg hp1) (by positivity)

/-- The full tower deficit never exceeds the first-power harmonic prime sum. -/
theorem averagedPrimePowerDefect_le_primeHarmonic (N : ℕ) :
    averagedPrimePowerDefect N ≤ ∑ p ∈ Nat.primesLE N, Real.log p / (p : ℝ) := by
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hpN, hprime⟩ := Nat.mem_primesLE.mp hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hprime.one_lt.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hlog : 1 ≤ Nat.log p N := Nat.log_pos_iff.mpr ⟨hpN, hprime.one_lt⟩
  have hpow : (p : ℝ) ≤ (p : ℝ) ^ Nat.log p N := by
    simpa only [pow_one] using pow_le_pow_right₀ hp1 hlog
  exact div_le_div_of_nonneg_left (Real.log_nonneg hp1) hp0 hpow

/-- A uniform logarithmic-square bound on the exact prime-power deficit. -/
theorem averagedPrimePowerDefect_le_log_sq (N : ℕ) :
    averagedPrimePowerDefect N ≤ (Real.log N) ^ 2 := by
  by_cases hN : N = 0
  · subst N
    simp [averagedPrimePowerDefect]
  · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
    calc
      averagedPrimePowerDefect N ≤ ∑ p ∈ Nat.primesLE N, Real.log p / (p : ℝ) :=
        averagedPrimePowerDefect_le_primeHarmonic N
      _ ≤ ∑ p ∈ Finset.Icc 1 N, Real.log p / (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (fun p hp => Finset.mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.one_lt.le,
            (Nat.mem_primesLE.mp hp).1⟩)
        intro p hp _
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp hp).1
        exact div_nonneg (Real.log_nonneg hp1) (by positivity)
      _ ≤ (Real.log N) ^ 2 :=
        GaloisForLFunctions.TransHorizonIncidenceMechanics.sum_log_div_le_log_sq hN1

/-- The averaged staircase lies between Chebyshev mass and its logarithmic-square correction. -/
theorem averagedPrimePowerCount_bounds (N : ℕ) :
    Chebyshev.theta N - (Real.log N) ^ 2 ≤ averagedPrimePowerCount N ∧
      averagedPrimePowerCount N ≤ Chebyshev.theta N := by
  rw [averagedPrimePowerCount_eq_theta_sub_defect]
  constructor
  · linarith only [averagedPrimePowerDefect_le_log_sq N]
  · linarith only [averagedPrimePowerDefect_nonneg N]

end
end GaloisForLFunctions.SelbergClass.Primon
