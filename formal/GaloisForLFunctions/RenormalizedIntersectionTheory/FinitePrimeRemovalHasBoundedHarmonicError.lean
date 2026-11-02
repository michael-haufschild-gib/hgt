import GaloisForLFunctions.RenormalizedIntersectionTheory.TheRoughMeanAtAFixedScale

/-!
# Bounded harmonic error under finite prime removal

A bounded completely multiplicative real sequence need not have a harmonic
asymptotic. Nevertheless, removing finitely many primes multiplies its harmonic
primitive by the finite Euler head, up to a uniformly bounded error. Prime
peeling and the bounded harmonic mass of a multiplicative interval prove this.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

/-- Dividing a horizon by a fixed positive integer changes a bounded-coefficient
harmonic primitive by at most the logarithmic length, with a uniform endpoint error. -/
theorem abs_gaugeHarmonicSum_sub_natDiv_le {ω : ℕ → ℝ} (hbd : ∀ n, |ω n| ≤ 1)
    {p : ℕ} (hp : 1 ≤ p) (Y : ℕ) :
    |gaugeHarmonicSum ω Y - gaugeHarmonicSum ω (Y / p)| ≤ 2 + Real.log (2 * p) := by
  have hH (n : ℕ) : |hsum n - Real.log n| ≤ 1 := by
    simpa only [gaugeHarmonicSum, hsum, one_div] using abs_harmonic_sub_log_le n
  have hdiff := abs_gaugeHarmonicSum_sub_le hbd (Nat.div_le_self Y p)
  have hlog := abs_log_rpow_sub_log_div_rpow_le (β := 1) one_pos le_rfl hp Y
  simp only [Real.rpow_one] at hlog
  linarith only [hdiff, (abs_le.mp (hH Y)).2, (abs_le.mp (hH (Y / p))).1,
    (abs_le.mp hlog).2]

/-- Finite prime removal preserves the harmonic primitive up to its exact Euler
factor and a bounded additive error, without any density or asymptotic hypothesis. -/
theorem exists_abs_roughMean_sub_eulerHead_mul_le {ω : ℕ → ℝ}
    (hmul : ∀ a b, a ≠ 0 → b ≠ 0 → ω (a * b) = ω a * ω b)
    (hbd : ∀ n, |ω n| ≤ 1) (T : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℕ,
      |gaugeHarmonicSum (roughGauge T ω) Y -
        (∏ p ∈ Nat.primesBelow T, (1 - ω p / p)) * gaugeHarmonicSum ω Y| ≤ C := by
  induction T with
  | zero =>
    refine ⟨0, le_rfl, fun Y => ?_⟩
    simp [roughGauge_zero]
  | succ T ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    by_cases hT : T.Prime
    · let a := ω T / T
      let H := ∏ p ∈ Nat.primesBelow T, (1 - ω p / p)
      have hlog : 0 ≤ Real.log (2 * (T : ℝ)) := Real.log_nonneg (by
        have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT.one_lt.le
        linarith only [hT1])
      refine ⟨|1 - a| * C + |a| * (2 + Real.log (2 * T)), by positivity, fun Y => ?_⟩
      have hprod : (∏ p ∈ Nat.primesBelow (T + 1), (1 - ω p / p)) = H * (1 - a) := by
        rw [Nat.primesBelow_succ, if_pos hT, prod_insert (fun h =>
          (Nat.lt_irrefl T) (Nat.mem_primesBelow.mp h).1)]
        dsimp only [H, a]
        ring
      have hpeel := gaugeHarmonicSum_roughGauge_prime hmul hT Y
      have hdiff := abs_gaugeHarmonicSum_sub_natDiv_le (abs_roughGauge_le hbd T) hT.one_lt.le Y
      have heq : gaugeHarmonicSum (roughGauge (T + 1) ω) Y -
          H * (1 - a) * gaugeHarmonicSum ω Y =
          (1 - a) * (gaugeHarmonicSum (roughGauge T ω) Y - H * gaugeHarmonicSum ω Y) +
          a * (gaugeHarmonicSum (roughGauge T ω) Y -
            gaugeHarmonicSum (roughGauge T ω) (Y / T)) := by
        dsimp only [a]
        rw [hpeel]
        ring
      rw [hprod, heq]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (hbound Y) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hdiff (abs_nonneg _))
    · refine ⟨C, hC, fun Y => ?_⟩
      rw [roughGauge_succ_of_not_prime hT, Nat.primesBelow_succ, if_neg hT]
      exact hbound Y

end GaloisForLFunctions.RenormalizedIntersectionTheory
