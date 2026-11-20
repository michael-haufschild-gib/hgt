import GaloisForLFunctions.BezoutValuationIncidence.SingularSeries.TwinPrimeConstant

/-!
# Singular densities of the three signed families

For even N all three families at separation kN have the same local-density
factor. Changing N to kN inserts just the odd primes dividing k but not N.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open Finset BezoutValuationIncidence
noncomputable section

/-- The odd prime divisors at which the two excluded classes coincide. -/
def oddFactors (N : ℕ) : Finset ℕ := N.primeFactors.filter (2 < ·)

/-- The even-target Goldbach singular series (1.2). -/
def singularSeries (N : ℕ) : ℝ :=
  2 * twinPrimeConstant * ∏ p ∈ oddFactors N, ((p : ℝ) - 1) / (p - 2)

/-- A uniform positive lower bound for the main term. -/
theorem two_mul_twinPrimeConstant_le (N : ℕ) :
    2 * twinPrimeConstant ≤ singularSeries N := by
  have h : 1 ≤ ∏ p ∈ oddFactors N, ((p : ℝ) - 1) / (p - 2) := by
    apply Finset.one_le_prod
    intro p hp
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
    exact (one_le_div₀ (sub_pos.mpr hp2)).mpr (by linarith only)
  exact le_mul_of_one_le_right (mul_nonneg (by norm_num) twinPrimeConstant_pos.le) h

theorem singularSeries_pos (N : ℕ) : 0 < singularSeries N :=
  (mul_pos (by norm_num : (0 : ℝ) < 2) twinPrimeConstant_pos).trans_le
    (two_mul_twinPrimeConstant_le N)

/-- The local factors contributed by the dilation, with multiplicities discarded. -/
theorem singularSeries_dilate {N k : ℕ} (hN : N ≠ 0) (hk : k ≠ 0) :
    singularSeries (k * N) = singularSeries N *
      ∏ p ∈ oddFactors k \ oddFactors N, ((p : ℝ) - 1) / (p - 2) := by
  have hset : oddFactors (k * N) = oddFactors k ∪ oddFactors N := by
    rw [oddFactors, Nat.primeFactors_mul hk hN, filter_union]
    rfl
  have hnew : (oddFactors k ∪ oddFactors N) \ oddFactors N = oddFactors k \ oddFactors N := by
    ext p
    simp only [mem_sdiff, mem_union]
    tauto
  have hp := Finset.prod_sdiff (f := fun p : ℕ => ((p : ℝ) - 1) / (p - 2))
    (s₁ := oddFactors N) (s₂ := oddFactors k ∪ oddFactors N) subset_union_right
  rw [hnew] at hp
  rw [singularSeries, hset, ← hp, singularSeries]
  ring

#print axioms singularSeries_pos
#print axioms singularSeries_dilate

end
end GaloisForLFunctions.Goldbach.LiLiu
