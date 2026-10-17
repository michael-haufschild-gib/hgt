import GaloisForLFunctions.RHTower.FiniteComplexPacketEnergyPerturbation

/-!
# Bounded-test energy stability under a smaller packet remainder

An exponentially smaller summable remainder does not change the weighted half-order energy
limit. Tests may have either sign and may vary with the degree.
-/

open Complex Filter Topology
open scoped BigOperators Real

namespace RHTower

theorem abs_finiteWeightedComplexEnergy_add_sub_le {ι : Type*}
    (s : Finset ι) (a r : ι → ℂ) (g : ι → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hg : ∀ i ∈ s, |g i| ≤ M) :
    |(∑ i ∈ s, g i * ‖a i + r i‖ ^ 2) - ∑ i ∈ s, g i * ‖a i‖ ^ 2| ≤
      M * (2 * (∑ i ∈ s, ‖a i‖) * (∑ i ∈ s, ‖r i‖) +
        (∑ i ∈ s, ‖r i‖) ^ 2) := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ i ∈ s, |g i * (‖a i + r i‖ ^ 2 - ‖a i‖ ^ 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, M * (2 * ‖a i‖ * ‖r i‖ + ‖r i‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul (hg i hi) (abs_norm_add_sq_sub_norm_sq_le (a i) (r i))
        (abs_nonneg _) hM
    _ = M * ∑ i ∈ s, (2 * ‖a i‖ * ‖r i‖ + ‖r i‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ M * ∑ i ∈ s, (2 * ‖a i‖ * (∑ j ∈ s, ‖r j‖) +
        ‖r i‖ * (∑ j ∈ s, ‖r j‖)) := by
      apply mul_le_mul_of_nonneg_left _ hM
      apply Finset.sum_le_sum
      intro i hi
      have hr := Finset.single_le_sum (fun j _ => norm_nonneg (r j)) hi
      nlinarith [norm_nonneg (a i), norm_nonneg (r i)]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
      ring

/-- A uniformly bounded test does not amplify an exponentially smaller packet remainder. -/
theorem tendsto_finiteWeightedComplexEnergy_add_of_exponentiallySmaller_l1
    {ι : ℕ → Type*} (s : ∀ n, Finset (ι n))
    (a r : ∀ n, ι n → ℂ) (g : ∀ n, ι n → ℝ) {A R M B beta L : ℝ}
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hB : 0 < B)
    (hbeta0 : 0 ≤ beta) (hbeta : beta < B)
    (hg : ∀ n i, i ∈ s n → |g n i| ≤ M)
    (ha : ∀ n, ∑ i ∈ s n, ‖a n i‖ ≤ A * B ^ n)
    (hr : ∀ n, ∑ i ∈ s n, ‖r n i‖ ≤ R * beta ^ n)
    (hlead : Tendsto (fun n : ℕ => Real.sqrt n / (B ^ 2) ^ n *
      ∑ i ∈ s n, g n i * ‖a n i‖ ^ 2) atTop (nhds L)) :
    Tendsto (fun n : ℕ => Real.sqrt n / (B ^ 2) ^ n *
      ∑ i ∈ s n, g n i * ‖a n i + r n i‖ ^ 2) atTop (nhds L) := by
  let q : ℝ := beta / B
  have hq0 : 0 ≤ q := div_nonneg hbeta0 hB.le
  have hq1 : q < 1 := (div_lt_one hB).mpr hbeta
  have hq2zero := tendsto_sqrtNat_mul_const_pow_of_lt_one
    (sq_nonneg q) (by nlinarith [sq_nonneg (q - 1)])
  have hmajor : Tendsto (fun n : ℕ => M *
      (2 * A * R * (Real.sqrt n * q ^ n) +
        R ^ 2 * (Real.sqrt n * (q ^ 2) ^ n))) atTop (nhds 0) := by
    simpa using (((tendsto_sqrtNat_mul_const_pow_of_lt_one hq0 hq1).const_mul
      (2 * A * R)).add (hq2zero.const_mul (R ^ 2))).const_mul M
  have hdiff : Tendsto (fun n : ℕ => Real.sqrt n / (B ^ 2) ^ n *
      (∑ i ∈ s n, g n i * ‖a n i + r n i‖ ^ 2) -
        Real.sqrt n / (B ^ 2) ^ n * (∑ i ∈ s n, g n i * ‖a n i‖ ^ 2))
      atTop (nhds 0) := by
    apply squeeze_zero_norm'
      (a := fun n : ℕ => M * (2 * A * R * (Real.sqrt n * q ^ n) +
        R ^ 2 * (Real.sqrt n * (q ^ 2) ^ n)))
    · filter_upwards with n
      have hscale : 0 ≤ Real.sqrt n / (B ^ 2) ^ n := by positivity
      have hpert := abs_finiteWeightedComplexEnergy_add_sub_le
        (s n) (a n) (r n) (g n) hM (hg n)
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg hscale]
      calc
        _ ≤ Real.sqrt n / (B ^ 2) ^ n *
            (M * (2 * (∑ i ∈ s n, ‖a n i‖) * (∑ i ∈ s n, ‖r n i‖) +
              (∑ i ∈ s n, ‖r n i‖) ^ 2)) :=
          mul_le_mul_of_nonneg_left hpert hscale
        _ ≤ Real.sqrt n / (B ^ 2) ^ n *
            (M * (2 * (A * B ^ n) * (R * beta ^ n) + (R * beta ^ n) ^ 2)) := by
          gcongr
          · exact ha n
          · exact hr n
          · exact hr n
        _ = _ := by
          dsimp only [q]
          simp only [pow_two, mul_pow, div_pow]
          field_simp [ne_of_gt (pow_pos hB n)]
    · exact hmajor
  convert hlead.add hdiff using 1
  · ext n
    ring
  · simp

end RHTower
