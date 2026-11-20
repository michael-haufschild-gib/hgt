import GaloisForLFunctions.goldbach.LiLiu.PrimePowerRemoval
import GaloisForLFunctions.goldbach.LiLiu.SingularDensity
import GaloisForLFunctions.goldbach.LiLiu.TestWeight

/-!
# From the weighted asymptotic to ordered prime representations

After division by N, the proper-prime-power error is at most
4 (log N)² / √N. The singular series has a uniform positive lower bound,
so this error can be absorbed even along targets with varying local density.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open Filter Finset BezoutValuationIncidence
open scoped Topology
noncomputable section

private theorem normalized_primePower_error_tendsto :
    Tendsto (fun N : ℕ => 4 * (Real.log N ^ 2 / Real.sqrt N)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have h' := (tendsto_const_nhds (x := (4 : ℝ))).mul (h.comp tendsto_natCast_atTop_atTop)
  simpa only [Function.comp_def, Real.rpow_two, Real.sqrt_eq_rpow, mul_zero] using h'

/-- At every sufficiently large target, subtracting ε times the singular series pays
for both nonprime endpoints. No asymptotic formula for the correlation is used. -/
theorem eventually_correlation_sub_le_count (φ : TestWeight) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (correlation φ N - ε * singularSeries N) * N ≤
      (centralPrimePairs N).card * Real.log N ^ 2 := by
  have hpos := mul_pos hε (mul_pos (by norm_num : (0 : ℝ) < 2) twinPrimeConstant_pos)
  filter_upwards [eventually_ge_atTop 2,
    normalized_primePower_error_tendsto.eventually_lt_const hpos] with N hN hsmall
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hp : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one h1
  have hL := Real.log_nonneg h1
  have hroot := Real.sqrt_pos.mpr hp
  have he : 4 * Real.log N ^ 2 ≤ ε * singularSeries N * Real.sqrt N := by
    rw [← mul_div_assoc, div_lt_iff₀ hroot] at hsmall
    exact hsmall.le.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (two_mul_twinPrimeConstant_le N) hε.le) hroot.le)
  have hscaled := mul_le_mul_of_nonneg_right he hroot.le
  have hpp := mul_le_mul_of_nonneg_right (Chebyshev.psi_sub_theta_le h1) hL
  have hb := correlation_mul_le_count_add_primePowers φ φ.values φ.supported (by omega : 1 ≤ N)
  rw [mul_assoc (ε * singularSeries N), Real.mul_self_sqrt hp.le] at hscaled
  linarith only [hb, hpp, hscaled]

/-- The quantitative conclusion once the relative weighted estimate is available on even N. -/
theorem count_of_eventual_weighted_lower (φ : TestWeight)
    (h : ∀ᶠ N : ℕ in atTop, Even N → φ.mass / 2 * singularSeries N ≤ correlation φ N) :
    ∀ᶠ N : ℕ in atTop, Even N →
      φ.mass / 4 * singularSeries N * N / Real.log N ^ 2 ≤ (centralPrimePairs N).card := by
  filter_upwards [eventually_ge_atTop 2, h,
    eventually_correlation_sub_le_count φ (show 0 < φ.mass / 4 by exact div_pos φ.mass_pos (by norm_num))]
    with N hN hmain hcount hEven
  have hL := Real.log_pos (show (1 : ℝ) < N by exact_mod_cast (by omega : 1 < N))
  apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
  apply le_trans _ hcount
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
  linarith only [hmain hEven]

/-- The positive count supplies two actual primes in the stated interval. -/
theorem prime_pair_of_eventual_weighted_lower (φ : TestWeight)
    (h : ∀ᶠ N : ℕ in atTop, Even N → φ.mass / 2 * singularSeries N ≤ correlation φ N) :
    ∀ᶠ N : ℕ in atTop, Even N → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N ∧
      (p : ℝ) ∈ Set.Icc ((N : ℝ) / 3) (2 * N / 3) ∧
      (q : ℝ) ∈ Set.Icc ((N : ℝ) / 3) (2 * N / 3) := by
  filter_upwards [eventually_ge_atTop 2, count_of_eventual_weighted_lower φ h] with N hN hc he
  have hp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL := Real.log_pos (show (1 : ℝ) < N by exact_mod_cast (by omega : 1 < N))
  have hpos := div_pos (mul_pos (mul_pos (div_pos φ.mass_pos (by norm_num))
    (singularSeries_pos N)) hp) (sq_pos_of_pos hL)
  have hcard : 0 < (centralPrimePairs N).card := by exact_mod_cast hpos.trans_le (hc he)
  obtain ⟨⟨p, q⟩, hpq⟩ := Finset.card_pos.mp hcard
  obtain ⟨hs, hpr, hqr, hw, hv⟩ := Finset.mem_filter.mp hpq
  have window (k : ℕ) (hk : inWindow N k) :
      (k : ℝ) ∈ Set.Icc ((N : ℝ) / 3) (2 * N / 3) := by
    have a := (le_div_iff₀ hp).mp hk.1
    have b := (div_le_iff₀ hp).mp hk.2
    exact ⟨by linarith only [a], by linarith only [b]⟩
  exact ⟨p, q, hpr, hqr, Finset.mem_antidiagonal.mp hs, window p hw, window q hv⟩

#print axioms prime_pair_of_eventual_weighted_lower
#print axioms eventually_correlation_sub_le_count
#print axioms count_of_eventual_weighted_lower

end
end GaloisForLFunctions.Goldbach.LiLiu
