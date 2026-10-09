import GaloisForLFunctions.RHTower.CanonicalProductE1LogDeriv

/-!
# The second Taylor coefficient of the genus-one canonical product

For a square-summable family of nonzero points `a_i` the genus-one product
`P(z) = ∏ (1 - z/a_i) e^{z/a_i}` satisfies `P'(0) = 0` and `P''(0) = -∑_i 1/a_i²`.

**Proof.** Near the origin, `P' = P · (log P)'` and
`(log P)'(z) = ∑ ((z - a_i)⁻¹ + a_i⁻¹) = z ∑ (a_i (z - a_i))⁻¹`. The last series converges uniformly
near `0`, dominated by `2/|a_i|²`. So `P'(z)/z → ∑ (a_i(-a_i))⁻¹ = -∑ 1/a_i²`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace RHTower

variable {ι : Type*}

/-- A square-summable family of nonzero points stays a positive distance away from the origin. -/
theorem exists_pos_le_norm_of_summable_inv_sq {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) : ∃ δ > 0, ∀ i, δ ≤ ‖a i‖ := by
  classical
  have hev := eventually_norm_ge_of_summable_inv_sq hane hsum one_pos
  have hfin : {i | ¬ 1 ≤ ‖a i‖}.Finite := Filter.eventually_cofinite.mp hev
  by_cases hne : hfin.toFinset.Nonempty
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image hfin.toFinset (fun i => ‖a i‖) hne
    refine ⟨min 1 ‖a i₀‖, lt_min one_pos (norm_pos_iff.mpr (hane i₀)), fun i => ?_⟩
    by_cases hi : 1 ≤ ‖a i‖
    · exact (min_le_left _ _).trans hi
    · exact (min_le_right _ _).trans (hi₀ i (by simpa using hi))
  · refine ⟨1, one_pos, fun i => ?_⟩
    by_contra hi
    exact hne ⟨i, by simpa using hi⟩

/-- The reduced Mittag-Leffler series `∑ (a_i (z - a_i))⁻¹`. -/
def canonicalProductE1Reduced (a : ι → ℂ) (z : ℂ) : ℂ := ∑' i, (a i * (z - a i))⁻¹

theorem norm_inv_mul_sub_le {a z : ℂ} {δ : ℝ} (hδa : δ ≤ ‖a‖) (hz : ‖z‖ ≤ δ / 2) (ha : a ≠ 0) :
    ‖(a * (z - a))⁻¹‖ ≤ 2 * (1 / ‖a‖ ^ (2 : ℕ)) := by
  have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hza : ‖a‖ / 2 ≤ ‖z - a‖ := by
    have h1 : ‖a‖ - ‖z‖ ≤ ‖z - a‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le a z
    linarith
  have hza0 : 0 < ‖z - a‖ := lt_of_lt_of_le (by positivity) hza
  rw [norm_inv, norm_mul]
  rw [inv_le_iff_one_le_mul₀ (mul_pos hpos hza0)]
  calc (1 : ℝ) = 2 * (1 / ‖a‖ ^ (2 : ℕ)) * (‖a‖ * (‖a‖ / 2)) := by field_simp
    _ ≤ 2 * (1 / ‖a‖ ^ (2 : ℕ)) * (‖a‖ * ‖z - a‖) := by gcongr

theorem tendsto_canonicalProductE1Reduced_zero {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) :
    Tendsto (canonicalProductE1Reduced a) (𝓝 0) (𝓝 (-∑' i, 1 / (a i) ^ 2)) := by
  obtain ⟨δ, hδ, hδa⟩ := exists_pos_le_norm_of_summable_inv_sq hane hsum
  have hlim : -∑' i, 1 / (a i) ^ 2 = ∑' i, (a i * (0 - a i))⁻¹ := by
    rw [← tsum_neg]
    congr 1
    funext i
    rw [zero_sub, mul_neg, inv_neg, ← pow_two, one_div]
  rw [hlim]
  refine tendsto_tsum_of_dominated_convergence (hsum.mul_left 2) (fun i => ?_) ?_
  · have hc : ContinuousAt (fun z : ℂ => (a i * (z - a i))⁻¹) 0 := by
      refine ContinuousAt.inv₀ (by fun_prop) ?_
      rw [zero_sub, mul_neg]
      exact neg_ne_zero.mpr (mul_ne_zero (hane i) (hane i))
    exact hc.tendsto
  · filter_upwards [ball_mem_nhds (0 : ℂ) (half_pos hδ)] with z hz i
    rw [mem_ball_zero_iff] at hz
    exact norm_inv_mul_sub_le (hδa i) hz.le (hane i)

/-- Near the origin, `P'(z) = z · (∑ (a_i (z - a_i))⁻¹) · P(z)`. -/
theorem deriv_canonicalProductE1Indexed_eq {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) {δ : ℝ} (hδa : ∀ i, δ ≤ ‖a i‖) {z : ℂ}
    (hz : ‖z‖ < δ) :
    deriv (canonicalProductE1Indexed a) z =
      z * canonicalProductE1Reduced a z * canonicalProductE1Indexed a z := by
  have hzne : ∀ i, z ≠ a i := by
    intro i h
    have := hδa i
    rw [← h] at this
    linarith
  have hP0 := canonicalProductE1Indexed_ne_zero a hane hsum hzne
  have hlog := logDeriv_canonicalProductE1Indexed hane hsum hzne
  rw [logDeriv_apply, div_eq_iff hP0] at hlog
  rw [hlog, canonicalProductE1Reduced, ← tsum_mul_left]
  congr 1
  congr 1
  funext i
  have hza : z - a i ≠ 0 := sub_ne_zero.mpr (hzne i)
  have hai := hane i
  field_simp
  ring

/-- **The second Taylor coefficient of the genus-one product.** `P''(0) = -∑ 1/a_i²`. -/
theorem hasDerivAt_deriv_canonicalProductE1Indexed_zero {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ (2 : ℕ))) :
    HasDerivAt (deriv (canonicalProductE1Indexed a)) (-∑' i, 1 / (a i) ^ 2) 0 := by
  obtain ⟨δ, hδ, hδa⟩ := exists_pos_le_norm_of_summable_inv_sq hane hsum
  have hd0 : deriv (canonicalProductE1Indexed a) 0 = 0 := by
    rw [deriv_canonicalProductE1Indexed_eq hane hsum hδa (by simpa using hδ)]
    simp
  have hPc : ContinuousAt (canonicalProductE1Indexed a) 0 :=
    (canonicalProductE1Indexed_analytic a hane hsum 0 (mem_univ 0)).continuousAt
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hlimP : Tendsto (canonicalProductE1Indexed a) (𝓝[≠] 0) (𝓝 1) := by
    have := hPc.tendsto
    rw [canonicalProductE1Indexed_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlimS := (tendsto_canonicalProductE1Reduced_zero hane hsum).mono_left
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hprod := hlimS.mul hlimP
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) hδ)]
    with t ht htb
  rw [mem_ball_zero_iff] at htb
  rw [zero_add, hd0, sub_zero, deriv_canonicalProductE1Indexed_eq hane hsum hδa htb, smul_eq_mul]
  have ht0 : t ≠ 0 := ht
  field_simp

end RHTower
