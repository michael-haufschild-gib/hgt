import GaloisForLFunctions.HTGeometry.ArcsineSeries

/-!
# The endpoint Maclaurin series of `arcsin`

The open-unit-ball expansion in `ArcsineSeries` extends to both endpoints.  The missing analytic
input is summability of the positive central-binomial coefficients.  We prove it without an
asymptotic estimate: finite coefficient sums are bounded by `π / 2` after radial damping, and the
damping tends to one.  Tannery's theorem then identifies the endpoint sum.
-/

namespace GaloisForLFunctions

open Filter
open scoped Nat Topology

/-- Every arcsine coefficient is strictly positive. -/
theorem arcsinCoeff_pos (j : ℕ) : 0 < arcsinCoeff j := by
  unfold arcsinCoeff
  exact div_pos (by exact_mod_cast Nat.centralBinom_pos j) (by positivity)

/-- Every finite sum of arcsine coefficients is at most `π / 2`. -/
theorem sum_range_arcsinCoeff_le_pi_half (N : ℕ) :
    ∑ j ∈ Finset.range N, arcsinCoeff j ≤ Real.pi / 2 := by
  let r : ℕ → ℝ := fun m => (m : ℝ) / (m + 1)
  have hr0 (m : ℕ) : 0 ≤ r m := by
    dsimp only [r]
    positivity
  have hr1 (m : ℕ) : r m < 1 := by
    dsimp only [r]
    rw [div_lt_one (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
    linarith
  have hrlim : Tendsto r atTop (𝓝 1) := by
    simpa [r] using (tendsto_natCast_div_add_atTop (1 : ℝ))
  have hlim : Tendsto
      (fun m => ∑ j ∈ Finset.range N, arcsinCoeff j * r m ^ (2 * j + 1))
      atTop (𝓝 (∑ j ∈ Finset.range N, arcsinCoeff j)) := by
    apply tendsto_finsetSum
    intro j _hj
    simpa using tendsto_const_nhds.mul (hrlim.pow (2 * j + 1))
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall fun m => by
    have habs : |r m| < 1 := by
      rw [abs_of_nonneg (hr0 m)]
      exact hr1 m
    have hs := arcsin_hasSum habs
    have hpartial := hs.summable.sum_le_tsum (Finset.range N)
      (fun j _hj => mul_nonneg (arcsinCoeff_nonneg j) (pow_nonneg (hr0 m) _))
    rw [hs.tsum_eq] at hpartial
    exact hpartial.trans (Real.arcsin_le_pi_div_two (r m))

/-- The endpoint coefficient series `∑ c_j` converges. -/
theorem summable_arcsinCoeff : Summable arcsinCoeff := by
  exact summable_of_sum_range_le arcsinCoeff_nonneg sum_range_arcsinCoeff_le_pi_half

/-- The endpoint coefficient sum is exactly `π / 2`. -/
theorem tsum_arcsinCoeff : ∑' j : ℕ, arcsinCoeff j = Real.pi / 2 := by
  let r : ℕ → ℝ := fun m => (m : ℝ) / (m + 1)
  have hr0 (m : ℕ) : 0 ≤ r m := by
    dsimp only [r]
    positivity
  have hr1 (m : ℕ) : r m < 1 := by
    dsimp only [r]
    rw [div_lt_one (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
    linarith
  have hrlim : Tendsto r atTop (𝓝 1) := by
    simpa [r] using (tendsto_natCast_div_add_atTop (1 : ℝ))
  have htannery : Tendsto
      (fun m => ∑' j : ℕ, arcsinCoeff j * r m ^ (2 * j + 1))
      atTop (𝓝 (∑' j : ℕ, arcsinCoeff j)) := by
    apply tendsto_tsum_of_dominated_convergence summable_arcsinCoeff
    · intro j
      simpa using tendsto_const_nhds.mul (hrlim.pow (2 * j + 1))
    · exact Filter.Eventually.of_forall fun m j => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow,
          abs_of_nonneg (arcsinCoeff_nonneg j), abs_of_nonneg (hr0 m)]
        calc
          arcsinCoeff j * r m ^ (2 * j + 1) ≤ arcsinCoeff j * 1 := by
            exact mul_le_mul_of_nonneg_left
              (pow_le_one₀ (hr0 m) (hr1 m).le) (arcsinCoeff_nonneg j)
          _ = arcsinCoeff j := mul_one _
  have htannery' : Tendsto (fun m => Real.arcsin (r m)) atTop
      (𝓝 (∑' j : ℕ, arcsinCoeff j)) := by
    apply htannery.congr'
    exact Filter.Eventually.of_forall fun m => by
      exact (arcsin_hasSum (by rw [abs_of_nonneg (hr0 m)]; exact hr1 m)).tsum_eq
  have harc : Tendsto (fun m => Real.arcsin (r m)) atTop (𝓝 (Real.arcsin 1)) :=
    Real.continuous_arcsin.continuousAt.tendsto.comp hrlim
  have h := tendsto_nhds_unique htannery' harc
  simpa [Real.arcsin_one] using h

/-- The arcsine series at the positive endpoint. -/
theorem arcsin_hasSum_one :
    HasSum (fun j : ℕ => arcsinCoeff j * (1 : ℝ) ^ (2 * j + 1)) (Real.arcsin 1) := by
  simpa [tsum_arcsinCoeff, Real.arcsin_one] using summable_arcsinCoeff.hasSum

/-- The arcsine series at the negative endpoint. -/
theorem arcsin_hasSum_neg_one :
    HasSum (fun j : ℕ => arcsinCoeff j * (-1 : ℝ) ^ (2 * j + 1)) (Real.arcsin (-1)) := by
  have h := arcsin_hasSum_one.neg
  rw [Real.arcsin_neg]
  apply HasSum.congr_fun h
  intro j
  rw [Odd.neg_one_pow (show Odd (2 * j + 1) from ⟨j, rfl⟩)]
  simp

/-- **Closed-unit-interval arcsine series.**  The Maclaurin expansion is valid for `|u| ≤ 1`. -/
theorem arcsin_hasSum_closed {u : ℝ} (hu : |u| ≤ 1) :
    HasSum (fun j : ℕ => arcsinCoeff j * u ^ (2 * j + 1)) (Real.arcsin u) := by
  rcases hu.lt_or_eq with hu' | hu'
  · exact arcsin_hasSum hu'
  · rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hu' with rfl | rfl
    · exact arcsin_hasSum_one
    · exact arcsin_hasSum_neg_one

end GaloisForLFunctions
