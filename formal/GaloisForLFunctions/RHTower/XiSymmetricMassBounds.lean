import GaloisForLFunctions.RHTower.XiVerticalRatioLimit
import GaloisForLFunctions.RHTower.XiHorizontalBound
import GaloisForLFunctions.RHTower.XiRectangleFold

/-!
# Two-sided bounds for the symmetric divisor mass

The quarter-path formula expresses the divisor mass of the symmetric rectangle as
`(2/π)` times the difference of the vertical and horizontal contributions.  The vertical one has
ratio `1/2` to `T log T` and the horizontal one is `O(log T)`, so the mass is
`(1/π) T log T (1 + o(1))`; in particular it is trapped between `(1/2π) T log T` and
`(2/π) T log T` at every sufficiently large admissible height.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- The divisor mass of the symmetric rectangle of half-height `T`. -/
def xiSymmetricMass (T : ℝ) : ℤ :=
  xiRegionOrderSum (Rectangle (((1 - 2 : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) ((2 : ℂ) + (T : ℂ) * I))

theorem two_pi_mul_xiSymmetricMass {T : ℝ} (hT : 0 ≤ T)
    (hne : ∀ x : ℝ, xi ((x : ℂ) + (T : ℂ) * I) ≠ 0) :
    2 * Real.pi * (xiSymmetricMass T : ℝ)
      = 4 * (∫ y in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + (y : ℂ) * I)).re)
        - 4 * ∫ x in (1 / 2 : ℝ)..2, (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im :=
  two_pi_mul_regionOrderSum_eq (by norm_num) hne hT

/-- **Two-sided `T log T` bounds for the symmetric divisor mass.** -/
theorem exists_xiSymmetricMass_two_sided :
    ∃ T₀ : ℝ, 4 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → (∀ x : ℝ, xi ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      (1 / (2 * Real.pi)) * (T * Real.log T) ≤ (xiSymmetricMass T : ℝ)
        ∧ (xiSymmetricMass T : ℝ) ≤ (2 / Real.pi) * (T * Real.log T) := by
  obtain ⟨c, hc, hhoriz⟩ := exists_horizontal_xi_bound
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  -- the vertical ratio is eventually within 1/8 of 1/2
  have hV := tendsto_vertical_ratio
  rw [Metric.tendsto_atTop] at hV
  obtain ⟨T₁, hT₁⟩ := hV (1 / 8) (by norm_num)
  refine ⟨max (max T₁ (8 * c)) 4, le_max_right _ _, fun T hT hne => ?_⟩
  have hT4 : (4 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hTc : 8 * c ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTT₁ : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hTlog : (0 : ℝ) < T * Real.log T := by positivity
  set V : ℝ := ∫ y in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + (y : ℂ) * I)).re with hVdef
  set H : ℝ := ∫ x in (1 / 2 : ℝ)..2, (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im with hHdef
  have hVbound : |V / (T * Real.log T) - 1 / 2| < 1 / 8 := by
    have h := hT₁ T hTT₁
    rw [Real.dist_eq] at h
    exact h
  have hVlow : (3 / 8) * (T * Real.log T) ≤ V := by
    rcases abs_lt.mp hVbound with ⟨h1, -⟩
    have h2 : (3 : ℝ) / 8 < V / (T * Real.log T) := by linarith
    rw [lt_div_iff₀ hTlog] at h2
    linarith
  have hVhigh : V ≤ (5 / 8) * (T * Real.log T) := by
    rcases abs_lt.mp hVbound with ⟨-, h2⟩
    have h3 : V / (T * Real.log T) < 5 / 8 := by linarith
    rw [div_lt_iff₀ hTlog] at h3
    linarith
  have hH : |H| ≤ c * Real.log T := hhoriz T hT4 hne
  have hHsmall : |H| ≤ (1 / 8) * (T * Real.log T) := by
    have hlogpos : (0 : ℝ) < Real.log T := by linarith
    have hstep : c * Real.log T ≤ (1 / 8) * (T * Real.log T) := by
      nlinarith [hTc, hlogpos, hc]
    linarith [hH, hstep]
  have hmass := two_pi_mul_xiSymmetricMass (le_of_lt hT0) hne
  rw [← hVdef, ← hHdef] at hmass
  rcases abs_le.mp hHsmall with ⟨hH1, hH2⟩
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith [hmass, hVlow, hH2, hπ, hTlog]
  · rw [div_mul_eq_mul_div, le_div_iff₀ hπ]
    nlinarith [hmass, hVhigh, hH1, hπ, hTlog]

end RHTower
