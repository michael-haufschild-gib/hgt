import GaloisForLFunctions.RHTower.Sieve.GallagherLemma

/-!
# The tail of the Gallagher weight

The weight of Gallagher's identity has total mass `δ`, but it is also `O(w^{-2})`, so the mass it
carries beyond a height `W` is at most `1/(π²W)` on each side.  That is what lets a bound on the
Dirichlet polynomial valid only on a bounded range of frequencies be used: the far frequencies
contribute at most the trivial size times the tail mass.

The weight is even, so the two tails are equal.
-/

namespace RHTower.Sieve

open Complex MeasureTheory FourierTransform

/-- The Fejér weight is even in the frequency. -/
theorem fejerWeightAt_neg (T L : ℝ) : fejerWeightAt T (-L) = fejerWeightAt T L := by
  rw [fejerWeightAt, fejerWeightAt, neg_neg]
  ring

/-- The Gallagher weight is even. -/
theorem fourier_triC_even {δ : ℝ} (hδ : 0 < δ) (w : ℝ) :
    𝓕 (triC δ) (-w) = 𝓕 (triC δ) w := by
  rw [fourier_triC hδ, fourier_triC hδ,
    show -(2 * Real.pi * -w) = -(-(2 * Real.pi * w)) by ring, fejerWeightAt_neg]

/-- **The Gallagher weight decays like `1/(π²w²)`.** -/
theorem fourier_triC_re_le_inv_sq {δ : ℝ} (hδ : 0 < δ) {w : ℝ} (hw : w ≠ 0) :
    (𝓕 (triC δ) w).re ≤ 1 / (Real.pi ^ 2 * w ^ 2) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hw2 : (0 : ℝ) < w ^ 2 := by positivity
  set L : ℝ := -(2 * Real.pi * w) with hLdef
  have hL0 : L ≠ 0 := by
    rw [hLdef]
    intro h
    have : Real.pi * w = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' (ne_of_gt hpi)
    · exact hw h'
  have hLsq : L ^ 2 = 4 * Real.pi ^ 2 * w ^ 2 := by rw [hLdef]; ring
  have hbd : ‖fejerWeightAt δ L‖ ≤ 4 / (δ * L ^ 2) := norm_fejerWeightAt_le hδ hL0
  have hre : (𝓕 (triC δ) w).re ≤ ‖𝓕 (triC δ) w‖ := Complex.re_le_norm _
  have hnorm : ‖𝓕 (triC δ) w‖ = δ * ‖fejerWeightAt δ L‖ := by
    rw [fourier_triC hδ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  refine le_trans hre ?_
  rw [hnorm, hLsq] at *
  rw [le_div_iff₀ (by positivity)]
  have hstep : ‖fejerWeightAt δ L‖ * (δ * (4 * Real.pi ^ 2 * w ^ 2)) ≤ 4 := by
    rw [← le_div_iff₀ (by positivity)]
    exact hbd
  nlinarith [hstep, norm_nonneg (fejerWeightAt δ L), hδ.le]

/-- **The tail mass of the Gallagher weight beyond a height.** -/
theorem integral_Ioi_fourier_triC_re_le {δ : ℝ} (hδ : 0 < δ) {W : ℝ} (hW : 0 < W) :
    (∫ w in Set.Ioi W, (𝓕 (triC δ) w).re) ≤ 1 / (Real.pi ^ 2 * W) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hf : IntegrableOn (fun w : ℝ => (𝓕 (triC δ) w).re) (Set.Ioi W) :=
    ((integrable_fourier_triC hδ).re).integrableOn
  have hg : IntegrableOn (fun w : ℝ => (1 / Real.pi ^ 2) * w ^ (-2 : ℝ)) (Set.Ioi W) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hW).const_mul _
  have hmono : ∀ w ∈ Set.Ioi W,
      (𝓕 (triC δ) w).re ≤ (1 / Real.pi ^ 2) * w ^ (-2 : ℝ) := by
    intro w hw
    have hw0 : (0 : ℝ) < w := lt_trans hW hw
    have hrw : w ^ (-2 : ℝ) = 1 / w ^ 2 := by
      rw [Real.rpow_neg hw0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast, one_div]
    rw [hrw]
    have := fourier_triC_re_le_inv_sq hδ (ne_of_gt hw0)
    calc (𝓕 (triC δ) w).re ≤ 1 / (Real.pi ^ 2 * w ^ 2) := this
      _ = 1 / Real.pi ^ 2 * (1 / w ^ 2) := by
          rw [one_div, one_div, one_div, mul_inv]
  refine le_trans (setIntegral_mono_on hf hg measurableSet_Ioi hmono) ?_
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hW,
    show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  rw [le_div_iff₀ (by positivity)]
  field_simp
  norm_num

end RHTower.Sieve
