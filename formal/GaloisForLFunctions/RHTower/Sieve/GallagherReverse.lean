import GaloisForLFunctions.RHTower.Sieve.GallagherLemma

/-!
# Gallagher's lemma in the mean-value direction

The exact overlap identity

`∫_ℝ ‖∑_{u < log n ≤ u+δ} a_n‖² du = ∫_ℝ Re 𝓕(δ-|·|)₊(w) · ‖∑_n a_n n^{2πiw}‖² dw`

is an equality, so it can be read in either direction.  Read from right to left it bounds a
short-interval mean square by a frequency integral; read from left to right — which is Gallagher's
lemma — it bounds the frequency integral over a *bounded* range by the short-interval mean square,
because the Fejér weight is bounded below on the central range:

`Re 𝓕(δ-|·|)₊(w) ≥ (4/5) δ²`   whenever `|2π δ w| ≤ 1`.

The lower bound comes from `2 - 2 cos θ ≥ (4/5)θ²` for `|θ| ≤ 1`, i.e. from the second-order Taylor
bound for the cosine.  The resulting inequality

`∫_{-W}^{W} ‖∑_n a_n n^{2πiw}‖² dw ≤ (5/(4δ²)) ∫_ℝ ‖∑_{u < log n ≤ u+δ} a_n‖² du`,   `2πδW ≤ 1`,

is the engine of every mean-value estimate for a Dirichlet polynomial whose coefficients are
concentrated: the short-interval sums are estimated by a count, not by the diagonal.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Set
open scoped FourierTransform

/-- The cosine's second-order Taylor bound in the form the Fejér weight needs. -/
theorem four_fifths_sq_le_two_sub_two_mul_cos {θ : ℝ} (hθ : |θ| ≤ 1) :
    (4 / 5) * θ ^ (2 : ℕ) ≤ 2 - 2 * Real.cos θ := by
  have hb := Real.cos_bound hθ
  rw [abs_le] at hb
  nlinarith [abs_nonneg θ, sq_abs θ, pow_le_one₀ (abs_nonneg θ) hθ (n := 4),
    abs_nonneg (θ ^ (4 : ℕ))]

/-- **The Fejér weight is bounded below on the central frequency range.** -/
theorem le_fejerWeightAt_re (L : ℝ) {T : ℝ} (hT : 0 < T) (hTL : |T * L| ≤ 1) :
    (4 / 5) * T ≤ (fejerWeightAt T L).re := by
  rcases eq_or_ne L 0 with rfl | hL
  · rw [fejerWeightAt_zero hT, Complex.ofReal_re]
    linarith
  · rw [fejerWeightAt, integral_fejer_symm_real L hL hT, Complex.ofReal_re]
    have hL2 : (0 : ℝ) < L ^ (2 : ℕ) := by positivity
    have hden : (0 : ℝ) < T * L ^ (2 : ℕ) := by positivity
    have hcos := four_fifths_sq_le_two_sub_two_mul_cos hTL
    rw [le_div_iff₀ hden]
    have hexp : (4 / 5) * (T * L) ^ (2 : ℕ) = (4 / 5) * T * (T * L ^ (2 : ℕ)) := by ring
    linarith [hexp.symm.trans_le hcos]

/-- **The Fourier weight of the triangular kernel is bounded below on the central range.** -/
theorem le_fourier_triC_re {δ : ℝ} (hδ : 0 < δ) {w : ℝ}
    (hw : |2 * Real.pi * δ * w| ≤ 1) :
    (4 / 5) * δ ^ (2 : ℕ) ≤ (𝓕 (triC δ) w).re := by
  have hTL : |δ * (-(2 * Real.pi * w))| ≤ 1 := by
    rw [abs_mul, abs_neg, ← abs_mul]
    rw [show δ * (2 * Real.pi * w) = 2 * Real.pi * δ * w by ring] at *
    exact hw
  have h := le_fejerWeightAt_re (-(2 * Real.pi * w)) hδ hTL
  rw [fourier_triC hδ w, Complex.re_ofReal_mul]
  calc (4 / 5) * δ ^ (2 : ℕ) = δ * ((4 / 5) * δ) := by ring
    _ ≤ δ * (fejerWeightAt δ (-(2 * Real.pi * w))).re :=
        mul_le_mul_of_nonneg_left h hδ.le

/-- **Gallagher's lemma.**  On a symmetric frequency range the mean square of a Dirichlet polynomial
is controlled by the mean square of its short-interval sums. -/
theorem integral_Icc_normSq_logPoly_le_window (a : ℕ → ℂ) (s : Finset ℕ) {δ W : ℝ}
    (hδ : 0 < δ) (hWδ : 2 * Real.pi * δ * W ≤ 1) :
    (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ (2 : ℕ))
      ≤ (5 / (4 * δ ^ (2 : ℕ))) * ∫ u : ℝ, ‖logWindowSum a s δ u‖ ^ (2 : ℕ) := by
  have hδ2 : (0 : ℝ) < 4 * δ ^ (2 : ℕ) := by positivity
  have hweight := integrable_gallagher_weight_mul hδ a s
  have hcont : Continuous fun w : ℝ => ‖logPoly a s w‖ ^ (2 : ℕ) :=
    ((continuous_logPoly a s).norm).pow 2
  have hstep : ∀ w ∈ Set.Icc (-W) W,
      ‖logPoly a s w‖ ^ (2 : ℕ)
        ≤ (5 / (4 * δ ^ (2 : ℕ))) * ((𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ (2 : ℕ)) := by
    intro w hw
    have hwabs : |w| ≤ W := by
      rw [abs_le]
      exact ⟨hw.1, hw.2⟩
    have hbound : |2 * Real.pi * δ * w| ≤ 1 := by
      have hpos : (0 : ℝ) < 2 * Real.pi * δ := by positivity
      rw [abs_mul, abs_of_pos hpos]
      calc (2 * Real.pi * δ) * |w| ≤ (2 * Real.pi * δ) * W :=
            mul_le_mul_of_nonneg_left hwabs hpos.le
        _ ≤ 1 := hWδ
    have hlow := le_fourier_triC_re hδ hbound
    have hsq : (0 : ℝ) ≤ ‖logPoly a s w‖ ^ (2 : ℕ) := by positivity
    have hmul : (4 / 5) * δ ^ (2 : ℕ) * ‖logPoly a s w‖ ^ (2 : ℕ)
        ≤ (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right hlow hsq
    have hc : (0 : ℝ) < 5 / (4 * δ ^ (2 : ℕ)) := by positivity
    have h2 := mul_le_mul_of_nonneg_left hmul hc.le
    have hid : (5 / (4 * δ ^ (2 : ℕ))) * ((4 / 5) * δ ^ (2 : ℕ) * ‖logPoly a s w‖ ^ (2 : ℕ))
        = ‖logPoly a s w‖ ^ (2 : ℕ) := by
      field_simp
    linarith [h2, hid.le, hid.ge]
  have hle : (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ (2 : ℕ))
      ≤ ∫ w in Set.Icc (-W) W,
          (5 / (4 * δ ^ (2 : ℕ))) * ((𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ (2 : ℕ)) := by
    refine setIntegral_mono_on ?_ ?_ measurableSet_Icc hstep
    · exact (hcont.continuousOn.integrableOn_compact isCompact_Icc)
    · exact (hweight.const_mul _).integrableOn
  refine hle.trans ?_
  rw [MeasureTheory.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (setIntegral_le_integral hweight ?_) ?_
  · filter_upwards with w
    exact mul_nonneg (fourier_triC_re_nonneg hδ w) (by positivity)
  · rw [← gallagher_identity a s hδ]

end RHTower.Sieve

end
