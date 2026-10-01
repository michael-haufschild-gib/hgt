import GaloisForLFunctions.HTGeometry.MellinRegularStrip
import GaloisForLFunctions.RHTower.DegreeThreeHankelChartMultiplier

/-!
# The derivative bound for antisymmetric chart functions

For `Φ` regular on `-1 < Re w < 2` with `Φ(w) = -m̃(w) Φ(1-w)` (the antisymmetry of the cube-root
chart transform of `ζ(s)³`'s functional equation), the chart function `F = Mellin⁻¹_{1/2} Φ` and its
derivative `F'(X) = X⁻¹ Mellin⁻¹(-wΦ)(X)` satisfy

`∫₀^∞ |F'|² ≤ K² ∫₀^∞ X² |F|²`,  where `|u m̃(u)| ≤ K` on `Re u = -1/2`.

Mellin–Plancherel turns the left side into `(1/2π) ∫ |uΦ(u)|²` on `Re u = -1/2` and the right side
into `(1/2π) ∫ |Φ|²` on `Re w = 3/2`; antisymmetry maps one line to the other with factor
`|u m̃(u)| ≤ K`. With `K = 2πκ` this is the estimate `‖F'‖ ≤ 2πκ ‖XF‖` that drives the
Kulikov–Nazarov–Sodin sampling inequality (Lemma B).
-/

open Complex MeasureTheory Filter Set Topology

noncomputable section

namespace RHTower.DegreeThreeHankel

open GaloisForLFunctions.HTGeometry

/-- **The chart derivative bound.** Let `Φ` be regular on `-1 < Re w < 2` and antisymmetric,
`Φ(w) = -m̃(w) Φ(1-w)`, and let `|u m̃(u)| ≤ K` on `Re u = -1/2`. Then
`F = Mellin⁻¹_{1/2} Φ` satisfies `∫ |F'|² ≤ K² ∫ X² |F|²` with `F'(X) = X⁻¹ Mellin⁻¹(-wΦ)(X)`. -/
theorem integral_norm_sq_chartDeriv_le {Φ : ℂ → ℂ} (hΦ : MellinRegularStrip Φ (-1) 2)
    (hanti : ∀ w : ℂ, -1 < w.re → w.re < 2 → Φ w = -chartMultiplier w * Φ (1 - w))
    {K : ℝ} (hK : ∀ t : ℝ, ‖((-1 / 2 : ℂ) + t * I) * chartMultiplier ((-1 / 2 : ℂ) + t * I)‖ ≤ K) :
    ∫ x in Ioi (0 : ℝ), ‖((x : ℂ))⁻¹ * mellinInv (1 / 2) (fun w => -w * Φ w) x‖ ^ 2
      ≤ K ^ 2 * ∫ x in Ioi (0 : ℝ), ‖mellinInv (1 / 2) Φ x‖ ^ 2 * x ^ 2 := by
  have hdΦ : MellinRegularStrip (fun w => -w * Φ w) (-1) 2 := by
    have h := hΦ.mul_id
    refine ⟨fun s h1 h2 => (h.diff s h1 h2).neg.congr_of_eventuallyEq
      (Eventually.of_forall fun z => by simp only [Pi.neg_apply]; ring), fun a b ha hb k => ?_⟩
    obtain ⟨C, hC⟩ := h.decay a b ha hb k
    exact ⟨C, fun s h1 h2 => by simpa [neg_mul, norm_neg] using hC s h1 h2⟩
  -- left side: Plancherel at `-1/2`
  have hL : ∫ x in Ioi (0 : ℝ), ‖((x : ℂ))⁻¹ * mellinInv (1 / 2) (fun w => -w * Φ w) x‖ ^ 2
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖(fun w => -w * Φ w) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 := by
    rw [← integral_norm_sq_mellinInv (Ψ := fun w => -w * Φ w) (σ := -1 / 2)
      (hdΦ.integrable_line (c := -1 / 2) (by norm_num) (by norm_num))
      (hdΦ.memLp_two_line (c := -1 / 2) (by norm_num) (by norm_num))]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx' : (0 : ℝ) < x := hx
    rw [hdΦ.mellinInv_eq (c₁ := 1 / 2) (c₂ := -1 / 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hx']
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx', mul_pow]
    have : x ^ (2 * (-1 / 2 : ℝ) - 1) = (x ^ 2)⁻¹ := by
      rw [show 2 * (-1 / 2 : ℝ) - 1 = -2 by norm_num, Real.rpow_neg hx'.le]; norm_cast
    rw [this, inv_pow]; ring
  -- right side: Plancherel at `3/2`
  have hR : ∫ x in Ioi (0 : ℝ), ‖mellinInv (1 / 2) Φ x‖ ^ 2 * x ^ 2
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖Φ (((3 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 := by
    rw [← integral_norm_sq_mellinInv (Ψ := Φ) (σ := 3 / 2)
      (hΦ.integrable_line (c := 3 / 2) (by norm_num) (by norm_num))
      (hΦ.memLp_two_line (c := 3 / 2) (by norm_num) (by norm_num))]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx' : (0 : ℝ) < x := hx
    rw [hΦ.mellinInv_eq (c₁ := 1 / 2) (c₂ := 3 / 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hx']
    congr 1
    rw [show 2 * (3 / 2 : ℝ) - 1 = (2 : ℕ) by norm_num, Real.rpow_natCast]
  rw [hL, hR]
  -- pointwise comparison on the lines
  have hpt : ∀ t : ℝ, ‖(fun w => -w * Φ w) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
      ≤ K ^ 2 * ‖Φ (((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * I)‖ ^ 2 := by
    intro t
    set u : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I with hu
    have hre1 : -1 < u.re := by simp [hu]; norm_num
    have hre2 : u.re < 2 := by simp [hu]; norm_num
    have h1u : 1 - u = ((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * I := by rw [hu]; push_cast; ring
    have hbound := hK t
    have hu' : ((-1 / 2 : ℂ) + t * I) = u := by rw [hu]; push_cast; ring
    rw [hu'] at hbound
    simp only
    rw [hanti u hre1 hre2, h1u]
    have hK0 : 0 ≤ K := le_trans (norm_nonneg _) hbound
    calc ‖-u * (-chartMultiplier u * Φ (((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * I))‖ ^ 2
        = (‖u * chartMultiplier u‖ * ‖Φ (((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * I)‖) ^ 2 := by
          rw [show -u * (-chartMultiplier u * Φ (((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * I))
            = u * chartMultiplier u * Φ (((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * I) by ring, norm_mul]
      _ ≤ (K * ‖Φ (((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * I)‖) ^ 2 := by
          gcongr
      _ = K ^ 2 * ‖Φ (((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * I)‖ ^ 2 := by ring
  have hint1 : Integrable fun t : ℝ => ‖(fun w => -w * Φ w) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 := by
    have := hdΦ.memLp_two_line (c := -1 / 2) (by norm_num) (by norm_num)
    exact (memLp_two_iff_integrable_sq_norm this.1).mp this
  have hint2 : Integrable fun t : ℝ => ‖Φ (((3 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 := by
    have := hΦ.memLp_two_line (c := 3 / 2) (by norm_num) (by norm_num)
    exact (memLp_two_iff_integrable_sq_norm this.1).mp this
  have hneg : ∫ t : ℝ, ‖Φ (((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * I)‖ ^ 2
      = ∫ t : ℝ, ‖Φ (((3 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 :=
    integral_neg_eq_self (fun t : ℝ => ‖Φ (((3 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2) volume
  have hmono : ∫ t : ℝ, ‖(fun w => -w * Φ w) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
      ≤ ∫ t : ℝ, K ^ 2 * ‖Φ (((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * I)‖ ^ 2 :=
    integral_mono hint1 ((hint2.comp_neg).const_mul _) hpt
  rw [integral_const_mul, hneg] at hmono
  have h2π : 0 ≤ 1 / (2 * Real.pi) := by positivity
  calc 1 / (2 * Real.pi) * ∫ t : ℝ, ‖(fun w => -w * Φ w) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
      ≤ 1 / (2 * Real.pi) * (K ^ 2 * ∫ t : ℝ, ‖Φ (((3 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmono h2π
    _ = K ^ 2 * (1 / (2 * Real.pi) * ∫ t : ℝ, ‖Φ (((3 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2) := by ring

end RHTower.DegreeThreeHankel
