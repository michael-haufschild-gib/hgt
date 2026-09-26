import Mathlib

/-!
# A weighted double-integral bound through Tonelli

Let `H` be continuous with `H(t) ≤ ψ(t) K ∫₀^{2π} q(t, θ) dθ` for every `t`, where `0 ≤ ψ ≤ Λ`, `K ≥ 0`,
`q ≥ 0` is jointly continuous and `∫_{[0,T]} q(t, θ) dt ≤ B` for every `θ`.  Then

  `∫₀ᵀ H ≤ Λ K (2π B)`.

The integral of `H` is at most that of its positive part, which is a lower integral dominated by
`Λ K ∫_{[0,T]} ∫_{(0,2π]} q`; Tonelli swaps the two lower integrals.
-/

open MeasureTheory Set Real

namespace GaloisForLFunctions.HTGeometry

theorem integral_le_of_weighted_double {H ψ : ℝ → ℝ} {q : ℝ → ℝ → ℝ} (hH : Continuous H)
    (hq : Continuous (Function.uncurry q)) (hq0 : ∀ t θ, 0 ≤ q t θ) {Λ K B T : ℝ}
    (hψ0 : ∀ t, 0 ≤ ψ t) (hψΛ : ∀ t, ψ t ≤ Λ) (hK : 0 ≤ K) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hbound : ∀ θ, ∫⁻ t in Icc 0 T, ENNReal.ofReal (q t θ) ≤ ENNReal.ofReal B)
    (hHle : ∀ t, H t ≤ ψ t * (K * ∫ θ in (0 : ℝ)..2 * π, q t θ)) :
    ∫ t in (0 : ℝ)..T, H t ≤ Λ * K * (2 * π * B) := by
  have hΛ : 0 ≤ Λ := (hψ0 0).trans (hψΛ 0)
  have hQc : ∀ t, Continuous fun θ => q t θ := fun t =>
    hq.comp (Continuous.prodMk continuous_const continuous_id)
  have hQ0 : ∀ t, 0 ≤ ∫ θ in (0 : ℝ)..2 * π, q t θ := fun t =>
    intervalIntegral.integral_nonneg (by positivity) fun θ _ => hq0 t θ
  have hHp : Continuous fun t => max (H t) 0 := hH.max continuous_const
  have step1 : ∫ t in (0 : ℝ)..T, H t ≤ ∫ t in (0 : ℝ)..T, max (H t) 0 :=
    intervalIntegral.integral_mono_on hT (hH.intervalIntegrable _ _) (hHp.intervalIntegrable _ _)
      fun t _ => le_max_left _ _
  have hRHS : 0 ≤ Λ * K * (2 * π * B) := by positivity
  refine step1.trans ?_
  rw [← ENNReal.ofReal_le_ofReal_iff hRHS, intervalIntegral.integral_of_le hT,
    ofReal_integral_eq_lintegral_ofReal (hHp.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (ae_of_all _ fun t => le_max_right _ _)]
  have hpt : ∀ t, ENNReal.ofReal (max (H t) 0) ≤
      ENNReal.ofReal (Λ * K) * ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (q t θ) := by
    intro t
    rw [← ofReal_integral_eq_lintegral_ofReal ((hQc t).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        (ae_of_all _ fun θ => hq0 t θ), ← intervalIntegral.integral_of_le (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (max_le ?_ (mul_nonneg (mul_nonneg hΛ hK) (hQ0 t)))
    calc H t ≤ ψ t * (K * ∫ θ in (0 : ℝ)..2 * π, q t θ) := hHle t
      _ ≤ Λ * (K * ∫ θ in (0 : ℝ)..2 * π, q t θ) :=
          mul_le_mul_of_nonneg_right (hψΛ t) (mul_nonneg hK (hQ0 t))
      _ = Λ * K * ∫ θ in (0 : ℝ)..2 * π, q t θ := by ring
  have hmeas : AEMeasurable (Function.uncurry fun t θ => ENNReal.ofReal (q t θ))
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (volume.restrict (Ioc (0 : ℝ) (2 * π)))) :=
    (ENNReal.measurable_ofReal.comp hq.measurable).aemeasurable
  calc ∫⁻ t in Ioc 0 T, ENNReal.ofReal (max (H t) 0)
      ≤ ∫⁻ t in Ioc 0 T, ENNReal.ofReal (Λ * K) * ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (q t θ) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (Λ * K) * ∫⁻ t in Ioc 0 T, ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (q t θ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Λ * K) * ∫⁻ θ in Ioc 0 (2 * π), ∫⁻ t in Ioc 0 T, ENNReal.ofReal (q t θ) := by
        rw [lintegral_lintegral_swap hmeas]
    _ ≤ ENNReal.ofReal (Λ * K) * ∫⁻ _ in Ioc 0 (2 * π), ENNReal.ofReal B :=
        mul_le_mul_right (lintegral_mono fun θ =>
          (lintegral_mono_set Ioc_subset_Icc_self).trans (hbound θ)) _
    _ = ENNReal.ofReal (Λ * K * (2 * π * B)) := by
        rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul hB,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end GaloisForLFunctions.HTGeometry
