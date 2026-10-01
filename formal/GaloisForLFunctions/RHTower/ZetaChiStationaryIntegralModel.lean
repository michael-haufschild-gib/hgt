import GaloisForLFunctions.RHTower.ZetaChiStationaryQuadraticModel

open Complex MeasureTheory Set
noncomputable section
namespace RHTower

/-- Replacing actual chi by its common conductor model costs at most 78
on every comparable-height subinterval, uniformly in its real saddle. -/
theorem exists_zetaChi_stationary_integral_model :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ a l u : ℝ, 8 ≤ a → a / 2 ≤ l → l ≤ u → u ≤ 2 * a →
      ‖∫ t in l..u,
        zetaChi (linePt t) * bourgainOscillation (t * Real.log (a / (2 * Real.pi))) -
          κ * bourgainOscillation (t - t * Real.log (t / a))‖ ≤ 78 := by
  obtain ⟨κ, hκ, hglobal, _⟩ := exists_zetaChi_stationary_phase_models
  refine ⟨κ, hκ, ?_⟩
  intro a l u ha hl hlu hu
  have ha0 : 0 < a := by linarith
  have hbound : ∀ t ∈ Set.uIoc l u,
      ‖zetaChi (linePt t) * bourgainOscillation (t * Real.log (a / (2 * Real.pi))) -
        κ * bourgainOscillation (t - t * Real.log (t / a))‖ ≤ 52 / a := by
    intro t ht
    rw [Set.uIoc_of_le hlu] at ht
    have ht4 : 4 ≤ t := by linarith [ht.1]
    have ht0 : 0 < t := by linarith
    apply (hglobal a ha0 t ht4).trans
    rw [div_le_div_iff₀ ht0 ha0]
    linarith [ht.1]
  apply (intervalIntegral.norm_integral_le_of_norm_le_const hbound).trans
  rw [abs_of_nonneg (sub_nonneg.mpr hlu)]
  have he : 52 / a * (u - l) = (52 * (u - l)) / a := by ring
  rw [he, div_le_iff₀ ha0]
  linarith

end RHTower
