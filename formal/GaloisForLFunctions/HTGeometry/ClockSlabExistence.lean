import GaloisForLFunctions.HTGeometry.ClockSlabProbe
import GaloisForLFunctions.HTGeometry.ClockTwoDimensionalProbe

/-!
# Existence of clock probes on a null slab, in every dimension

Assembling the Goursat solution with the slab reduction: on Minkowski space of any dimension
`n + 2`, a continuously differentiable potential depending only on the two null coordinates
`x⁰ ± x¹` admits a clock probe on an open neighbourhood of any prescribed event, nonvanishing there
and normalised to `1` at the event. Hence such a potential is determined by its probes.

The transverse dimensions cost nothing: the same bivariate solution serves in every dimension, and
the only thing that changes is which chart d'Alembertian is being reduced.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

/-- **Clock probes for slab potentials in every dimension.** -/
theorem exists_clockProbe_on_slab {v : ℝ → ℝ → ℝ}
    (hv : ContDiff ℝ 1 fun p : ℝ × ℝ => v p.1 p.2) (n : ℕ) (x : Fin (n + 2) → ℝ) :
    ∃ W : Set (Fin (n + 2) → ℝ), IsOpen W ∧ x ∈ W ∧ ∃ U : (Fin (n + 2) → ℝ) → ℝ,
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
          (slabLift v n) U W ∧
        (∀ y ∈ W, U y ≠ 0) ∧ U x = 1 := by
  classical
  set F : ℝ × ℝ → ℝ := fun p => v p.1 p.2 / 4 with hF_def
  have hFC : ContDiff ℝ 1 F := hv.div_const 4
  set ξ₀ : ℝ := x 0 + x 1 with hξ₀
  set η₀ : ℝ := x 0 - x 1 with hη₀
  set c : ℝ := ξ₀ - 1 with hc
  set c' : ℝ := ξ₀ + 1 with hc'
  set b : ℝ := η₀ - 1 with hb
  set b' : ℝ := η₀ + 1 with hb'
  have hcc : c ≤ c' := by rw [hc, hc']; linarith
  have hbb : b ≤ b' := by rw [hb, hb']; linarith
  obtain ⟨M, hMbound⟩ := ((isCompact_Icc (a := c) (b := c')).prod
    (isCompact_Icc (a := b) (b := b'))).exists_bound_of_continuousOn hFC.continuous.continuousOn
  have hM0 : 0 ≤ M :=
    le_trans (norm_nonneg (F (c, b))) (hMbound (c, b) ⟨⟨le_rfl, hcc⟩, ⟨le_rfl, hbb⟩⟩)
  have hM : ∀ ξ ∈ Icc c c', ∀ t ∈ Icc b b', |F (ξ, t)| ≤ M := by
    intro ξ hξ t ht
    have := hMbound (ξ, t) ⟨hξ, ht⟩
    rwa [Real.norm_eq_abs] at this
  obtain ⟨h, hh, u, A, B, Aa, Ab, Ba, Bb, hu0, hujoint, hC1u, hC1A, hC1B, hAbeq, hBaeq⟩ :=
    exists_goursat_C2 (fun ξ η => F (ξ, η)) (planarFst F) (planarSnd F) b b' c c' M
      hFC.continuous (continuous_planarFst hFC) (continuous_planarSnd hFC)
      (hasDerivAt_planarFst hFC) (hasDerivAt_planarSnd hFC) hbb hcc hM0 hM ξ₀
  have hΩopen : IsOpen ((Ioo (ξ₀ - h) (ξ₀ + h) ∩ Ioo c c') ×ˢ Ioo b b') :=
    (isOpen_Ioo.inter isOpen_Ioo).prod isOpen_Ioo
  have hmemΩ : slabCLM n x ∈ (Ioo (ξ₀ - h) (ξ₀ + h) ∩ Ioo c c') ×ˢ Ioo b b' := by
    rw [slabCLM_apply, ← hξ₀, ← hη₀]
    exact ⟨⟨⟨by linarith, by linarith⟩, by rw [hc, hc']; constructor <;> linarith⟩,
      by rw [hb, hb']; constructor <;> linarith⟩
  have hUcont : Continuous (slabLift u n) := hujoint.comp (slabCLM n).continuous
  have hU1 : slabLift u n x = 1 := by
    show u (x 0 + x 1) (x 0 - x 1) = 1
    rw [← hξ₀, ← hη₀]
    exact hu0 _
  have hxne : x ∈ {y : Fin (n + 2) → ℝ | slabLift u n y ≠ 0} := by
    show slabLift u n x ≠ 0
    rw [hU1]
    exact one_ne_zero
  refine ⟨slabBox ((Ioo (ξ₀ - h) (ξ₀ + h) ∩ Ioo c c') ×ˢ Ioo b b') n
      ∩ {y | slabLift u n y ≠ 0},
    (isOpen_slabBox hΩopen n).inter (isOpen_ne.preimage hUcont),
    ⟨hmemΩ, hxne⟩, slabLift u n, ?_, fun y hy => hy.2, hU1⟩
  intro y hy
  have hyΩ : slabCLM n y ∈ (Ioo (ξ₀ - h) (ξ₀ + h) ∩ Ioo c c') ×ˢ Ioo b b' := hy.1
  have hab := hAbeq (slabCLM n y) hyΩ
  have hba := hBaeq (slabCLM n y) hyΩ
  simp only [slabCLM_apply] at hab hba
  show (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
      (slabLift u n) y + slabLift v n y * slabLift u n y = 0
  rw [dalembert_slabLift hC1u hC1A hC1B hyΩ, hab, hba]
  show -2 * (F (y 0 + y 1, y 0 - y 1) * u (y 0 + y 1) (y 0 - y 1)
      + F (y 0 + y 1, y 0 - y 1) * u (y 0 + y 1) (y 0 - y 1))
      + v (y 0 + y 1) (y 0 - y 1) * u (y 0 + y 1) (y 0 - y 1) = 0
  rw [hF_def]
  ring

/-- **Slab potentials are determined by their probes, in every dimension.** -/
theorem slabPotential_eq_of_probes_on {v w : ℝ → ℝ → ℝ}
    (hv : ContDiff ℝ 1 fun p : ℝ × ℝ => v p.1 p.2) (n : ℕ)
    (hprobe : ∀ (U : (Fin (n + 2) → ℝ) → ℝ) (W : Set (Fin (n + 2) → ℝ)),
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
          (slabLift v n) U W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
          (slabLift w n) U W) :
    ∀ x : Fin (n + 2) → ℝ, w (x 0 + x 1) (x 0 - x 1) = v (x 0 + x 1) (x 0 - x 1) := by
  intro x
  obtain ⟨W, _, hxW, U, hUon, hUne, _⟩ := exists_clockProbe_on_slab hv n x
  exact potential_eqOn_of_solvesOn hUon (hprobe U W hUon) hUne hxW

end GaloisForLFunctions.HTGeometry
