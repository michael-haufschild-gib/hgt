import GaloisForLFunctions.HTGeometry.KleinGordonBandPotential

/-!
# The bands exhaust the potential

The inverse problem is well posed on each frequency band and ill posed without one. What makes the
band-restricted theory a theory *of the potential* rather than of a proxy is that the bands exhaust
it: as the cut-off grows the band compressions converge strongly to the operator itself.

The proof is the corpus's own strong-convergence criterion for Fourier multipliers — a family of
symbols converging pointwise under a uniform bound gives a strongly convergent family of multipliers
— applied to the indicator symbols, which converge pointwise to one because each frequency is
eventually below the cut-off. Two applications and a triangle inequality then move the limit past the
perturbation.

The consequence is that a perturbation is determined by its band compressions: what is recovered on
wider and wider bands converges to the potential, and two potentials with the same compressions on
every band are equal.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] in
theorem norm_one_le_one (_ : E) : ‖(1 : ℂ)‖ ≤ 1 := by simp

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Each frequency is eventually below the cut-off. -/
theorem tendsto_kgLowPass (ξ : E) :
    Tendsto (fun R : ℝ => kgLowPass R ξ) atTop (𝓝 (1 : ℂ)) := by
  refine tendsto_const_nhds.congr' ?_
  refine (eventually_atTop.mpr ⟨‖ξ‖, fun R hR => ?_⟩)
  show (1 : ℂ) = kgLowPass R ξ
  rw [kgLowPass, if_pos hR]

/-- **The low-pass projections converge strongly to the identity.** -/
theorem tendsto_kgLowPassOp_apply (x : Lp ℂ 2 (volume : Measure E)) :
    Tendsto (fun R : ℝ => kgLowPassOp R x) atTop (𝓝 x) := by
  have hid : fourierMulCLM (E := E) (measurable_const (a := (1 : ℂ))) zero_le_one
      (norm_one_le_one (E := E)) = ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure E)) :=
    fourierMulCLM_eq_id _ _ _ (Filter.Eventually.of_forall fun _ => rfl)
  have hlim := tendsto_fourierMulCLM_apply (l := (atTop : Filter ℝ))
    (fun R => measurable_kgLowPass (E := E) R) (measurable_const (a := (1 : ℂ)))
    zero_le_one (fun R => norm_kgLowPass_le (E := E) R) (norm_one_le_one (E := E))
    (fun ξ => tendsto_kgLowPass ξ) x
  rw [hid] at hlim
  exact hlim

section Band

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}

/-- **The band compressions converge strongly to the perturbation.** -/
theorem tendsto_kgBandOp_apply (x : Lp ℂ 2 (volume : Measure E)) :
    Tendsto (fun R : ℝ => kgBandOp W₀ R x) atTop (𝓝 (W₀ x)) := by
  have hP := tendsto_kgLowPassOp_apply (E := E) x
  have hWP : Tendsto (fun R : ℝ => W₀ (kgLowPassOp R x)) atTop (𝓝 (W₀ x)) :=
    ((W₀.continuous.tendsto x).comp hP).congr fun R => rfl
  have hPW := tendsto_kgLowPassOp_apply (E := E) (W₀ x)
  refine (tendsto_iff_norm_sub_tendsto_zero).mpr ?_
  have hbd : ∀ R : ℝ, ‖kgBandOp W₀ R x - W₀ x‖
      ≤ ‖W₀ (kgLowPassOp R x) - W₀ x‖ + ‖kgLowPassOp R (W₀ x) - W₀ x‖ := by
    intro R
    have hsplit : kgBandOp W₀ R x - W₀ x
        = kgLowPassOp R (W₀ (kgLowPassOp R x) - W₀ x) + (kgLowPassOp R (W₀ x) - W₀ x) := by
      rw [map_sub, kgBandOp_apply]
      abel
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_kgLowPassOp_apply_le R _
  have h1 : Tendsto (fun R : ℝ => ‖W₀ (kgLowPassOp R x) - W₀ x‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).mp hWP
  have h2 : Tendsto (fun R : ℝ => ‖kgLowPassOp R (W₀ x) - W₀ x‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).mp hPW
  have hsum : Tendsto (fun R : ℝ => ‖W₀ (kgLowPassOp R x) - W₀ x‖
      + ‖kgLowPassOp R (W₀ x) - W₀ x‖) atTop (𝓝 0) := by
    simpa using h1.add h2
  exact squeeze_zero (fun _ => norm_nonneg _) hbd hsum

end Band

/-- **A perturbation is determined by its band compressions.** -/
theorem eq_of_kgBandOp_eq {W₁ W₂ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}
    (heq : ∀ R : ℝ, kgBandOp W₁ R = kgBandOp W₂ R) : W₁ = W₂ := by
  refine ContinuousLinearMap.ext fun x => ?_
  have h1 := tendsto_kgBandOp_apply (W₀ := W₁) x
  have h2 := tendsto_kgBandOp_apply (W₀ := W₂) x
  have hfun : (fun R : ℝ => kgBandOp W₁ R x) = fun R : ℝ => kgBandOp W₂ R x := by
    funext R
    rw [heq R]
  rw [hfun] at h1
  exact tendsto_nhds_unique h1 h2

end GaloisForLFunctions.HTGeometry
