import GaloisForLFunctions.HTGeometry.ClockGoursatSolution

/-!
# The Goursat solution, read pointwise

The solution of the characteristic ODE takes values in a space of functions. Evaluating at a second
null coordinate turns it into a function of two variables, and the two derivatives can then be read
off separately:

* differentiating in `ξ` gives the Volterra transform of the solution, because evaluation is a
  continuous linear map and therefore commutes with the derivative;
* differentiating that transform in `η` gives `K·u`, by the fundamental theorem of calculus.

Together these say `∂η ∂ξ u = K u` on the open rectangle: the Goursat solution satisfies the
characteristic equation pointwise.
-/

namespace GaloisForLFunctions.HTGeometry

open Set MeasureTheory

/-! ## The two differentiation steps -/

/-- **The Volterra transform differentiates to the integrand.** -/
theorem hasDerivAt_volterraFun {b b' : ℝ} {K U : ℝ → ℝ}
    (hK : Continuous K) (hU : Continuous U) {η : ℝ} (hη : η ∈ Ioo b b') :
    HasDerivAt (volterraFun K b b' U) (K η * U η) η := by
  have hf : Continuous fun t => K t * U t := hK.mul hU
  have hFTC : HasDerivAt (fun z : ℝ => ∫ t in b..z, K t * U t) (K η * U η) η :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable b η)
      (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt
  refine hFTC.congr_of_eventuallyEq ?_
  refine Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hη) ?_
  intro z hz
  rw [volterraFun, clampTo_of_mem (Ioo_subset_Icc_self hz)]

/-- **Evaluation commutes with the derivative**, being a continuous linear map. -/
theorem hasDerivWithinAt_bcf_eval {α : ℝ → BoundedContinuousFunction ℝ ℝ}
    {v : BoundedContinuousFunction ℝ ℝ} {s : Set ℝ} {ξ : ℝ}
    (h : HasDerivWithinAt α v s ξ) (η : ℝ) :
    HasDerivWithinAt (fun z => α z η) (v η) s ξ := by
  have h2 := (BoundedContinuousFunction.evalCLM ℝ η).hasFDerivAt.comp_hasDerivWithinAt ξ h
  exact h2

/-! ## The pointwise Goursat solution -/

/-- **The characteristic equation has a local solution, pointwise.** The `ξ`-derivative of `u` is
the Volterra transform of `u`, and that transform differentiates in `η` to `K·u`; together,
`∂η ∂ξ u = K u`. -/
theorem exists_goursat_pointwise (K : ℝ → ℝ → ℝ) (b b' c c' M : ℝ)
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) (hbb : b ≤ b') (hcc : c ≤ c') (hM0 : 0 ≤ M)
    (hM : ∀ ξ ∈ Icc c c', ∀ t ∈ Icc b b', |K ξ t| ≤ M) (ξ₀ : ℝ) :
    ∃ h : ℝ, 0 < h ∧ ∃ u : ℝ → ℝ → ℝ,
      (∀ η, u ξ₀ η = 1) ∧
      (∀ ξ, Continuous (u ξ)) ∧
      (∀ ξ ∈ Icc (ξ₀ - h) (ξ₀ + h), ∀ η : ℝ,
        HasDerivWithinAt (fun z => u z η)
          (volterraFun (K (clampTo c c' ξ)) b b' (u ξ) η) (Icc (ξ₀ - h) (ξ₀ + h)) ξ) ∧
      (∀ ξ : ℝ, ∀ η ∈ Ioo b b',
        HasDerivAt (volterraFun (K (clampTo c c' ξ)) b b' (u ξ))
          (K (clampTo c c' ξ) η * u ξ η) η) := by
  obtain ⟨h, hh, α, hα0, hαd⟩ := exists_goursat_solution K b b' c c' M hK hbb hcc hM0 hM ξ₀
  refine ⟨h, hh, fun ξ η => α ξ η, ?_, ?_, ?_, ?_⟩
  · intro η
    show α ξ₀ η = 1
    rw [hα0]
    rfl
  · intro ξ
    exact (α ξ).continuous
  · intro ξ hξ η
    exact hasDerivWithinAt_bcf_eval (hαd ξ hξ) η
  · intro ξ η hη
    exact hasDerivAt_volterraFun (continuous_kernel_slice hK _) (α ξ).continuous hη

end GaloisForLFunctions.HTGeometry
