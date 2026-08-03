import GaloisForLFunctions.HTGeometry.ClockGoursatGlobal

/-!
# Both mixed derivatives of the Goursat solution

Exchanging the order of integration in the Goursat identity

`u(ξ,η) = 1 + ∫_{ξ₀}^{ξ} ∫_b^η K(τ,t) u(τ,t) dt dτ = 1 + ∫_b^η ∫_{ξ₀}^{ξ} K(τ,t) u(τ,t) dτ dt`

exhibits `u` as a primitive in `η` as well as in `ξ`. The fundamental theorem of calculus then gives

`∂η u(ξ,η) = ∫_{ξ₀}^{ξ} K(τ,η) u(τ,η) dτ`,  and differentiating that in `ξ` gives `K(ξ,η)u(ξ,η)`.

So both mixed second derivatives of the Goursat solution exist and both equal `K·u`, which is what
the chart d'Alembertian of the two-dimensional clock equation requires.
-/

namespace GaloisForLFunctions.HTGeometry

open Set MeasureTheory

/-- **The Goursat solution has both mixed second derivatives, and both equal `K·u`.** -/
theorem exists_goursat_mixed (K : ℝ → ℝ → ℝ) (b b' c c' M : ℝ)
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) (hbb : b ≤ b') (hcc : c ≤ c') (hM0 : 0 ≤ M)
    (hM : ∀ ξ ∈ Icc c c', ∀ t ∈ Icc b b', |K ξ t| ≤ M) (ξ₀ : ℝ) :
    ∃ h : ℝ, 0 < h ∧ ∃ u : ℝ → ℝ → ℝ,
      (∀ η, u ξ₀ η = 1) ∧
      Continuous (fun p : ℝ × ℝ => u p.1 p.2) ∧
      (∀ ξ ∈ Ioo (ξ₀ - h) (ξ₀ + h), ∀ η : ℝ,
        HasDerivAt (fun z => u z η)
          (volterraFun (K (clampTo c c' ξ)) b b' (u ξ) η) ξ) ∧
      (∀ ξ : ℝ, ∀ η ∈ Ioo b b',
        HasDerivAt (volterraFun (K (clampTo c c' ξ)) b b' (u ξ))
          (K (clampTo c c' ξ) η * u ξ η) η) ∧
      (∀ ξ ∈ Ioo (ξ₀ - h) (ξ₀ + h), ∀ η ∈ Ioo b b',
        HasDerivAt (fun z => u ξ z) (∫ τ in ξ₀..ξ, K (clampTo c c' τ) η * u τ η) η) ∧
      (∀ ξ η : ℝ,
        HasDerivAt (fun z => ∫ τ in ξ₀..z, K (clampTo c c' τ) η * u τ η)
          (K (clampTo c c' ξ) η * u ξ η) ξ) := by
  obtain ⟨h, hh, u, hu0, hujoint, hud, hform, huη⟩ :=
    exists_goursat_global K b b' c c' M hK hbb hcc hM0 hM ξ₀
  -- the integrand is jointly continuous
  have hker : Continuous fun p : ℝ × ℝ => K (clampTo c c' p.1) p.2 :=
    hK.comp (((continuous_clampTo c c').comp continuous_fst).prodMk continuous_snd)
  have hF : Continuous fun p : ℝ × ℝ => K (clampTo c c' p.1) p.2 * u p.1 p.2 :=
    hker.mul hujoint
  have hFswap : Continuous fun p : ℝ × ℝ => K (clampTo c c' p.2) p.1 * u p.2 p.1 :=
    hF.comp continuous_swap
  -- the inner integral along the characteristic parameter
  have hGcont : ∀ ξ : ℝ, Continuous fun t => ∫ τ in ξ₀..ξ, K (clampTo c c' τ) t * u τ t := by
    intro ξ
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun t τ => K (clampTo c c' τ) t * u τ t) hFswap continuous_const
  have hgcont : ∀ η : ℝ, Continuous fun τ => K (clampTo c c' τ) η * u τ η := by
    intro η
    exact hF.comp (continuous_id.prodMk continuous_const)
  refine ⟨h, hh, u, hu0, hujoint, hud, huη, ?_, ?_⟩
  · -- the eta derivative, by Fubini and the fundamental theorem of calculus
    intro ξ hξ η hη
    have hswap : ∀ z : ℝ,
        (∫ τ in ξ₀..ξ, volterraFun (K (clampTo c c' τ)) b b' (u τ) z)
          = ∫ t in b..clampTo b b' z, ∫ τ in ξ₀..ξ, K (clampTo c c' τ) t * u τ t := by
      intro z
      exact intervalIntegral_swap_of_continuous hF ξ₀ ξ b (clampTo b b' z)
    have hprim : HasDerivAt
        (fun z => 1 + ∫ t in b..z, ∫ τ in ξ₀..ξ, K (clampTo c c' τ) t * u τ t)
        (∫ τ in ξ₀..ξ, K (clampTo c c' τ) η * u τ η) η := by
      refine HasDerivAt.const_add 1 ?_
      exact intervalIntegral.integral_hasDerivAt_right
        ((hGcont ξ).intervalIntegrable b η)
        ((hGcont ξ).stronglyMeasurableAtFilter _ _) (hGcont ξ).continuousAt
    refine hprim.congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hη) ?_
    intro z hz
    show u ξ z = 1 + ∫ t in b..z, ∫ τ in ξ₀..ξ, K (clampTo c c' τ) t * u τ t
    rw [hform ξ hξ z, hswap z, clampTo_of_mem (Ioo_subset_Icc_self hz)]
  · -- the xi derivative of the eta derivative
    intro ξ η
    exact intervalIntegral.integral_hasDerivAt_right
      ((hgcont η).intervalIntegrable ξ₀ ξ)
      ((hgcont η).stronglyMeasurableAtFilter _ _) (hgcont η).continuousAt

end GaloisForLFunctions.HTGeometry
