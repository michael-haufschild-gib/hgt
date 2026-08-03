import GaloisForLFunctions.HTGeometry.ClockGoursatContinuity

/-!
# The Goursat solution satisfies its integral equation

The solution of the characteristic ODE is characterised by an integral identity: its `ξ`-derivative
is the Volterra transform of the solution, so integrating along the characteristic parameter gives

`u(ξ,η) = 1 + ∫_{ξ₀}^{ξ} (∫_b^η K(τ,t) u(τ,t) dt) dτ`.

Recovering that identity needs the integrand to be continuous in `τ`, which follows from the joint
continuity of the previous file together with the continuity of a parametric interval integral.
The identity is the object on which the Fubini exchange acts to produce the second mixed derivative.
-/

namespace GaloisForLFunctions.HTGeometry

open Set MeasureTheory

/-- **The Volterra transform of a jointly continuous family is continuous in the parameter.** -/
theorem continuous_volterraFun_param {K : ℝ → ℝ → ℝ}
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) {v : ℝ → ℝ → ℝ}
    (hv : Continuous fun p : ℝ × ℝ => v p.1 p.2) (b b' c c' η : ℝ) :
    Continuous fun τ => volterraFun (K (clampTo c c' τ)) b b' (v τ) η := by
  have hker : Continuous fun p : ℝ × ℝ => K (clampTo c c' p.1) p.2 :=
    hK.comp (((continuous_clampTo c c').comp continuous_fst).prodMk continuous_snd)
  have huncurry : Continuous
      (Function.uncurry fun τ t => K (clampTo c c' τ) t * v τ t) := hker.mul hv
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous huncurry
    continuous_const

/-- **The Goursat solution satisfies its integral equation.** -/
theorem exists_goursat_integral_form (K : ℝ → ℝ → ℝ) (b b' c c' M : ℝ)
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) (hbb : b ≤ b') (hcc : c ≤ c') (hM0 : 0 ≤ M)
    (hM : ∀ ξ ∈ Icc c c', ∀ t ∈ Icc b b', |K ξ t| ≤ M) (ξ₀ : ℝ) :
    ∃ h : ℝ, 0 < h ∧ ∃ u : ℝ → ℝ → ℝ,
      (∀ η, u ξ₀ η = 1) ∧
      (∀ ξ, Continuous (u ξ)) ∧
      ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2)
        (Icc (ξ₀ - h) (ξ₀ + h) ×ˢ (univ : Set ℝ)) ∧
      (∀ ξ ∈ Icc (ξ₀ - h) (ξ₀ + h), ∀ η : ℝ,
        HasDerivWithinAt (fun z => u z η)
          (volterraFun (K (clampTo c c' ξ)) b b' (u ξ) η) (Icc (ξ₀ - h) (ξ₀ + h)) ξ) ∧
      (∀ ξ ∈ Ioo (ξ₀ - h) (ξ₀ + h), ∀ η : ℝ,
        u ξ η = 1 + ∫ τ in ξ₀..ξ, volterraFun (K (clampTo c c' τ)) b b' (u τ) η) ∧
      (∀ ξ : ℝ, ∀ η ∈ Ioo b b',
        HasDerivAt (volterraFun (K (clampTo c c' ξ)) b b' (u ξ))
          (K (clampTo c c' ξ) η * u ξ η) η) := by
  obtain ⟨h, hh, u, hu0, huc, hujoint, hud, huη⟩ :=
    exists_goursat_jointly_continuous K b b' c c' M hK hbb hcc hM0 hM ξ₀
  refine ⟨h, hh, u, hu0, huc, hujoint, hud, ?_, huη⟩
  -- the clamped solution is globally jointly continuous
  have hclampmem : ∀ τ : ℝ, clampTo (ξ₀ - h) (ξ₀ + h) τ ∈ Icc (ξ₀ - h) (ξ₀ + h) :=
    clampTo_mem (by linarith)
  have hbar : Continuous fun p : ℝ × ℝ => u (clampTo (ξ₀ - h) (ξ₀ + h) p.1) p.2 := by
    refine hujoint.comp_continuous
      (((continuous_clampTo (ξ₀ - h) (ξ₀ + h)).comp continuous_fst).prodMk continuous_snd) ?_
    intro p
    exact ⟨hclampmem p.1, mem_univ p.2⟩
  intro ξ hξ η
  -- continuity of the integrand along the characteristic parameter
  have hVbar := continuous_volterraFun_param hK
    (v := fun τ => u (clampTo (ξ₀ - h) (ξ₀ + h) τ)) hbar b b' c c' η
  have hVon : ContinuousOn
      (fun τ => volterraFun (K (clampTo c c' τ)) b b' (u τ) η) (Icc (ξ₀ - h) (ξ₀ + h)) := by
    refine hVbar.continuousOn.congr ?_
    intro τ hτ
    show volterraFun (K (clampTo c c' τ)) b b' (u τ) η
      = volterraFun (K (clampTo c c' τ)) b b' (u (clampTo (ξ₀ - h) (ξ₀ + h) τ)) η
    rw [clampTo_of_mem hτ]
  -- the derivative holds on the open interval
  have hsub : uIcc ξ₀ ξ ⊆ Ioo (ξ₀ - h) (ξ₀ + h) := by
    intro z hz
    rcases Set.mem_uIcc.mp hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith, by linarith [hξ.2]⟩
    · exact ⟨by linarith [hξ.1], by linarith⟩
  have hderiv : ∀ x ∈ uIcc ξ₀ ξ,
      HasDerivAt (fun z => u z η) (volterraFun (K (clampTo c c' x)) b b' (u x) η) x := by
    intro x hx
    have hxo := hsub hx
    refine (hud x ⟨le_of_lt hxo.1, le_of_lt hxo.2⟩ η).hasDerivAt ?_
    exact Icc_mem_nhds hxo.1 hxo.2
  have hint : IntervalIntegrable
      (fun τ => volterraFun (K (clampTo c c' τ)) b b' (u τ) η) volume ξ₀ ξ := by
    exact (hVon.mono (hsub.trans Ioo_subset_Icc_self)).intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hu0 η] at hFTC
  linarith [hFTC]

end GaloisForLFunctions.HTGeometry
