import Mathlib.MeasureTheory.Integral.Prod
import GaloisForLFunctions.HTGeometry.ClockGoursatIntegralForm

/-!
# Fubini for continuous integrands, and the Goursat solution in global form

Two preparations for the second mixed derivative.

The first is a convenience form of Fubini: for a jointly continuous integrand the exchange of two
interval integrals needs no integrability side condition, because a continuous function is
integrable on the compact rectangle that contains the region of integration.

The second repackages the Goursat solution so that it is **globally** jointly continuous, by
clamping the characteristic parameter to the interval on which the solution is defined. All the
differential statements are local anyway, so nothing is lost, and every integrability condition
downstream becomes automatic.
-/

namespace GaloisForLFunctions.HTGeometry

open Set MeasureTheory

/-! ## Fubini for a continuous integrand -/

theorem integrableOn_uncurry_of_continuous {F : ℝ → ℝ → ℝ}
    (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2) (a b c d : ℝ) :
    IntegrableOn (Function.uncurry F) (uIoc a b ×ˢ uIoc c d) := by
  have hcomp : IsCompact ((uIcc a b) ×ˢ (uIcc c d)) := isCompact_uIcc.prod isCompact_uIcc
  have h1 : IntegrableOn (Function.uncurry F) ((uIcc a b) ×ˢ (uIcc c d)) :=
    hF.continuousOn.integrableOn_compact hcomp
  exact h1.mono_set (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)

/-- **Fubini for interval integrals of a continuous integrand.** -/
theorem intervalIntegral_swap_of_continuous {F : ℝ → ℝ → ℝ}
    (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2) (a b c d : ℝ) :
    ∫ x in a..b, ∫ y in c..d, F x y = ∫ y in c..d, ∫ x in a..b, F x y :=
  intervalIntegral_intervalIntegral_swap (integrableOn_uncurry_of_continuous hF a b c d)

/-! ## The Goursat solution in global form -/

/-- **The Goursat solution, globally jointly continuous.** Clamping the characteristic parameter
loses nothing, since every differential statement is local. -/
theorem exists_goursat_global (K : ℝ → ℝ → ℝ) (b b' c c' M : ℝ)
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) (hbb : b ≤ b') (hcc : c ≤ c') (hM0 : 0 ≤ M)
    (hM : ∀ ξ ∈ Icc c c', ∀ t ∈ Icc b b', |K ξ t| ≤ M) (ξ₀ : ℝ) :
    ∃ h : ℝ, 0 < h ∧ ∃ u : ℝ → ℝ → ℝ,
      (∀ η, u ξ₀ η = 1) ∧
      Continuous (fun p : ℝ × ℝ => u p.1 p.2) ∧
      (∀ ξ ∈ Ioo (ξ₀ - h) (ξ₀ + h), ∀ η : ℝ,
        HasDerivAt (fun z => u z η)
          (volterraFun (K (clampTo c c' ξ)) b b' (u ξ) η) ξ) ∧
      (∀ ξ ∈ Ioo (ξ₀ - h) (ξ₀ + h), ∀ η : ℝ,
        u ξ η = 1 + ∫ τ in ξ₀..ξ, volterraFun (K (clampTo c c' τ)) b b' (u τ) η) ∧
      (∀ ξ : ℝ, ∀ η ∈ Ioo b b',
        HasDerivAt (volterraFun (K (clampTo c c' ξ)) b b' (u ξ))
          (K (clampTo c c' ξ) η * u ξ η) η) := by
  obtain ⟨h, hh, u, hu0, huc, hujoint, hud, hform, huη⟩ :=
    exists_goursat_integral_form K b b' c c' M hK hbb hcc hM0 hM ξ₀
  have hJ : (ξ₀ - h) ≤ (ξ₀ + h) := by linarith
  have hclampmem : ∀ τ : ℝ, clampTo (ξ₀ - h) (ξ₀ + h) τ ∈ Icc (ξ₀ - h) (ξ₀ + h) :=
    clampTo_mem hJ
  refine ⟨h, hh, fun τ => u (clampTo (ξ₀ - h) (ξ₀ + h) τ), ?_, ?_, ?_, ?_, ?_⟩
  · intro η
    have h₀ : clampTo (ξ₀ - h) (ξ₀ + h) ξ₀ = ξ₀ :=
      clampTo_of_mem ⟨by linarith, by linarith⟩
    show u (clampTo (ξ₀ - h) (ξ₀ + h) ξ₀) η = 1
    rw [h₀]
    exact hu0 η
  · refine hujoint.comp_continuous
      (((continuous_clampTo (ξ₀ - h) (ξ₀ + h)).comp continuous_fst).prodMk continuous_snd) ?_
    intro p
    exact ⟨hclampmem p.1, mem_univ p.2⟩
  · intro ξ hξ η
    have heq : ∀ z ∈ Ioo (ξ₀ - h) (ξ₀ + h),
        u (clampTo (ξ₀ - h) (ξ₀ + h) z) η = u z η := by
      intro z hz
      rw [clampTo_of_mem (Ioo_subset_Icc_self hz)]
    have hclampξ : clampTo (ξ₀ - h) (ξ₀ + h) ξ = ξ :=
      clampTo_of_mem (Ioo_subset_Icc_self hξ)
    have hbase : HasDerivAt (fun z => u z η)
        (volterraFun (K (clampTo c c' ξ)) b b' (u ξ) η) ξ :=
      (hud ξ (Ioo_subset_Icc_self hξ) η).hasDerivAt (Icc_mem_nhds hξ.1 hξ.2)
    have hcong : (fun z => u (clampTo (ξ₀ - h) (ξ₀ + h) z) η) =ᶠ[nhds ξ]
        fun z => u z η :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hξ) heq
    show HasDerivAt (fun z => u (clampTo (ξ₀ - h) (ξ₀ + h) z) η)
      (volterraFun (K (clampTo c c' ξ)) b b' (u (clampTo (ξ₀ - h) (ξ₀ + h) ξ)) η) ξ
    rw [hclampξ]
    exact hbase.congr_of_eventuallyEq hcong
  · intro ξ hξ η
    have hclampξ : clampTo (ξ₀ - h) (ξ₀ + h) ξ = ξ :=
      clampTo_of_mem (Ioo_subset_Icc_self hξ)
    show u (clampTo (ξ₀ - h) (ξ₀ + h) ξ) η
      = 1 + ∫ τ in ξ₀..ξ, volterraFun (K (clampTo c c' τ)) b b'
          (u (clampTo (ξ₀ - h) (ξ₀ + h) τ)) η
    rw [hclampξ, hform ξ hξ η]
    congr 1
    refine intervalIntegral.integral_congr ?_
    intro τ hτ
    have hτJ : τ ∈ Icc (ξ₀ - h) (ξ₀ + h) := by
      rcases Set.mem_uIcc.mp hτ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith, by linarith [hξ.2]⟩
      · exact ⟨by linarith [hξ.1], by linarith⟩
    show volterraFun (K (clampTo c c' τ)) b b' (u τ) η
      = volterraFun (K (clampTo c c' τ)) b b' (u (clampTo (ξ₀ - h) (ξ₀ + h) τ)) η
    rw [clampTo_of_mem hτJ]
  · intro ξ η hη
    exact hasDerivAt_volterraFun (continuous_kernel_slice hK _)
      (huc (clampTo (ξ₀ - h) (ξ₀ + h) ξ)) hη

end GaloisForLFunctions.HTGeometry
