import GaloisForLFunctions.HTGeometry.ClockGoursatRegularity
import GaloisForLFunctions.HTGeometry.ClockBivariateSecondOrder

/-!
# The Goursat solution as a twice continuously differentiable function

Everything the second-order chart calculus asks for is now available for the Goursat solution: the
two first derivatives, the two mixed derivatives, and — once the kernel is continuously
differentiable — the two pure second derivatives. This file collects them into the exact package
that calculus consumes, three `IsC1On` records on one open rectangle, together with the statement
that both mixed derivatives are `K·u`.

The rectangle is the intersection of the interval of existence with the region where the clamping
used to globalise the solution is invisible, times the interval on which the kernel bound was
assumed. On it every derivative statement of the construction is available simultaneously.
-/

namespace GaloisForLFunctions.HTGeometry

open Set MeasureTheory

/-- **The Goursat solution of a continuously differentiable kernel is twice continuously
differentiable.** -/
theorem exists_goursat_C2 (K Ka Kb : ℝ → ℝ → ℝ) (b b' c c' M : ℝ)
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (hKa : Continuous fun p : ℝ × ℝ => Ka p.1 p.2)
    (hKb : Continuous fun p : ℝ × ℝ => Kb p.1 p.2)
    (hKda : ∀ ξ t : ℝ, HasDerivAt (fun w => K w t) (Ka ξ t) ξ)
    (hKdb : ∀ ξ t : ℝ, HasDerivAt (fun w => K ξ w) (Kb ξ t) t)
    (hbb : b ≤ b') (hcc : c ≤ c') (hM0 : 0 ≤ M)
    (hM : ∀ ξ ∈ Icc c c', ∀ t ∈ Icc b b', |K ξ t| ≤ M) (ξ₀ : ℝ) :
    ∃ h : ℝ, 0 < h ∧ ∃ u A B Aa Ab Ba Bb : ℝ → ℝ → ℝ,
      (∀ η, u ξ₀ η = 1) ∧
      Continuous (fun p : ℝ × ℝ => u p.1 p.2) ∧
      IsC1On u A B ((Ioo (ξ₀ - h) (ξ₀ + h) ∩ Ioo c c') ×ˢ Ioo b b') ∧
      IsC1On A Aa Ab ((Ioo (ξ₀ - h) (ξ₀ + h) ∩ Ioo c c') ×ˢ Ioo b b') ∧
      IsC1On B Ba Bb ((Ioo (ξ₀ - h) (ξ₀ + h) ∩ Ioo c c') ×ˢ Ioo b b') ∧
      (∀ p ∈ (Ioo (ξ₀ - h) (ξ₀ + h) ∩ Ioo c c') ×ˢ Ioo b b',
        Ab p.1 p.2 = K p.1 p.2 * u p.1 p.2) ∧
      (∀ p ∈ (Ioo (ξ₀ - h) (ξ₀ + h) ∩ Ioo c c') ×ˢ Ioo b b',
        Ba p.1 p.2 = K p.1 p.2 * u p.1 p.2) := by
  classical
  obtain ⟨h, hh, u, hu0, hujoint, hud, huηderiv, huη, hmix⟩ :=
    exists_goursat_mixed K b b' c c' M hK hbb hcc hM0 hM ξ₀
  set s : Set ℝ := Ioo (ξ₀ - h) (ξ₀ + h) ∩ Ioo c c' with hs_def
  set Ω : Set (ℝ × ℝ) := s ×ˢ Ioo b b' with hΩ_def
  have hs_open : IsOpen s := isOpen_Ioo.inter isOpen_Ioo
  have hΩ_open : IsOpen Ω := hs_open.prod isOpen_Ioo
  have hs_h : s ⊆ Ioo (ξ₀ - h) (ξ₀ + h) := inter_subset_left
  have hs_c : s ⊆ Ioo c c' := inter_subset_right
  -- the continuous building blocks
  have hclamp : Continuous (clampTo c c') := continuous_clampTo c c'
  have hker : Continuous fun p : ℝ × ℝ => K (clampTo c c' p.1) p.2 :=
    hK.comp ((hclamp.comp continuous_fst).prodMk continuous_snd)
  have hkera : Continuous fun p : ℝ × ℝ => Ka (clampTo c c' p.1) p.2 :=
    hKa.comp ((hclamp.comp continuous_fst).prodMk continuous_snd)
  have hAcont : Continuous fun p : ℝ × ℝ => volterraFun (K (clampTo c c' p.1)) b b' (u p.1) p.2 :=
    continuous_goursatXiDeriv hK hujoint b b' c c'
  have hBcont : Continuous fun p : ℝ × ℝ => ∫ τ in ξ₀..p.1, K (clampTo c c' τ) p.2 * u τ p.2 :=
    continuous_goursatEtaDeriv hK hujoint c c' ξ₀
  have hAbcont : Continuous fun p : ℝ × ℝ => K (clampTo c c' p.1) p.2 * u p.1 p.2 :=
    hker.mul hujoint
  -- continuity of the two pure second derivatives
  have hAacont : Continuous fun p : ℝ × ℝ => ∫ t in b..clampTo b b' p.2,
      Ka (clampTo c c' p.1) t * u p.1 t
        + K (clampTo c c' p.1) t * volterraFun (K (clampTo c c' p.1)) b b' (u p.1) t := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun p : ℝ × ℝ => fun t => Ka (clampTo c c' p.1) t * u p.1 t
        + K (clampTo c c' p.1) t * volterraFun (K (clampTo c c' p.1)) b b' (u p.1) t)
      ?_ ((continuous_clampTo b b').comp continuous_snd)
    have h1 : Continuous fun q : (ℝ × ℝ) × ℝ => Ka (clampTo c c' q.1.1) q.2 :=
      hkera.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    have h2 : Continuous fun q : (ℝ × ℝ) × ℝ => u q.1.1 q.2 :=
      hujoint.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    have h3 : Continuous fun q : (ℝ × ℝ) × ℝ => K (clampTo c c' q.1.1) q.2 :=
      hker.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    have h4 : Continuous fun q : (ℝ × ℝ) × ℝ =>
        volterraFun (K (clampTo c c' q.1.1)) b b' (u q.1.1) q.2 :=
      hAcont.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    exact (h1.mul h2).add (h3.mul h4)
  have hBbcont : Continuous fun p : ℝ × ℝ => ∫ τ in ξ₀..p.1,
      Kb (clampTo c c' τ) p.2 * u τ p.2
        + K (clampTo c c' τ) p.2 * ∫ σ in ξ₀..τ, K (clampTo c c' σ) p.2 * u σ p.2 := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun p : ℝ × ℝ => fun τ => Kb (clampTo c c' τ) p.2 * u τ p.2
        + K (clampTo c c' τ) p.2 * ∫ σ in ξ₀..τ, K (clampTo c c' σ) p.2 * u σ p.2)
      ?_ continuous_fst
    have h1 : Continuous fun q : (ℝ × ℝ) × ℝ => Kb (clampTo c c' q.2) q.1.2 :=
      hKb.comp ((hclamp.comp continuous_snd).prodMk (continuous_snd.comp continuous_fst))
    have h2 : Continuous fun q : (ℝ × ℝ) × ℝ => u q.2 q.1.2 :=
      hujoint.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
    have h3 : Continuous fun q : (ℝ × ℝ) × ℝ => K (clampTo c c' q.2) q.1.2 :=
      hK.comp ((hclamp.comp continuous_snd).prodMk (continuous_snd.comp continuous_fst))
    have h4 : Continuous fun q : (ℝ × ℝ) × ℝ =>
        ∫ σ in ξ₀..q.2, K (clampTo c c' σ) q.1.2 * u σ q.1.2 :=
      hBcont.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
    exact (h1.mul h2).add (h3.mul h4)
  refine ⟨h, hh, u,
    fun ξ η => volterraFun (K (clampTo c c' ξ)) b b' (u ξ) η,
    fun ξ η => ∫ τ in ξ₀..ξ, K (clampTo c c' τ) η * u τ η,
    fun ξ η => ∫ t in b..clampTo b b' η,
      Ka (clampTo c c' ξ) t * u ξ t
        + K (clampTo c c' ξ) t * volterraFun (K (clampTo c c' ξ)) b b' (u ξ) t,
    fun ξ η => K (clampTo c c' ξ) η * u ξ η,
    fun ξ η => K (clampTo c c' ξ) η * u ξ η,
    fun ξ η => ∫ τ in ξ₀..ξ,
      Kb (clampTo c c' τ) η * u τ η
        + K (clampTo c c' τ) η * ∫ σ in ξ₀..τ, K (clampTo c c' σ) η * u σ η,
    hu0, hujoint, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hΩ_open, fun p hp => hud p.1 (hs_h hp.1) p.2,
      fun p hp => huη p.1 (hs_h hp.1) p.2 hp.2, hAcont, hBcont⟩
  · refine ⟨hΩ_open, fun p hp => ?_, fun p hp => huηderiv p.1 p.2 hp.2, hAacont, hAbcont⟩
    exact hasDerivAt_goursat_xi_second hK hKa hKda hujoint hs_open hs_c hs_h hud hp.1 p.2
  · refine ⟨hΩ_open, fun p _ => hmix p.1 p.2, fun p hp => ?_, hAbcont, hBbcont⟩
    exact hasDerivAt_goursat_eta_second hK hKb hKdb hujoint hh huη (hs_h hp.1) hp.2
  · intro p hp
    show K (clampTo c c' p.1) p.2 * u p.1 p.2 = K p.1 p.2 * u p.1 p.2
    rw [clampTo_of_mem (Ioo_subset_Icc_self (hs_c hp.1))]
  · intro p hp
    show K (clampTo c c' p.1) p.2 * u p.1 p.2 = K p.1 p.2 * u p.1 p.2
    rw [clampTo_of_mem (Ioo_subset_Icc_self (hs_c hp.1))]

end GaloisForLFunctions.HTGeometry
