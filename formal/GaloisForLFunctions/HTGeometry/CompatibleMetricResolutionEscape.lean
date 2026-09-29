import GaloisForLFunctions.HTGeometry.ResolutionAmplification

/-!
# Coordinate-free resolution escape

Fix a compact space `X` with full-support laws `μ₀, μ₁` and an all-depth exact formation family
`K_d` of `p₀^{⊗d}, p₁^{⊗d}` with `0 < A(p₀, p₁) < 1`.  For every metric compatible with the topology
of `X` the resolution amplifications diverge, `α_d(K_d) → ∞`.  Without any metric, the pulled-back
Neyman–Pearson effects `e_d = K_d^* 1_{B_d}` of a Feller family eventually leave every
equicontinuous family of `[0, 1]`-valued continuous effects.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [t : TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {Y : Type*} [Fintype Y] [MetricSpace Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- **Corollary 4.2 (RP.15a).**  `α_d(K_d) → ∞` for every metric `d` compatible with the topology.
-/
theorem tendsto_resolutionAmplification_of_compatible (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [P.IsOpenPosMeasure] [Q.IsOpenPosMeasure]
    (hsep : ∀ y y' : Y, y ≠ y' → 1 ≤ dist y y') (p₀ p₁ : Measure Y) [IsProbabilityMeasure p₀]
    [IsProbabilityMeasure p₁] (hA0 : 0 < hellingerAffinity p₀ p₁)
    (hA1 : hellingerAffinity p₀ p₁ < 1) (K : ∀ d : ℕ, Kernel X (Fin d → Y))
    [∀ d, IsMarkovKernel (K d)] (h₀ : ∀ d, IsExactFormation P (K d) p₀)
    (h₁ : ∀ d, IsExactFormation Q (K d) p₁) (B : ∀ d : ℕ, Set (Fin d → Y))
    (hNP : ∀ d, IsNeymanPearson p₀ p₁ (B d)) (m : MetricSpace X)
    (hm : m.toUniformSpace.toTopologicalSpace = t) :
    Tendsto (fun d => @resolutionAmplification X (Fin d → Y) m _ _ _ (K d)) atTop (𝓝 ⊤) := by
  subst hm
  exact tendsto_resolutionAmplification P Q hsep p₀ p₁ hA0 hA1 K h₀ h₁ B hNP

omit [MetricSpace Y] in
/-- **Corollary 4.2.**  The pulled-back Neyman–Pearson effects of a Feller all-depth exact
formation eventually leave every equicontinuous family of `[0, 1]`-valued effects. -/
theorem eventually_formationEffect_not_mem_of_equicontinuous (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [P.IsOpenPosMeasure] [Q.IsOpenPosMeasure]
    (p₀ p₁ : Measure Y) [IsProbabilityMeasure p₀] [IsProbabilityMeasure p₁] (hne : p₀ ≠ p₁)
    (K : ∀ d : ℕ, Kernel X (Fin d → Y)) [∀ d, IsMarkovKernel (K d)]
    (h₀ : ∀ d, IsExactFormation P (K d) p₀) (h₁ : ∀ d, IsExactFormation Q (K d) p₁)
    (B : ∀ d : ℕ, Set (Fin d → Y)) (hNP : ∀ d, IsNeymanPearson p₀ p₁ (B d))
    {F : Set C(X, ℝ)} (hb : ∀ e ∈ F, ∀ x, e x ∈ Icc (0 : ℝ) 1)
    (hF : Equicontinuous fun f : F => ((f : C(X, ℝ)) : X → ℝ)) :
    ∃ N, ∀ d ≥ N, ∀ f ∈ F, ¬ ∀ x, f x = formationEffect (K d) (B d) x := by
  by_contra h
  push Not at h
  refine not_equicontinuous_of_formsInFamily P Q p₀ p₁ hne hb (fun N => ?_) hF
  obtain ⟨d, hd, f, hf, hfe⟩ := h N
  exact ⟨d, hd, K d, inferInstance, h₀ d, h₁ d, B d, hNP d, f, hf, hfe⟩

end GaloisForLFunctions.HTGeometry
