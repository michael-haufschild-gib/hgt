import GaloisForLFunctions.HTGeometry.ClockGoursatPointwise

/-!
# Joint continuity of the Goursat solution

The solution of the characteristic ODE is differentiable, hence continuous, as a curve in the space
of bounded continuous functions. Evaluation on that space is continuous, so the solution read as a
function of the two null coordinates is jointly continuous on the strip where it is defined.

Joint continuity is what the remaining step of the two-dimensional construction needs: it makes the
double integral of the Goursat equation a continuous integrand on a compact rectangle, which is the
hypothesis of the Fubini exchange that produces the second mixed derivative.
-/

namespace GaloisForLFunctions.HTGeometry

open Set MeasureTheory

/-- **Joint continuity of a differentiable curve of bounded continuous functions.** -/
theorem continuousOn_bcf_eval {α : ℝ → BoundedContinuousFunction ℝ ℝ} {s : Set ℝ}
    (hα : ContinuousOn α s) :
    ContinuousOn (fun p : ℝ × ℝ => α p.1 p.2) (s ×ˢ (univ : Set ℝ)) := by
  have hmap : ContinuousOn
      (fun p : ℝ × ℝ => ((α p.1 : BoundedContinuousFunction ℝ ℝ), p.2)) (s ×ˢ univ) := by
    refine ContinuousOn.prodMk ?_ continuousOn_snd
    exact hα.comp continuousOn_fst fun p hp => hp.1
  exact ContinuousEval.continuous_eval.comp_continuousOn hmap

/-- **The Goursat solution is jointly continuous.** -/
theorem exists_goursat_jointly_continuous (K : ℝ → ℝ → ℝ) (b b' c c' M : ℝ)
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
      (∀ ξ : ℝ, ∀ η ∈ Ioo b b',
        HasDerivAt (volterraFun (K (clampTo c c' ξ)) b b' (u ξ))
          (K (clampTo c c' ξ) η * u ξ η) η) := by
  obtain ⟨h, hh, α, hα0, hαd⟩ := exists_goursat_solution K b b' c c' M hK hbb hcc hM0 hM ξ₀
  have hαc : ContinuousOn α (Icc (ξ₀ - h) (ξ₀ + h)) := fun ξ hξ =>
    (hαd ξ hξ).continuousWithinAt
  refine ⟨h, hh, fun ξ η => α ξ η, ?_, ?_, ?_, ?_, ?_⟩
  · intro η
    show α ξ₀ η = 1
    rw [hα0]
    rfl
  · intro ξ
    exact (α ξ).continuous
  · exact continuousOn_bcf_eval hαc
  · intro ξ hξ η
    exact hasDerivWithinAt_bcf_eval (hαd ξ hξ) η
  · intro ξ η hη
    exact hasDerivAt_volterraFun (continuous_kernel_slice hK _) (α ξ).continuous hη

/-- **The kernel against the solution is continuous along the characteristic parameter**, the
integrand of the second mixed derivative. -/
theorem continuousOn_kernel_mul_solution {K : ℝ → ℝ → ℝ}
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) {u : ℝ → ℝ → ℝ} {s : Set ℝ} (c c' : ℝ)
    (hu : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (s ×ˢ (univ : Set ℝ))) (η : ℝ) :
    ContinuousOn (fun τ => K (clampTo c c' τ) η * u τ η) s := by
  have h1 : ContinuousOn (fun τ : ℝ => K (clampTo c c' τ) η) s := by
    refine Continuous.continuousOn ?_
    exact hK.comp ((continuous_clampTo c c').prodMk continuous_const)
  have h2 : ContinuousOn (fun τ : ℝ => u τ η) s := by
    have hmap : ContinuousOn (fun τ : ℝ => ((τ, η) : ℝ × ℝ)) s :=
      (continuous_id.prodMk continuous_const).continuousOn
    exact hu.comp hmap fun τ hτ => ⟨hτ, mem_univ η⟩
  exact h1.mul h2

end GaloisForLFunctions.HTGeometry
