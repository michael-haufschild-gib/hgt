import GaloisForLFunctions.HTGeometry.SplitFibreSection
import GaloisForLFunctions.HTGeometry.AlgebraSpectrumChart
import GaloisForLFunctions.HTGeometry.ComplexAffineLineSimplyConnected

/-!
# The values of a continuous section are analytic

On the chart at a point, the section's value on the chart generator is a continuous root branch of
the chart relation, hence analytic; every other element is then a rational expression in the chart
coordinates.  This is the analyticity half of step (c) of the general simple connectedness of the
affine line.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {B : Type*} [CommRing B] [Algebra ℂ[X] B] [Algebra ℂ B] [IsScalarTower ℂ ℂ[X] B]

/-- **The values of a continuous section are analytic.** -/
theorem analyticAt_section_apply [Module.Free ℂ[X] B] [Module.Finite ℂ[X] B]
    {n : ℕ} (hn : 1 ≤ n) (e : Module.Basis (Fin n) ℂ[X] B) (h : SplitFibres B n)
    {σ : ℂ → AlgSpec B} (hσc : Continuous σ) (hσ : ∀ s, AlgSpec.proj B (σ s) = s)
    (b : B) (s₀ : ℂ) : AnalyticAt ℂ (fun s => σ s b) s₀ := by
  obtain ⟨θ, p, U, hp, hmonic, hU, hmem, hgen, hsep, -⟩ :=
    exists_chart_of_splitFibres hn e h (σ s₀)
  rw [hσ s₀] at hmem
  have hθc : Continuous fun s => σ s θ := (AlgSpec.continuous_eval θ).comp hσc
  have hθroot : ∀ s, biEval p (s, σ s θ) = 0 := by
    intro s
    have := AlgSpec.apply_aeval θ p (σ s)
    rw [hp, map_zero, hσ s] at this
    exact this.symm
  have hθan : AnalyticAt ℂ (fun s => σ s θ) s₀ :=
    analyticAt_of_continuous_biRoot_at hθc hθroot s₀ (hsep s₀ hmem)
  obtain ⟨q, g, hgU, hb⟩ := hgen b
  have hEq : ∀ s ∈ U, σ s b = biEval q (s, σ s θ) / g.eval s := by
    intro s hs
    have h1 := eval_eq_of_gen hgU hb (χ := σ s) (by rw [hσ s]; exact hs)
    rw [AlgSpec.toPlane, hσ s] at h1
    exact h1
  refine AnalyticAt.congr ?_ (Filter.eventuallyEq_of_mem (hU.mem_nhds hmem) (fun s hs =>
    (hEq s hs).symm))
  have hgan : AnalyticAt ℂ (fun s : ℂ => g.eval s) s₀ := by
    have := (analyticAt_id (𝕜 := ℂ) (z := s₀)).aeval_polynomial g
    simpa using this
  exact ((analyticAt_biEval q (s₀, σ s₀ θ)).comp₂ analyticAt_id hθan).div hgan (hgU s₀ hmem)

end

end GaloisForLFunctions.HTGeometry
