import GaloisForLFunctions.RHTower.FokasLenellsCausalAnalyticGraphCore
import GaloisForLFunctions.RHTower.FokasLenellsCausalGeneratorEigenvectors

/-! Rational Cauchy eigenvectors form a core for the actual maximal causal generator:
finite rational sums approximate both the state and its generator derivative. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The actual state/derivative graph pair of a rational Cauchy eigenvector. -/
def causalCauchyEigenGraph (w : {z : ℂ // 0 < z.im}) : causalGeneratorGraph :=
  ⟨((causalCauchyEigenDomain w).val, causalGenerator (causalCauchyEigenDomain w)),
    (causalGeneratorGraph_mem_iff _ _).2 (causalGenerator_hasRightDeriv _)⟩

/-- The actual graph resolvent maps every rational input to a scalar multiple of its graph pair. -/
theorem causalResolventGraph_cauchyEigenvector (a : ℝ) (w : {z : ℂ // 0 < z.im}) :
    causalResolventGraph a (causalCauchyEigenvector w) =
      ((Real.exp a : ℂ)-causalPoleRate w.val)⁻¹ • causalCauchyEigenGraph w := by
  have hne : ((Real.exp a : ℂ)-causalPoleRate w.val) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
    have hw := causalPoleRate_re_neg w
    linarith [Real.exp_pos a]
  have he : causalResolvent a (causalCauchyEigenvector w) =
      ((Real.exp a : ℂ)-causalPoleRate w.val)⁻¹ • causalCauchyEigenDomain w := by
    apply causalGeneratorShift_injective a
    rw [causalGeneratorShift_resolvent, map_smul]
    change causalCauchyEigenvector w = ((Real.exp a : ℂ)-causalPoleRate w.val)⁻¹ •
      ((Real.exp a : ℂ) • (causalCauchyEigenDomain w).val -
        causalGenerator (causalCauchyEigenDomain w))
    rw [causalGenerator_cauchyEigenDomain, ← sub_smul, inv_smul_smul₀ hne]
    rfl
  apply causalGeneratorGraphInput_injective
  exact congrArg (fun u : causalGeneratorDomain => u.val) he

/-- Finite rational Cauchy sums are dense in the full generator graph norm, not merely in data norm. -/
theorem topologicalClosure_span_causalCauchyEigenGraph_eq_top :
    (Submodule.span ℂ (Set.range causalCauchyEigenGraph)).topologicalClosure = ⊤ := by
  let M := (Submodule.span ℂ (Set.range causalCauchyEigenGraph)).topologicalClosure
  let S := Submodule.span ℂ (Set.range causalCauchyEigenvector)
  have hc : IsClosed {v : hardyL2ᗮ | causalResolventGraph 0 v ∈ M} :=
    (Submodule.span ℂ (Set.range causalCauchyEigenGraph)).isClosed_topologicalClosure.preimage
      (causalResolventGraph 0).continuous
  have hs : (S : Set (hardyL2ᗮ)) ⊆ {v : hardyL2ᗮ | causalResolventGraph 0 v ∈ M} := by
    have hsub : S ≤ M.comap (causalResolventGraph 0).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro v ⟨w, rfl⟩
      change causalResolventGraph 0 (causalCauchyEigenvector w) ∈ M
      rw [causalResolventGraph_cauchyEigenvector]
      apply M.smul_mem
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, rfl⟩)
    exact hsub
  have hd (v : hardyL2ᗮ) : v ∈ closure (S : Set (hardyL2ᗮ)) := by
    rw [← Submodule.topologicalClosure_coe]
    change v ∈ ((Submodule.span ℂ (Set.range causalCauchyEigenvector)).topologicalClosure : Set (hardyL2ᗮ))
    rw [topologicalClosure_span_causalCauchyEigenvector_eq_top]
    trivial
  apply top_unique
  intro p _
  obtain ⟨v, rfl⟩ := causalResolventGraph_surjective 0 p
  exact (closure_minimal hs hc) (hd v)

end
end RHTower.FokasLenells
