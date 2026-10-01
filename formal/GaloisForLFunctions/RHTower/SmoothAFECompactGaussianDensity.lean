import GaloisForLFunctions.RHTower.SmoothAFECompactGaussianHolomorphicAnnihilator
import GaloisForLFunctions.HTGeometry.LocallyConvexDenseOfVanishingDual
import Mathlib.Analysis.RCLike.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open Complex Set Metric
noncomputable section
namespace RHTower

/-- Every function holomorphic on a larger disc lies in the closed complex
linear span of imaginary Gaussian Cauchy modes on the smaller right-hand disc. -/
theorem mem_closedSpan_compactGaussianModes_of_holomorphic_disc
    (c : ℂ) {r R : ℝ} [CompactSpace (closedBall c r)]
    (hr : 0 ≤ r) (hc : r < c.re) (hR : r < R)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (closedBall c R))
    (g : C(closedBall c r, ℂ)) (hg : ∀ z, g z = f z) :
    g ∈ (Submodule.span ℂ (Set.range fun t : ℝ =>
      compactGaussianCauchyKernel (closedBall c r) ((t : ℂ) * I))).topologicalClosure := by
  let S := Submodule.span ℂ (Set.range fun t : ℝ =>
    compactGaussianCauchyKernel (closedBall c r) ((t : ℂ) * I))
  change g ∈ S.topologicalClosure
  by_contra hnot
  obtain ⟨l, hl, hlg⟩ :=
    HTGeometry.exists_dual_vanishing_of_notMem_closed_submodule_lcs
      (S.topologicalClosure.restrictScalars ℝ) S.isClosed_topologicalClosure hnot
  let A : C(closedBall c r, ℂ) →L[ℂ] ℂ := StrongDual.extendRCLike l
  have haxis (t : ℝ) :
      A (compactGaussianCauchyKernel (closedBall c r) ((t : ℂ) * I)) = 0 := by
    let v := compactGaussianCauchyKernel (closedBall c r) ((t : ℂ) * I)
    have hv : v ∈ S.topologicalClosure :=
      S.le_topologicalClosure (Submodule.subset_span ⟨t, rfl⟩)
    have hiv : I • v ∈ S.topologicalClosure := S.topologicalClosure.smul_mem I hv
    change StrongDual.extendRCLike (𝕜 := ℂ) l v = 0
    rw [StrongDual.extendRCLike_apply, RCLike.I_to_complex, hl v hv, hl (I • v) hiv]
    simp
  have hAg := compactGaussianFunctional_annihilates_holomorphic_disc c hr hc hR
    A haxis hf g hg
  have hre : (A g).re = l g := by
    simpa only [RCLike.re_to_complex] using (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) l g)
  exact hlg (by rw [hAg, Complex.zero_re] at hre; exact hre.symm)

/-- Supremum-norm approximation uses finite linear combinations of the modes. -/
theorem exists_finite_compactGaussianModes_approximation
    (c : ℂ) {r R : ℝ} [CompactSpace (closedBall c r)]
    (hr : 0 ≤ r) (hc : r < c.re) (hR : r < R)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (closedBall c R))
    (g : C(closedBall c r, ℂ)) (hg : ∀ z, g z = f z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ →₀ ℂ, ‖g - a.sum (fun t b => b •
      compactGaussianCauchyKernel (closedBall c r) ((t : ℂ) * I))‖ < ε := by
  have hclosed := mem_closedSpan_compactGaussianModes_of_holomorphic_disc c hr hc hR hf g hg
  change g ∈ closure (↑(Submodule.span ℂ (Set.range fun t : ℝ =>
    compactGaussianCauchyKernel (closedBall c r) ((t : ℂ) * I))) :
      Set C(closedBall c r, ℂ)) at hclosed
  obtain ⟨q, hq, hdist⟩ := Metric.mem_closure_iff.mp hclosed ε hε
  obtain ⟨a, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hq
  refine ⟨a, ?_⟩
  simpa only [dist_eq_norm] using hdist

end RHTower
