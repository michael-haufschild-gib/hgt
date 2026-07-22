import GaloisForLFunctions.Bottcher.AlgebraicBranch

open Complex Filter Topology Set

namespace HTGeometry

noncomputable section

/-- Bivariate relation for an affine perturbation of an analytic function. -/
def affineSimpleZeroRelation (H K : ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  H p.2 + p.1 * K p.2

/-- Exact analytic motion law for a simple zero under an affine perturbation. -/
theorem exists_affineSimpleZero_branch
    {H K : ℂ → ℂ} {z0 : ℂ}
    (hH : AnalyticAt ℂ H z0) (hK : AnalyticAt ℂ K z0)
    (hzero : H z0 = 0) (hsimple : deriv H z0 ≠ 0) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g 0 ∧
      g 0 = z0 ∧
      (∀ᶠ c : ℂ in 𝓝 0, H (g c) + c * K (g c) = 0) ∧
      HasDerivAt g (-K z0 / deriv H z0) 0 := by
  let f : ℂ × ℂ → ℂ := affineSimpleZeroRelation H K
  have hfan : AnalyticAt ℂ f (0, z0) := by
    have hfst : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1) (0, z0) := analyticAt_fst
    have hsnd : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) (0, z0) := analyticAt_snd
    have hsum := (hH.comp (x := (0, z0)) hsnd).add
      (hfst.mul (hK.comp (x := (0, z0)) hsnd))
    simpa [f, affineSimpleZeroRelation, Function.comp_def] using hsum
  have hroot : f (0, z0) = 0 := by
    simp [f, affineSimpleZeroRelation, hzero]
  have hHder : HasDerivAt H (deriv H z0) z0 := hH.differentiableAt.hasDerivAt
  have hpartial : HasDerivAt (fun z => f (0, z)) (deriv H z0) z0 := by
    simpa [f, affineSimpleZeroRelation] using hHder
  obtain ⟨g, hgan, hg0, hrel⟩ :=
    Bottcher.exists_analyticAt_branch_of_hasDerivAt
      hfan.contDiffAt hroot hpartial hsimple
  have hgraw : HasDerivAt g (deriv g 0) 0 := hgan.differentiableAt.hasDerivAt
  have hHcomp : HasDerivAt (fun c : ℂ => H (g c))
      (deriv H z0 * deriv g 0) 0 := by
    simpa [Function.comp_def] using hHder.comp_of_eq 0 hgraw hg0.symm
  have hKder : HasDerivAt K (deriv K z0) z0 := hK.differentiableAt.hasDerivAt
  have hKcomp : HasDerivAt (fun c : ℂ => K (g c))
      (deriv K z0 * deriv g 0) 0 := by
    simpa [Function.comp_def] using hKder.comp_of_eq 0 hgraw hg0.symm
  have hcK : HasDerivAt (fun c : ℂ => c * K (g c)) (K z0) 0 := by
    simpa [hg0] using (hasDerivAt_id (0 : ℂ)).mul hKcomp
  have hrelationDer : HasDerivAt (fun c : ℂ => H (g c) + c * K (g c))
      (deriv H z0 * deriv g 0 + K z0) 0 := hHcomp.add hcK
  have hrelEq : (fun c : ℂ => H (g c) + c * K (g c)) =ᶠ[𝓝 0]
      (fun _ : ℂ => (0 : ℂ)) := by
    simpa [f, affineSimpleZeroRelation] using hrel
  have hcoeff : deriv H z0 * deriv g 0 + K z0 = 0 :=
    hrelationDer.unique (hrelEq.hasDerivAt_iff.mpr (hasDerivAt_const 0 0))
  have hgderiv : deriv g 0 = -K z0 / deriv H z0 := by
    apply (eq_div_iff hsimple).2
    linear_combination hcoeff
  refine ⟨g, hgan, hg0, ?_, ?_⟩
  · simpa [f, affineSimpleZeroRelation] using hrel
  · simpa [hgderiv] using hgraw

/-- A real perturbation of a real simple-zero equation has horizontal first-order velocity. -/
theorem affineSimpleZeroVelocity_im_eq_zero
    {h k : ℂ} (hhim : h.im = 0) (hkim : k.im = 0) :
    (-k / h).im = 0 := by
  rw [Complex.div_im]
  simp [hhim, hkim]

/-- The analytic branch supplied by a Schwarz-real affine deformation is tangent to the real
axis at every real simple zero. -/
theorem exists_affineSimpleZero_branch_real_tangent
    {H K : ℂ → ℂ} {z0 : ℂ}
    (hH : AnalyticAt ℂ H z0) (hK : AnalyticAt ℂ K z0)
    (hzero : H z0 = 0) (hsimple : deriv H z0 ≠ 0)
    (hHreal : (deriv H z0).im = 0) (hKreal : (K z0).im = 0) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g 0 ∧
      g 0 = z0 ∧
      (∀ᶠ c : ℂ in 𝓝 0, H (g c) + c * K (g c) = 0) ∧
      HasDerivAt g (-K z0 / deriv H z0) 0 ∧
      (-K z0 / deriv H z0).im = 0 := by
  obtain ⟨g, hgan, hg0, hrel, hgder⟩ :=
    exists_affineSimpleZero_branch hH hK hzero hsimple
  exact ⟨g, hgan, hg0, hrel, hgder,
    affineSimpleZeroVelocity_im_eq_zero hHreal hKreal⟩

end

end HTGeometry

