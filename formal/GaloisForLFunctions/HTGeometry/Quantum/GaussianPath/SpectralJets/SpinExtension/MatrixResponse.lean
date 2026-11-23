import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.RootTangent

/-! # Matrix differential of a simple energy in a split spin sector -/
open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- One old eigenvalue germ gives the sector velocity for every
transverse block pair, through its linear matrix differential. -/
theorem simple_root_sector_velocities (H : Mat I) (z : ℂ) (hz : H.charpoly.eval z=0)
    (hs : H.charpoly.derivative.eval z≠0) :
    ∃ f : Mat I → ℂ, AnalyticAt ℂ f H ∧ f H=z ∧
      (∀ᶠ K in 𝓝 H, matrixCharpolyRelation (K,f K)=0) ∧
      ∀ (b : ℂ), b≠0 → ∀ W V : Mat I, ∃ e : ℂ → ℂ, AnalyticAt ℂ e 0 ∧ e 0=z ∧
        (∀ᶠ u in 𝓝 0, splitDet (scalar I (e u)-H) W V b u=0) ∧
        deriv e 0=fderiv ℂ f H (b⁻¹ • (W*V)) := by
  have hrel : matrixCharpolyRelation (H,z)=0 := by simpa only [matrixCharpolyRelation,←Matrix.eval_charpoly] using hz
  obtain ⟨f,hf,hf₀,hroot⟩ := parametric_holo_implicit (matrixCharpolyRelation_analyticAt (H,z))
    hrel ((matrixCharpolyRelation_partial_w H z).trans_ne hs)
  refine ⟨f,hf,hf₀,hroot,?_⟩
  intro b hb W V
  let Z := b⁻¹ • (W*V)
  let line (s : ℂ) := H+s • Z
  have hline : HasDerivAt line Z 0 := by
    simpa only [line,id_eq,one_smul] using ((hasDerivAt_id (0:ℂ)).smul_const Z).const_add H
  have hzero : line 0=H := by simp [line]
  have hf' : AnalyticAt ℂ f (line 0) := hzero.symm ▸ hf
  have ha : AnalyticAt ℂ line 0 := analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  let g := f ∘ line
  have hg₀ : g 0=z := by rw [show g 0=f (line 0) from rfl,hzero,hf₀]
  have hlim : Tendsto line (𝓝 0) (𝓝 H) := by simpa only [hzero] using hline.continuousAt.tendsto
  obtain ⟨e,he,he₀,her⟩ := normalized_branch H W V b z hb hz hs
  have ht := spin_root_tangent H Z W V b b⁻¹ 0 1 (mul_inv_cancel₀ hb)
    (by simp [Z]) g e (hf'.comp ha) he (he₀.trans hg₀.symm) (hlim.eventually hroot) her (hg₀.symm ▸ hs)
  have hd := (hf'.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hline).deriv
  rw [hzero] at hd
  exact ⟨e,he,he₀,her,(by simpa only [one_mul,zero_add] using ht : deriv e 0=deriv g 0).trans hd⟩

#print axioms simple_root_sector_velocities
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
