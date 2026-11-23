import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.Anchored.JointGraph

/-! # The ordered transverse product as an identity of spectral germs -/
open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.Anchored
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev M := Matrix I I ℂ

private theorem simple_near (H : M) (z : ℂ) (hs : H.charpoly.derivative.eval z≠0) :
    ∀ᶠ q : M × ℂ in 𝓝 (H,z), q.1.charpoly.derivative.eval q.2 ≠ 0 := by
  let L (q : M × ℂ) := fderiv ℂ matrixCharpolyRelation q (0,1)
  have hc : ContinuousAt L (H,z) :=
    (((ContinuousLinearMap.apply ℂ ℂ ((0,1) : M × ℂ)).analyticAt _).comp
      (matrixCharpolyRelation_analyticAt (H,z)).fderiv).continuousAt
  have hL : L (H,z) ≠ 0 := (matrixCharpolyRelation_partial_w H z).trans_ne hs
  exact (hc.eventually_ne hL).mono fun q h => (matrixCharpolyRelation_partial_w q.1 q.2).symm.trans_ne h

/-- The inverse-splitting derivative equals the old root differential
applied to the ordered transverse product, throughout a neighbourhood
of all three matrices. Old physical derivatives can thus act on this identity. -/
theorem joint_transverse_slope (H W V : M) (b z : ℂ) (hb : b≠0)
    (hz : H.charpoly.eval z=0) (hs : H.charpoly.derivative.eval z≠0) :
    ∃ (f : M → ℂ) (e : Blocks I × ℂ → ℂ), AnalyticAt ℂ f H ∧ f H=z ∧
      AnalyticAt ℂ e ((H,W,V),0) ∧ e ((H,W,V),0)=z ∧
      (∀ᶠ p in 𝓝 ((H,W,V),(0:ℂ)), relation b (p,e p)=0) ∧
      ∀ᶠ p : Blocks I in 𝓝 (H,W,V), deriv (fun u : ℂ => e (p,u)) 0 =
        fderiv ℂ f p.1 (b⁻¹ • (p.2.1*p.2.2)) := by
  let p₀ : Blocks I := (H,W,V)
  obtain ⟨f,e,hf,hf₀,hroot,he,he₀,hg,hmatch⟩ := joint_root_graph H W V b z hb hz hs
  refine ⟨f,e,hf,hf₀,he,he₀,hg,?_⟩
  have hm : Tendsto (fun p : Blocks I => p.1) (𝓝 p₀) (𝓝 H) := continuousAt_fst
  have h0 : Tendsto (fun p : Blocks I => (p,(0:ℂ))) (𝓝 p₀) (𝓝 (p₀,0)) :=
    (continuousAt_id.prodMk continuousAt_const).tendsto
  have hf' : Tendsto (fun p : Blocks I => f p.1) (𝓝 p₀) (𝓝 z) := by simpa only [hf₀] using hf.continuousAt.tendsto.comp hm
  filter_upwards [hmatch,hm.eventually hf.eventually_analyticAt,hm.eventually hroot.eventually_nhds,
    h0.eventually he.eventually_analyticAt,h0.eventually hg.eventually_nhds,
    (hm.prodMk_nhds hf').eventually (simple_near H z hs)] with p hmatch hfa hfr hea her hsimple
  let Z := b⁻¹ • (p.2.1*p.2.2)
  let line (s : ℂ) := p.1+s • Z
  have hline : HasDerivAt line Z 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0:ℂ)).smul_const Z).const_add p.1
  have hz₀ : line 0=p.1 := by simp [line]
  have ha : AnalyticAt ℂ line 0 := analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hua : AnalyticAt ℂ (fun u : ℂ => (p,u)) 0 := analyticAt_const.prodMk analyticAt_id
  have hfa' : AnalyticAt ℂ f (line 0) := hz₀.symm ▸ hfa
  have h := spin_root_tangent p.1 Z p.2.1 p.2.2 b b⁻¹ 0 1 (mul_inv_cancel₀ hb)
    (by simp [Z]) (f ∘ line) (fun u => e (p,u)) (hfa'.comp ha) (hea.comp hua)
    (by simpa only [Function.comp_apply,hz₀] using hmatch)
    (by exact (hz₀ ▸ hline.continuousAt.tendsto).eventually hfr)
    (hua.continuousAt.tendsto.eventually her)
    (by simpa only [Function.comp_apply,hz₀] using hsimple)
  have hd := (hfa'.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hline).deriv
  rw [hz₀] at hd
  exact (by simpa only [one_mul,zero_add] using h : _ = deriv (f ∘ line) 0).trans hd

#print axioms joint_transverse_slope
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.Anchored
