import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.RootGraph
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.RootTangent

/-! # A common spectral branch for varying old and transverse operators -/
open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.Anchored
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev M := Matrix I I ℂ

/-- Old generator and the two ordered transverse blocks. -/
abbrev Blocks (I : Type*) := Matrix I I ℂ × Matrix I I ℂ × Matrix I I ℂ

def relation (b : ℂ) (x : (Blocks I × ℂ) × ℂ) : ℂ :=
  splitDet (scalar I x.2-x.1.1.1) x.1.1.2.1 x.1.1.2.2 b x.1.2

private theorem analytic_entry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : E → M} {x : E} (h : AnalyticAt ℂ A x) (i j : I) :
    AnalyticAt ℂ (fun p => A p i j) x := by
  let row : M →L[ℂ] (I → ℂ) := ContinuousLinearMap.proj (R:=ℂ) i
  let col : (I → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R:=ℂ) j
  exact ((col.comp row).analyticAt _).comp h

private theorem relation_analytic (b : ℂ) (x : (Blocks I × ℂ) × ℂ) :
    AnalyticAt ℂ (relation b) x := by
  have hB : AnalyticAt ℂ (fun q : (Blocks I × ℂ) × ℂ => q.1.1) x := analyticAt_fst.comp analyticAt_fst
  have hH := analyticAt_fst.comp hB
  have hT := analyticAt_snd.comp hB
  have hu : AnalyticAt ℂ (fun q : (Blocks I × ℂ) × ℂ => q.1.2) x := analyticAt_snd.comp analyticAt_fst
  have he (i j : I) : AnalyticAt ℂ (fun q : (Blocks I × ℂ) × ℂ => (scalar I q.2-q.1.1.1) i j) x := by
    by_cases hij : i=j
    · subst j
      simpa only [Matrix.sub_apply,scalar_apply,diagonal_apply_eq] using!
        (analyticAt_snd.sub (analytic_entry hH i i))
    · simpa [scalar_apply,hij] using! (analytic_entry hH i j).neg
  apply analyticAt_matrix_det_parametric
  intro i j
  cases i with
  | inl i => cases j with
    | inl j => exact he i j
    | inr j => exact (analytic_entry (analyticAt_fst.comp hT) i j).neg
  | inr i => cases j with
    | inl j => exact (hu.mul (analytic_entry (analyticAt_snd.comp hT) i j)).neg
    | inr j => exact analyticAt_const.add (hu.mul (he i j))

/-- One analytic graph continues the simple root while all transverse
and old matrix entries vary. At inverse splitting zero its restriction
is the old matrix root throughout a neighbourhood. -/
theorem joint_root_graph (H W V : M) (b z : ℂ) (hb : b≠0)
    (hz : H.charpoly.eval z=0) (hs : H.charpoly.derivative.eval z≠0) :
    ∃ (f : M → ℂ) (e : Blocks I × ℂ → ℂ),
      AnalyticAt ℂ f H ∧ f H=z ∧ (∀ᶠ K in 𝓝 H, matrixCharpolyRelation (K,f K)=0) ∧
      AnalyticAt ℂ e ((H,W,V),0) ∧ e ((H,W,V),0)=z ∧
      (∀ᶠ p in 𝓝 ((H,W,V),(0:ℂ)), relation b (p,e p)=0) ∧
      ∀ᶠ p : Blocks I in 𝓝 (H,W,V), e (p,0)=f p.1 := by
  let p₀ : Blocks I := (H,W,V)
  have hz' : matrixCharpolyRelation (H,z)=0 := by
    simpa only [matrixCharpolyRelation,←Matrix.eval_charpoly] using hz
  obtain ⟨f,hf,hf₀,hroot⟩ := parametric_holo_implicit (matrixCharpolyRelation_analyticAt (H,z)) hz'
    ((matrixCharpolyRelation_partial_w H z).trans_ne hs)
  have hF := relation_analytic b ((p₀,0),z)
  have h₀ : relation b ((p₀,0),z)=0 := (normalized_zero H W V b z).trans (by rw [hz,zero_mul])
  have hpart : fderiv ℂ (relation b) ((p₀,0),z) (0,1) = H.charpoly.derivative.eval z*b^Fintype.card I := by
    have hd := hF.differentiableAt.hasFDerivAt.comp_hasDerivAt (f:=fun w : ℂ => ((p₀,(0:ℂ)),w)) z
      ((hasDerivAt_const z (p₀,(0:ℂ))).prodMk (hasDerivAt_id z))
    have hp := (H.charpoly.hasDerivAt z).mul_const (b^Fintype.card I)
    exact hd.unique (hp.congr_of_eventuallyEq (Eventually.of_forall (normalized_zero H W V b)))
  obtain ⟨e,he,he₀,hgraph⟩ := analytic_simple_root_graph hF h₀
    (hpart.trans_ne (mul_ne_zero hs (pow_ne_zero _ hb)))
  have hpair := continuousAt_id.prodMk he.continuousAt
  have hg : ∀ᶠ p in 𝓝 (p₀,(0:ℂ)), relation b (p,e p)=0 := by
    filter_upwards [(by simpa only [he₀] using hpair.tendsto :
      Tendsto (fun p : Blocks I × ℂ => (p,e p)) (𝓝 (p₀,0)) (𝓝 ((p₀,0),z))).eventually hgraph] with p hp
    exact hp.mpr rfl
  refine ⟨f,e,hf,hf₀,hroot,he,he₀,hg,?_⟩
  have hh : Tendsto (fun p : Blocks I => p.1) (𝓝 p₀) (𝓝 H) := continuousAt_fst
  apply root_graph_restrict hgraph (fun p : Blocks I => (p,0)) (fun p => f p.1)
    (continuousAt_id.prodMk continuousAt_const).tendsto (by simpa only [hf₀] using hf.continuousAt.tendsto.comp hh)
  filter_upwards [hh.eventually hroot] with p hp
  have hh' : p.1.charpoly.eval (f p.1)=0 := by
    simpa only [matrixCharpolyRelation,←Matrix.eval_charpoly] using hp
  exact (normalized_zero p.1 p.2.1 p.2.2 b _).trans (by rw [hh',zero_mul])

#print axioms joint_root_graph
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.Anchored
