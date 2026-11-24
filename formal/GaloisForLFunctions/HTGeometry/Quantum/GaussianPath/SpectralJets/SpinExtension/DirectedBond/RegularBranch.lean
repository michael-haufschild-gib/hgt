import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.SectorReduction
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.RootGraph
import GaloisForLFunctions.HTGeometry.GeneralParametricEigenbranch

/-! # Joint analytic energy branch at infinite terminal splitting -/
open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "M" => Matrix I I ℂ
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem zero_splitting_equation (H V : M) (e a z : ℂ) (hz : z≠0) :
    (reduced (scalar I e-H) V a z 0).det =
      (2*z)^Fintype.card I*matrixCharpolyRelation (H+(a/z) • V,e) := by
  have hscale : (2*z)*(a/z)=2*a := by field_simp
  have he : reduced (scalar I e-H) V a z 0=(2*z) • (scalar I e-(H+(a/z) • V)) := by
    simp only [reduced,zero_smul,add_zero,← sub_sub,smul_sub,smul_smul,hscale]
  rw [he,det_smul,matrixCharpolyRelation]

omit [DecidableEq I] in
private theorem analytic_product {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {A B : P→M} {p : P} (ha : AnalyticAt ℂ A p) (hb : AnalyticAt ℂ B p) :
    AnalyticAt ℂ (fun y => A y*B y) p := by
  apply analyticAt_matrix_of_entries
  intro i j
  apply Finset.analyticAt_fun_sum
  exact fun r _ => (analyticAt_matrix_entry ha i r).mul (analyticAt_matrix_entry hb r j)

private def equation (H V : E→M) (z : E→ℂ) (a : ℂ) (p : (E × ℂ) × ℂ) :=
  (reduced (scalar I p.2-H p.1.1) (V p.1.1) a (z p.1.1) p.1.2).det

omit [CompleteSpace E] in
private theorem analytic_equation {H V : E→M} {z : E→ℂ} {x : E} (a u e : ℂ)
    (hH : AnalyticAt ℂ H x) (hV : AnalyticAt ℂ V x) (hz : AnalyticAt ℂ z x) :
    AnalyticAt ℂ (equation H V z a) ((x,u),e) := by
  let p := ((x,u),e)
  have hx : AnalyticAt ℂ (fun q : (E × ℂ) × ℂ => q.1.1) p := analyticAt_fst.comp analyticAt_fst
  have hu : AnalyticAt ℂ (fun q : (E × ℂ) × ℂ => q.1.2) p := analyticAt_snd.comp analyticAt_fst
  have hl : AnalyticAt ℂ (fun q : (E × ℂ) × ℂ => scalar I q.2-H q.1.1) p := by
    simp only [scalar_eq_smul]
    exact (analyticAt_snd.smul analyticAt_const).sub (hH.comp hx)
  have hv := hV.comp hx
  have hc : AnalyticAt ℂ (fun q : (E × ℂ) × ℂ => 2*z q.1.1) p :=
    analyticAt_const.mul (hz.comp hx)
  have hd : AnalyticAt ℂ (fun _ : (E × ℂ) × ℂ => 2*a) p := analyticAt_const
  have hr : AnalyticAt ℂ (fun q : (E × ℂ) × ℂ =>
      reduced (scalar I q.2-H q.1.1) (V q.1.1) a (z q.1.1) q.1.2) p := by
    unfold reduced
    exact ((hc.smul hl).sub (hd.smul hv)).add (hu.smul (analytic_product (hl.add hv) (hl.sub hv)))
  exact analyticAt_matrix_det_parametric (analyticAt_matrix_entry hr)

/-- At inverse splitting zero the new energy equals the old energy in
the longitudinally projected field, as a germ in every remaining control. -/
theorem regular_branch {H V : E→M} {z f : E→ℂ} {x : E} (a : ℂ)
    (hH : AnalyticAt ℂ H x) (hV : AnalyticAt ℂ V x) (hz : AnalyticAt ℂ z x) (hf : AnalyticAt ℂ f x)
    (hn : z x≠0) (hroot : ∀ᶠ p in 𝓝 x, matrixCharpolyRelation (H p+(a/z p) • V p,f p)=0)
    (hs : (H x+(a/z x) • V x).charpoly.derivative.eval (f x)≠0) :
    ∃ e : E × ℂ →ℂ, AnalyticAt ℂ e (x,0) ∧ e (x,0)=f x ∧
      (∀ᶠ p in 𝓝 x, e (p,0)=f p) ∧ ∀ᶠ q in 𝓝 (x,(0:ℂ)),
        (reduced (scalar I (e q)-H q.1) (V q.1) a (z q.1) q.2).det=0 := by
  let F := equation H V z a
  let v := f x
  let K := H x+(a/z x) • V x
  let c := (2*z x)^Fintype.card I
  have hF := analytic_equation a 0 v hH hV hz
  have hline (r : ℂ) : F ((x,0),r)=c*K.charpoly.eval r := by
    dsimp only [F,equation]
    rw [zero_splitting_equation _ _ _ _ _ hn]
    simp only [matrixCharpolyRelation,←Matrix.eval_charpoly,K,c]
  have h₀ : F ((x,0),v)=0 := by
    dsimp only [F,equation,v]
    rw [zero_splitting_equation _ _ _ _ _ hn,hroot.self_of_nhds,mul_zero]
  have hd := hF.differentiableAt.hasFDerivAt.comp_hasDerivAt (f:=fun r : ℂ => ((x,(0:ℂ)),r)) v
    ((hasDerivAt_const v (x,(0:ℂ))).prodMk (hasDerivAt_id v))
  have hp : fderiv ℂ F ((x,0),v) (0,1)=c*K.charpoly.derivative.eval v :=
    hd.unique (((K.charpoly.hasDerivAt v).const_mul c).congr_of_eventuallyEq (Eventually.of_forall hline))
  obtain ⟨e,he,he₀,hg⟩ := analytic_simple_root_graph hF h₀
    (hp.trans_ne (mul_ne_zero (pow_ne_zero _ (mul_ne_zero (by norm_num) hn)) hs))
  refine ⟨e,he,he₀,?_,?_⟩
  · apply root_graph_restrict hg (fun p => (p,0)) f (continuousAt_id.prodMk continuousAt_const).tendsto hf.continuousAt.tendsto
    filter_upwards [hroot,hz.continuousAt.eventually_ne hn] with p h hne
    dsimp only [F,equation]
    rw [zero_splitting_equation _ _ _ _ _ hne,h,mul_zero]
  · have ht : Tendsto (fun q : E × ℂ => (q,e q)) (𝓝 (x,0)) (𝓝 ((x,0),v)) := by
      simpa only [id_eq,he₀] using (continuousAt_id.prodMk he.continuousAt).tendsto
    exact (ht.eventually hg).mono fun q h => h.mpr rfl

#print axioms regular_branch
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
