import GaloisForLFunctions.HTGeometry.RealAnalyticImplicit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.LocalZeros

/-! # Null projection of simultaneous analytic equations at a simple time root -/

open Set Filter MeasureTheory Metric Topology
open scoped ContDiff
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicTimes
noncomputable section

private theorem root_graph {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {F : P × ℝ → ℝ} {x : P} {t : ℝ} (ha : AnalyticAt ℝ F (x,t)) (hz : F (x,t)=0)
    (hd : fderiv ℝ F (x,t) (0,1)≠0) :
    ∃ f : P → ℝ, AnalyticAt ℝ f x ∧ f x=t ∧ ∀ᶠ u in 𝓝 (x,t), F u=0 ↔ f u.1=u.2 := by
  have hD : ContDiffAt ℝ ω F (x,t) := ha.contDiffAt
  have hI : (fderiv ℝ F (x,t) ∘L (.inr ℝ P ℝ)).IsInvertible :=
    clm_invertible_of_apply_one_ne_real (by simpa using hd)
  have hω : (ω : WithTop ℕ∞)≠0 := by decide
  exact ⟨hD.implicitFunction hω hI,(hD.contDiffAt_implicitFunction hω hI).analyticAt,
    hD.implicitFunction_apply_self hω hI,by simpa only [hz] using hD.eventually_apply_eq_iff_implicitFunction hω hI⟩

/-- If a dense set of coupling vectors admits no common root, the
parameters admitting a common root simple in the time equation form
a null set. Analyticity is needed only on the open domain in question. -/
theorem projection_simple_root_null {m : ℕ} {W : Set ((Fin m → ℝ) × ℝ)} (hW : IsOpen W)
    {F : (Fin m → ℝ) × ℝ → ℝ} {G : (Fin m → ℝ) × ℝ → ℂ}
    (hF : AnalyticOnNhd ℝ F W) (hG : AnalyticOnNhd ℝ G W)
    {D : Set (Fin m → ℝ)} (hD : Dense D)
    (hsep : ∀ x∈D, ∀ t, (x,t)∈W → F (x,t)=0 → G (x,t)≠0) :
    volume (Prod.fst '' {p∈W | F p=0 ∧ fderiv ℝ F p (0,1)≠0 ∧ G p=0})=0 := by
  let Z := {p∈W | F p=0 ∧ fderiv ℝ F p (0,1)≠0 ∧ G p=0}
  have chart (p : ↥Z) : ∃ O, IsOpen O ∧ p.val∈O ∧ volume (Prod.fst '' (O∩Z))=0 := by
    rcases p with ⟨⟨x,t⟩,hw,hz,hder,hzero⟩
    obtain ⟨f,hf,hx,hgraph⟩ := root_graph (hF _ hw) hz hder
    obtain ⟨A,hA,B,hB,hbox⟩ := mem_nhds_prod_iff.mp ((hW.mem_nhds hw).and hgraph)
    obtain ⟨V,hVB,hoV,htV⟩ := mem_nhds_iff.mp hB
    have hV : ∀ᶠ y in 𝓝 x, f y∈V := hf.continuousAt.eventually (hoV.mem_nhds (hx.symm ▸ htV))
    obtain ⟨U,hU,hoU,hxU⟩ := mem_nhds_iff.mp (hA.and (hV.and hf.eventually_analyticAt))
    have row {y} (hy : y∈U) : (y,f y)∈W ∧ F (y,f y)=0 := by
      obtain ⟨hmem,heq⟩ := hbox (show (y,f y)∈A ×ˢ B from ⟨(hU hy).1,hVB (hU hy).2.1⟩)
      exact ⟨hmem,heq.mpr rfl⟩
    let g (y : Fin m → ℝ) := G (y,f y)
    have hg : AnalyticOnNhd ℝ g U := fun y hy => (hG _ (row hy).1).comp
      (analyticAt_id.prod (hU hy).2.2)
    have hn : volume {y∈U | g y=0}=0 := by
      apply AlgebraicCurves.analytic_zero_null hoU hg
      intro y hy r hr hsub
      obtain ⟨v,hd,hv⟩ := hD.exists_mem_open isOpen_ball (nonempty_ball.mpr hr)
      exact ⟨v,hv,hsep v hd _ (row (hsub hv)).1 (row (hsub hv)).2⟩
    refine ⟨U ×ˢ V,hoU.prod hoV,⟨hxU,htV⟩,measure_mono_null ?_ hn⟩
    rintro _ ⟨⟨y,v⟩,⟨huy,hvv⟩,hp,rfl⟩
    have he := (hbox (show (y,v)∈A ×ˢ B from ⟨(hU huy).1,hVB hvv⟩)).2.mp hp.2.1
    exact ⟨huy,by simpa only [g,he] using hp.2.2.2⟩
  choose O ho hm hn using chart
  have cover : Z ⊆ ⋃ i : ↥Z, O i := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hm _⟩
  obtain ⟨C,hC,hcov⟩ := (isLindelof_iff_lindelofSpace.mpr (inferInstance : LindelofSpace ↥Z)).elim_countable_subcover O ho cover
  apply measure_mono_null _ ((measure_biUnion_null_iff hC).mpr fun i _ => hn i)
  rintro x ⟨z,hz,rfl⟩
  obtain ⟨i,hi,hh⟩ := by simpa only [mem_iUnion,exists_prop] using hcov hz
  exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,z,⟨hh,hz⟩,rfl⟩⟩

#print axioms projection_simple_root_null
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicTimes
