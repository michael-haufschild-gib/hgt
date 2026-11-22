import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.GaussianChart
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.SpectralLine

/-! # Directional derivative of an actual scalar return date -/
open Filter Set Matrix MeasureTheory Topology Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EntrySensitivity
noncomputable section
open EmptyVisitFlux PrecisionReturns
private abbrev State (n : ℕ) := Fin n→Bool

private theorem arc_relabel {I : Type*} [Fintype I] [DecidableEq I] (x : I→UnitAddCircle) (p : Equiv.Perm I) (r : ℝ) :
    x ∘ p∈enclosingUnitArc r ↔ x∈enclosingUnitArc r := by
  have pull (z : I→UnitAddCircle) (e : Equiv.Perm I) (hz : z∈enclosingUnitArc r) : z ∘ e∈enclosingUnitArc r := by
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    refine mem_iUnion.mpr ⟨e.symm i,?_⟩
    intro j hj
    have hji : e j≠i := fun h => hj (e.apply_eq_iff_eq_symm_apply.mp h)
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hi (e j) hji
  exact ⟨fun h => by simpa only [Function.comp_assoc,Equiv.self_comp_symm,Function.comp_id] using pull (x ∘ p) p.symm h,
    pull x p⟩

private theorem chart_response {n : ℕ} (H Z : selfAdjoint (Register n)) (a ε : ℝ)
    (hε : 0 < ε) (hs : ε < sqrt 2) (hi : Function.Injective H.2.isHermitian.eigenvalues)
    (i j : State n) :
    let E := H.2.isHermitian.eigenvalues
    let w (k : State n) := -E k/(2*π)
    let v := firstVisit H a 0 ε
    let V : Register n := H.2.isHermitian.eigenvectorUnitary
    let d (k : State n) := ((star V*Z.val*V) k k).re
    w j < w i → (∀ᶠ f : State n→ℝ in 𝓝 w,
      IsLeast {t : ℝ | a ≤ t ∧ flow f t∈enclosingUnitArc (SharpOccupation.physicalArc ε)}
        (v*(w i-w j)/(f i-f j))) →
      HasDerivAt (fun z : ℝ => firstVisit (fieldLine H Z z) a 0 ε) (-v*(d i-d j)/(E i-E j)) 0 := by
  intro E w v V d hji hchart
  obtain ⟨g,hg,hder,hspec⟩ := spectral_line_branches H Z hi
  let f (z : ℝ) (k : State n) := -g z k/(2*π)
  have hf0 : f 0=w := by funext k; dsimp only [f,w,E]; rw [hg]
  have hcont : Tendsto f (𝓝 0) (𝓝 w) := by
    rw [←hf0]
    exact tendsto_pi_nhds.mpr fun k => ((hder k).continuousAt.neg.div_const _).tendsto
  have hgap : E i-E j≠0 := sub_ne_zero.mpr fun h => hji.ne (by dsimp only [w]; rw [h])
  have hgap0 : g 0 i-g 0 j≠0 := by rwa [hg]
  have hdiff := (hder i).sub (hder j)
  have hnear : ∀ᶠ z : ℝ in 𝓝 0, g z i-g z j≠0 :=
    hdiff.continuousAt.tendsto.eventually (isOpen_compl_singleton.mem_nhds hgap0)
  have heq : (fun z : ℝ => firstVisit (fieldLine H Z z) a 0 ε) =ᶠ[𝓝 0]
      (fun z => v*(E i-E j)/(g z i-g z j)) := by
    filter_upwards [hspec,hcont.eventually hchart,hnear] with z hz hleast hgz
    obtain ⟨p,hp⟩ := hz
    let K := fieldLine H Z z
    let W (l : State n) := -K.2.isHermitian.eigenvalues l/(2*π)
    have hset : {t : ℝ | a ≤ t ∧ flow (f z) t∈enclosingUnitArc (SharpOccupation.physicalArc ε)} =
        PrecisionReturns.visitSet K a 0 ε := by
      ext t
      have hphase : flow (f z) t=flow W t ∘ p := by
        funext l
        dsimp only [flow,f,W,K,Function.comp_apply]
        rw [hp]
        rfl
      change (_ ∧ _) ↔ (_ ∧ _)
      rw [hphase,arc_relabel]
      exact and_congr_right fun _ => physical_visit K hε hs t
    rw [hset] at hleast
    have ht := (firstVisit_isLeast K a 0 hε).unique hleast
    refine ht.trans ?_
    dsimp only [w,f]
    rw [←sub_div,←sub_div,show -E i- -E j= -(E i-E j) by ring,
      show -g z i- -g z j= -(g z i-g z j) by ring]
    field_simp [hgz,Real.pi_ne_zero]
  have hd := (hasDerivAt_const (0:ℝ) (v*(E i-E j))).div hdiff hgap0
  change HasDerivAt (fun z : ℝ => v*(E i-E j)/(g z i-g z j))
    ((0*(g 0 i-g 0 j)-v*(E i-E j)*(d i-d j))/(g 0 i-g 0 j)^2) 0 at hd
  have h0 : g 0 i-g 0 j=E i-E j := by rw [hg]
  rw [h0,show (0*(E i-E j)-v*(E i-E j)*(d i-d j))/(E i-E j)^2 =
    -v*(d i-d j)/(E i-E j) by field_simp [hgap]; ring] at hd
  exact hd.congr_of_eventuallyEq heq

/-- For every Hermitian field direction the first empty-return derivative
depends on the same two endpoint eigenstates. The difference of their
field expectations is divided by their energy gap. -/
theorem gaussian_first_empty_field_response (ε : ℝ) (hε : 0 < ε) (hs : ε < sqrt 2) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let E := H.2.isHermitian.eigenvalues
      let V : Register N := H.2.isHermitian.eigenvectorUnitary
      ∀ a > (0:ℝ), ε < orbitCircuitDistance H 0 a →
        let v := firstVisit H a 0 ε
        ∃ i j : State N, E i≠E j ∧ ∀ Z : selfAdjoint (Register N),
          HasDerivAt (fun z : ℝ => firstVisit (fieldLine H Z z) a 0 ε)
            (-v*(((star V*Z.val*V) i i).re-((star V*Z.val*V) j j).re)/(E i-E j)) 0 := by
  filter_upwards [gaussian_first_empty_gap_chart ε hε hs,gaussian_path_all_prefixes_maximally_projective] with ω hchart hi
  intro k N H E V a ha hfar v
  obtain ⟨i,j,hji,h⟩ := hchart k a ha hfar
  have hne : E i≠E j := by
    intro he
    change -E j/(2*π) < -E i/(2*π) at hji
    rw [he] at hji
    exact hji.false
  exact ⟨i,j,hne,fun Z => chart_response H Z a ε hε hs (hi k).injective i j hji h⟩

#print axioms gaussian_first_empty_field_response
end
end GaloisForLFunctions.HTGeometry.EntrySensitivity
