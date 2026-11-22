import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.PoleResponses
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! # Two boundary-field settings separate weighted energy sums -/
open Matrix Filter Topology Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq A]

private theorem weighted_second (f : I→ℂ→ℂ) (c : I→ℂ) (hf : ∀ j, AnalyticAt ℂ (f j) 0) :
    deriv (deriv (fun g => ∑ j, c j*f j g)) 0=∑ j, c j*deriv (deriv (f j)) 0 := by
  have hd : deriv (fun g => ∑ j, c j*f j g) =ᶠ[𝓝 0] fun g => ∑ j, c j*deriv (f j) g :=
    (hasDerivAt_analyticCombination f c hf).mono (fun _ h => h.deriv)
  exact hd.deriv_eq.trans (hasDerivAt_analyticCombination_deriv f c hf).deriv

/-- Unequal second-order responses separate the two weighted actions at
every sufficiently small nonzero bond strength. -/
theorem weighted_actions_separate {E : A→ℂ} {M : Matrix A A ℂ} {z w : ℂ}
    (hz : Function.Injective (layerSplitEnergy E z)) (hw : Function.Injective (layerSplitEnergy E w))
    (f g : A×Bool→ℂ→ℂ) (c d : A×Bool→ℂ)
    (hf : ∀ j, AnalyticAt ℂ (f j) 0) (hg : ∀ j, AnalyticAt ℂ (g j) 0)
    (hf₀ : ∀ j, f j 0=layerSplitEnergy E z j) (hg₀ : ∀ j, g j 0=layerSplitEnergy E w j)
    (hfr : ∀ j, ∀ᶠ u in 𝓝 (0:ℂ), matrixCharpolyRelation
      (diagonal (layerSplitEnergy E z)+u • layerCrossPerturbation M,f j u)=0)
    (hgr : ∀ j, ∀ᶠ u in 𝓝 (0:ℂ), matrixCharpolyRelation
      (diagonal (layerSplitEnergy E w)+u • layerCrossPerturbation M,g j u)=0)
    (hne : transverseResponse E M c z≠transverseResponse E M d w) :
    ∀ᶠ u in 𝓝[≠] (0:ℂ), (∑ j, c j*f j u)≠∑ j, d j*g j u := by
  have ha : AnalyticAt ℂ (fun u => ∑ j, c j*f j u) 0 :=
    Finset.analyticAt_fun_sum _ (fun j _ => analyticAt_const.mul (hf j))
  have hb : AnalyticAt ℂ (fun u => ∑ j, d j*g j u) 0 :=
    Finset.analyticAt_fun_sum _ (fun j _ => analyticAt_const.mul (hg j))
  apply (ha.eventually_eq_or_eventually_ne hb).resolve_left
  intro he
  change (fun u => ∑ j, c j*f j u) =ᶠ[𝓝 (0:ℂ)] (fun u => ∑ j, d j*g j u) at he
  have hh := he.deriv.deriv_eq
  rw [weighted_second f c hf,weighted_second g d hg,localExtension_secondDeriv_sum c hz f hf hf₀ hfr,
    localExtension_secondDeriv_sum d hw g hg hg₀ hgr] at hh
  exact hne (mul_left_cancel₀ (by norm_num : (2:ℂ)≠0) hh)

private theorem real_punctured : Tendsto (fun u : ℝ => (u:ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,?_⟩
  · simpa only [Complex.ofReal_zero] using
      ((Complex.continuous_ofReal.continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi (0:ℝ))))
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hu)

/-- For a prescribed regular real field, one other real field makes the
two spectra disagree on every pair in a finite list of weighted actions,
even with arbitrarily small positive real bond strength. -/
theorem separated_real_fields (hcard : 3≤Fintype.card A) {E : A→ℂ} (hE : Function.Injective E)
    (hgap : ∀ a b i j, a≠b → i≠j → E b-E a=E j-E i → (a,b)=(i,j))
    {M : Matrix A A ℂ} (hM : ∀ a b, a≠b → M a b≠0) (c d : I→A×Bool→ℂ)
    (hbal : ∀ j, ∑ i, c j i=0) (hc : ∀ j, c j≠0)
    (w : ℝ) (hw : Function.Injective (layerSplitEnergy E (w:ℂ))) {T : Set ℝ} (hT : T.Infinite) :
    ∃ z ∈ T, ∀ᶠ (u : ℝ) in 𝓝[>] (0:ℝ), ∃ F G : A×Bool→ℂ,
      (∀ i, matrixCharpolyRelation (diagonal (layerSplitEnergy E (z:ℂ))+(u:ℂ) • layerCrossPerturbation M,F i)=0) ∧
      (∀ i, matrixCharpolyRelation (diagonal (layerSplitEnergy E (w:ℂ))+(u:ℂ) • layerCrossPerturbation M,G i)=0) ∧
      Function.Injective F ∧ Function.Injective G ∧ ∀ j, (∑ i, c j i*F i)≠∑ i, d j i*G i := by
  classical
  obtain ⟨_,⟨z,hzT,rfl⟩,hz,ha⟩ := simultaneous_response_escape hcard hE hgap hM c hbal hc
    (fun j => transverseResponse E M (d j) w) (hT.image Complex.ofReal_injective.injOn)
  choose f hf hf₀ hfr using exists_layerSplitBranch hz M
  choose g hg hg₀ hgr using exists_layerSplitBranch hw M
  have hsep := Filter.eventually_all.mpr fun j => weighted_actions_separate hz hw f g (c j) (d j)
    hf hg hf₀ hg₀ hfr hgr (ha j)
  have simple (v : A×Bool→ℂ→ℂ) (hv : ∀ i, AnalyticAt ℂ (v i) 0)
      (hi : Function.Injective (fun i => v i 0)) : ∀ᶠ u in 𝓝 (0:ℂ), Function.Injective (fun i => v i u) := by
    have both (i j : A×Bool) : ∀ᶠ u in 𝓝 (0:ℂ), v i u=v j u → i=j := by
      by_cases h : i=j
      · exact Filter.Eventually.of_forall fun _ _ => h
      · exact (((hv i).continuousAt.ne_iff_eventually_ne (hv j).continuousAt).mp (hi.ne h)).mono fun _ hne he => (hne he).elim
    filter_upwards [Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (both i)] with u hu
    exact fun {i j} => hu i j
  have hsf := simple f hf (fun {i j} hij => hz (by simpa only [hf₀] using hij))
  have hsg := simple g hg (fun {i j} hij => hw (by simpa only [hg₀] using hij))
  have ht := real_punctured.mono_right nhdsWithin_le_nhds
  refine ⟨z,hzT,?_⟩
  filter_upwards [real_punctured.eventually hsep,ht.eventually (Filter.eventually_all.mpr hfr),
    ht.eventually (Filter.eventually_all.mpr hgr),ht.eventually hsf,ht.eventually hsg] with u h hf' hg' hs₁ hs₂
  exact ⟨fun i => f i u,fun i => g i u,hf',hg',hs₁,hs₂,h⟩

#print axioms separated_real_fields
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
