import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.FrozenEnergies
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NullFrequencies

/-! # Conditional absolute continuity of the actions of an unmodified prefix -/

open MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
open PrefixCouplings
noncomputable section

/-- The terminal-field null-set theorem also holds in increasing energy
order. The permutation converting the order may vary with the field. -/
theorem gaussian_ordered_null_frequencies :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ S : Set ℝ, volume S=0 →
      ∀ᵐ z : ℝ, ∀ m : Config k → ℤ, m≠0 → (∑ i, m i)=0 →
        (∑ i, (m i:ℝ)*orderedBoundaryEnergy ω k z i)∉S := by
  filter_upwards [gaussian_boundary_null_frequencies] with ω hω
  intro k S hS
  filter_upwards [hω k S hS] with z hz
  intro m hm hb
  let E := (boundaryHermitian ω k z).eigenvalues
  let e := Fintype.equivFin (Config k)
  let b := (e.trans (Tuple.sort (E ∘ e.symm))).trans e.symm
  let q := m ∘ b.symm
  have hn : q≠0 := by
    intro h
    apply hm
    funext i
    simpa only [q,Function.comp_apply,Equiv.symm_apply_apply,Pi.zero_apply] using congrFun h (b i)
  have hq : (∑ i, q i)=0 := (Equiv.sum_comp b.symm m).trans hb
  have he : (∑ i, (m i:ℝ)*orderedBoundaryEnergy ω k z i) = ∑ i, (q i:ℝ)*E i := by
    have hsort (j : Config k) : orderedBoundaryEnergy ω k z j = E (b j) := rfl
    simp only [hsort]
    simpa only [q,Function.comp_apply,Equiv.symm_apply_apply] using
      Equiv.sum_comp b (fun i => (q i:ℝ)*E i)
  rw [he]
  exact hz q hn hq

/-- On the original draw, a balanced spectral action avoids every measurable
family of null sets selected from all the other coefficients, including
the complete dynamics on every strictly smaller prefix. -/
theorem gaussian_conditional_null (k : ℕ) (S : Set (PathPauliDisorder × ℝ)) (hmS : MeasurableSet S)
    (hS : ∀ η : PathPauliDisorder, volume (Prod.mk η ⁻¹' S)=0) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ m : Config k → ℤ, m≠0 → (∑ i, m i)=0 →
      (eraseTerminal k ω, ∑ i, (m i:ℝ)*orderedBoundaryEnergy ω k 0 i)∉S := by
  classical
  apply ae_all_iff.mpr
  intro m
  by_cases hm : m≠0 ∧ (∑ i, m i)=0
  · let F (ω : PathPauliDisorder) := ∑ i, (m i:ℝ)*orderedBoundaryEnergy ω k 0 i
    have hc : Continuous F :=
      continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_frozen_energy k i)
    let A := (fun ω => (eraseTerminal k ω,F ω)) ⁻¹' Sᶜ
    have hA : MeasurableSet A := hmS.compl.preimage ((continuous_eraseTerminal k).prodMk hc).measurable
    have ha : ∀ᵐ ω ∂pathPauliDisorderLaw, ω∈A := by
      apply ae_of_resampled_coordinate (gaussianReal 0 1) (terminalCoordinate k) A hA
      filter_upwards [gaussian_ordered_null_frequencies] with ω hω
      let i := terminalCoordinate k
      let η := eraseTerminal k ω
      have hac : gaussianReal 0 1 ≪ volume := ProbabilityTheory.gaussianReal_absolutelyContinuous 0 one_ne_zero
      have hshift := (measurePreserving_add_right (volume : Measure ℝ) (-ω i)).quasiMeasurePreserving
      filter_upwards [hac.ae_le (hshift.ae (hω k _ (hS η)))] with y hy
      have he := ordered_congr (boundary_update ω k y 0)
      change (Function.update (Function.update ω i y) i 0,
        ∑ j, (m j:ℝ)*orderedBoundaryEnergy (Function.update ω i y) k 0 j)∉S
      rw [he,Function.update_idem,add_zero]
      have h := hy m hm.1 hm.2
      change (η, ∑ j, (m j:ℝ)*orderedBoundaryEnergy ω k (y + -ω i) j)∉S at h
      change (η, ∑ j, (m j:ℝ)*orderedBoundaryEnergy ω k (y-ω i) j)∉S
      rwa [sub_eq_add_neg]
    exact ha.mono fun _ h _ _ => h
  · exact .of_forall fun _ hn hb => (hm ⟨hn,hb⟩).elim

/-- Relabel the conditional null-set law in the physical eigenbasis.
The permutation may depend on the whole draw. -/
theorem gaussian_native_null (k : ℕ) (S : Set (PathPauliDisorder × ℝ)) (hmS : MeasurableSet S)
    (hS : ∀ η : PathPauliDisorder, volume (Prod.mk η ⁻¹' S)=0) :
    ∀ᵐ ω ∂pathPauliDisorderLaw,
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      ∀ m : Config k → ℤ, m≠0 → (∑ i, m i)=0 → (eraseTerminal k ω, ∑ i, (m i:ℝ)*E i)∉S := by
  filter_upwards [gaussian_conditional_null k S hmS hS] with ω hω
  intro E m hm₀ hb
  obtain ⟨b,hsort⟩ := ordered_at_zero k ω
  let q := m ∘ b
  have hq : q≠0 := by
    intro he
    apply hm₀
    funext i
    simpa only [q,Function.comp_apply,Equiv.apply_symm_apply,Pi.zero_apply] using congrFun he (b.symm i)
  have he : (∑ i, (q i:ℝ)*orderedBoundaryEnergy ω k 0 i)=∑ i, (m i:ℝ)*E i := by
    rw [hsort]
    exact Equiv.sum_comp b (fun i => (m i:ℝ)*E i)
  rw [←he]
  exact hω q hq ((Equiv.sum_comp b m).trans hb)

/-- A forecast that can inspect every other field still has zero
probability of matching a nonzero balanced action exactly. -/
theorem gaussian_predictable_actions (k : ℕ) (g : PathPauliDisorder → ℝ) (hg : Measurable g) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ m : Config k → ℤ, m≠0 → (∑ i, m i)=0 →
      (∑ i, (m i:ℝ)*orderedBoundaryEnergy ω k 0 i) ≠ g (eraseTerminal k ω) := by
  let S := {p : PathPauliDisorder × ℝ | p.2=g p.1}
  have hm : MeasurableSet S := measurableSet_eq_fun measurable_snd (hg.comp measurable_fst)
  have hnull (η : PathPauliDisorder) : volume (Prod.mk η ⁻¹' S)=0 := measure_singleton (g η)
  exact gaussian_conditional_null k S hm hnull

#print axioms gaussian_conditional_null
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
