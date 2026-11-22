import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.AnalyticFibers
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.GaussianActions

/-! # Absolute continuity of actions under one continuously distributed terminal field -/
open MeasureTheory Set Filter Matrix Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section

private theorem null_action {I : Type*} [Fintype I] [DecidableEq I] {A Z : Matrix I I ℂ}
    (ha : A.IsHermitian) (hz : Z.IsHermitian) (hH : ∀ t : ℝ, (A+(t:ℂ) • Z).IsHermitian)
    (m : I→ℤ) (hfin : ∀ c : ℝ, {t : ℝ | ¬Function.Injective (hH t).eigenvalues ∨
      ∃ σ : Equiv.Perm I, (∑ i, (m i:ℝ)*(hH t).eigenvalues (σ i))=c}.Finite)
    (S : Set ℝ) (hS : volume S=0) :
    volume {t : ℝ | (∑ i, (m i:ℝ)*(hH t).eigenvalues i)∈S}=0 := by
  let E (t : ℝ) := (hH t).eigenvalues
  let V := {t : ℝ | ¬Function.Injective (E t)}
  have hV : V.Finite := (hfin 0).subset fun _ ht => Or.inl ht
  let e := Fintype.equivFin I
  let b (t : ℝ) : Equiv.Perm I := (e.trans (Tuple.sort (E t ∘ e.symm))).trans e.symm
  let f (σ : Equiv.Perm I) (t : ℝ) := ∑ i, (m i:ℝ)*sortedFieldLevels E t (e (σ i))
  have hnull (σ : Equiv.Perm I) : volume (f σ ⁻¹' S ∩ Vᶜ)=0 := by
    apply null_preimage_of_finite_levels hV.isClosed.isOpen_compl _ _ S hS
    · intro t ht
      have hi : Function.Injective (E t) := not_not.mp ht
      exact Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul (sortedFieldLevels_analytic ha hz hH hi _)
    · intro c
      exact (hfin c).subset fun t ht => Or.inr ⟨σ.trans (b t),ht.2⟩
  apply measure_mono_null _ (measure_union_null (hV.countable.measure_zero volume) (measure_iUnion_null hnull))
  intro t ht
  by_cases hv : t∈V
  · exact Or.inl hv
  · apply Or.inr
    refine mem_iUnion.mpr ⟨(b t).symm,?_,hv⟩
    change (∑ i, (m i:ℝ)*E t (b t ((b t).symm i)))∈S
    change (∑ i, (m i:ℝ)*E t i)∈S at ht
    simpa only [Equiv.apply_symm_apply] using ht

/-- On each typical Gaussian prefix a null frequency set, selected even after
the other couplings are known, misses all nonzero balanced integer actions
for almost every value of the single terminal field. -/
theorem gaussian_boundary_null_frequencies :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ S : Set ℝ, volume S=0 →
      ∀ᵐ z : ℝ, ∀ m : (Fin (k+3)→Bool)→ℤ, m≠0 → (∑ i, m i)=0 →
        (∑ i, (m i:ℝ)*(boundaryHermitian ω k z).eigenvalues i)∉S := by
  filter_upwards [gaussian_integer_action_levels] with ω hω
  intro k S hS
  apply ae_all_iff.mpr
  intro m
  by_cases hm : m=0
  · exact .of_forall fun _ hn => (hn hm).elim
  by_cases hb : (∑ i, m i)=0
  · have hZ : (SpinExtension.lastPauli (k+2) 2).IsHermitian := by
      rw [SpinExtension.lastPauli_word]
      exact finitePauliMatrix_isHermitian _
    let bad := {z : ℝ | (∑ i, (m i:ℝ)*(boundaryHermitian ω k z).eigenvalues i)∈S}
    have h : volume bad=0 := null_action
      (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian
      hZ (boundaryHermitian ω k) m (hω k m hm hb) S hS
    have hh : ∀ᵐ z : ℝ, z∉bad := measure_eq_zero_iff_ae_notMem.mp h
    exact hh.mono fun _ hz _ _ => hz
  · exact .of_forall fun _ _ hs => (hb hs).elim

#print axioms gaussian_boundary_null_frequencies
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
