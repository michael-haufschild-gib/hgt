import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.AnalyticFibers
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.JointFrequencies

/-! # Maximal projective rank of the first derivatives in one physical direction -/
open MeasureTheory Set Filter Topology Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section
private abbrev Basis (k : ℕ) := Fin (k+3)→Bool

/-- Canonically ordered energies on the terminal-field line, expressed
on the original register index. -/
def orderedBoundaryEnergy (ω : PathPauliDisorder) (k : ℕ) (z : ℝ) (i : Basis k) : ℝ :=
  sortedFieldLevels (fun u => (boundaryHermitian ω k u).eigenvalues) z (Fintype.equivFin _ i)

/-- Ordered energies vary continuously even at a collision of labels. -/
theorem continuous_orderedBoundaryEnergy (ω : PathPauliDisorder) (k : ℕ) (i : Basis k) :
    Continuous (fun z => orderedBoundaryEnergy ω k z i) := by
  let e := Fintype.equivFin (Basis k)
  have hc : Continuous (boundaryHamiltonian ω k) :=
    continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  have hG : Continuous (fun z => Matrix.reindex e e (boundaryHamiltonian ω k z)) := by
    exact continuous_pi fun j => continuous_pi fun l =>
      (continuous_apply (e.symm l)).comp ((continuous_apply (e.symm j)).comp hc)
  have hh := continuous_sortedTuple_eigenvalues hG (fun z => (boundaryHermitian ω k z).reindex e)
  exact ((continuous_apply (e i)).comp hh).congr fun z =>
    congrFun (sortedTuple_eigenvalues_reindex e (boundaryHermitian ω k z)) (e i)

/-- Outside countably many baseline fields, the energies and their first
derivatives in the single terminal-Z direction both have full rational
projective rank. -/
theorem gaussian_boundary_projective_slopes :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∃ B : Set ℝ, B.Countable ∧ ∀ z ∉ B,
      let E := orderedBoundaryEnergy ω k
      MaximallyProjectiveEnergy (E z) ∧ (∀ i, AnalyticAt ℝ (fun u => E u i) z) ∧
        MaximallyProjectiveEnergy (fun i => deriv (fun u => E u i) z) := by
  filter_upwards [gaussian_integer_action_levels,gaussian_boundary_joint_nonresonance] with ω hfin hnr
  intro k
  let E (z : ℝ) := (boundaryHermitian ω k z).eigenvalues
  let e := Fintype.equivFin (Basis k)
  let b (z : ℝ) := (e.trans (Tuple.sort (E z ∘ e.symm))).trans e.symm
  let F := orderedBoundaryEnergy ω k
  let U := {z : ℝ | Function.Injective (E z)}
  have hc : Continuous (boundaryHamiltonian ω k) := continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  have ho : IsOpen U := by
    simpa only [U,E,compl_setOf,not_not] using (isClosed_repeatedSpectrum hc (boundaryHermitian ω k)).isOpen_compl
  have hZ : (SpinExtension.lastPauli (k+2) 2).IsHermitian := by
    rw [SpinExtension.lastPauli_word]
    exact finitePauliMatrix_isHermitian _
  have ha (i : Basis k) : AnalyticOnNhd ℝ (fun t => F t i) U := fun z hz =>
    sortedFieldLevels_analytic (isSelfAdjoint_pathHamiltonian _).isHermitian hZ (boundaryHermitian ω k) hz (e i)
  let M := {m : Basis k→ℤ // m≠0 ∧ (∑ i, m i)=0}
  let f (m : M) (z : ℝ) := ∑ i, (m.val i:ℝ)*F z i
  let C (m : M) := {z ∈ U | deriv (f m) z=0}
  have hC (m : M) : (C m).Countable := by
    apply countable_critical_of_finite_levels ho
    · exact fun z hz => Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul (ha i z hz)
    · intro c
      exact (hfin k m.val m.property.1 m.property.2 c).subset fun z hz => Or.inr ⟨b z,hz.2⟩
  obtain ⟨B,hB,hn⟩ := hnr k
  refine ⟨B∪⋃ m : M, C m,hB.union (countable_iUnion hC),?_⟩
  intro z hz _
  have hi : MaximallyProjectiveEnergy (E z) := by
    intro m hbal hsum
    exact (hn z (fun h => hz (Or.inl h)) 0 m (by simp) hbal (by simpa using hsum)).2
  have hU : z∈U := hi.injective
  refine ⟨hi.comp_equiv (b z),fun i => ha i z hU,?_⟩
  intro m hb hsum
  by_contra hm
  let p : M := ⟨m,hm,hb⟩
  have hd : HasDerivAt (f p) (∑ i, (m i:ℝ)*deriv (fun u => F u i) z) z :=
    HasDerivAt.fun_sum fun i _ => ((ha i z hU).differentiableAt.hasDerivAt.const_mul (m i:ℝ))
  exact hz (Or.inr (mem_iUnion.mpr ⟨p,hU,hd.deriv.trans hsum⟩))

#print axioms gaussian_boundary_projective_slopes
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
