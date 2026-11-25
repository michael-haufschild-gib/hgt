import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCouplings.TerminalField
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.ProjectiveSlopes

/-! # Ordered energies of an unmodified Gaussian prefix -/

open MeasureTheory ProbabilityTheory Set Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
open PrefixCouplings
noncomputable section

abbrev Config (k : ℕ) := Fin (k+3) → Bool

/-- Remove the last longitudinal coefficient of the indicated prefix. -/
def eraseTerminal (k : ℕ) (ω : PathPauliDisorder) : PathPauliDisorder :=
  Function.update ω (terminalCoordinate k) 0

theorem continuous_eraseTerminal (k : ℕ) : Continuous (eraseTerminal k) := by
  apply continuous_pi
  intro j
  by_cases h : j=terminalCoordinate k
  · subst j
    simpa only [eraseTerminal,Function.update_self] using (continuous_const (y:=(0:ℝ)) :
      Continuous (fun _ : PathPauliDisorder => (0:ℝ)))
  · simpa only [eraseTerminal,Function.update_of_ne h] using
      (continuous_apply j : Continuous (fun ω : PathPauliDisorder => ω j))

private theorem eigenvalues_congr {I : Type} [Fintype I] [DecidableEq I] {A B : Matrix I I ℂ}
    (ha : A.IsHermitian) (hb : B.IsHermitian) (he : A=B) : ha.eigenvalues=hb.eigenvalues := by
  subst B
  rfl

/-- Equal Hermitian matrices have the same ordered energies. -/
theorem ordered_congr {ω η : PathPauliDisorder} {k : ℕ} {z w : ℝ}
    (h : boundaryHamiltonian ω k z=boundaryHamiltonian η k w) :
    orderedBoundaryEnergy ω k z=orderedBoundaryEnergy η k w := by
  have he := eigenvalues_congr (boundaryHermitian ω k z) (boundaryHermitian η k w) h
  let e := Fintype.equivFin (Config k)
  let F (E : Config k → ℝ) (i : Config k) := sortedTuple (E ∘ e.symm) (e i)
  change F (boundaryHermitian ω k z).eigenvalues=F (boundaryHermitian η k w).eigenvalues
  rw [he]

theorem continuous_frozen_energy (k : ℕ) (i : Config k) :
    Continuous (fun ω => orderedBoundaryEnergy ω k 0 i) := by
  let e := Fintype.equivFin (Config k)
  let p : PathPauliDisorder → PathPauliDisorder × ℝ := fun ω => (ω,0)
  have hp : Continuous p := (continuous_id : Continuous (id : PathPauliDisorder → _)).prodMk
    (continuous_const (y:=(0:ℝ)))
  have hc : Continuous (fun ω : PathPauliDisorder => boundaryHamiltonian ω k 0) := by
    change Continuous ((fun z : PathPauliDisorder × ℝ => boundaryHamiltonian z.1 k z.2) ∘ p)
    exact (continuous_boundary_draw k).comp hp
  have hG : Continuous (fun ω => Matrix.reindex e e (boundaryHamiltonian ω k 0)) :=
    continuous_pi fun j => continuous_pi fun l =>
      (continuous_apply (e.symm l)).comp ((continuous_apply (e.symm j)).comp hc)
  have hh := continuous_sortedTuple_eigenvalues hG (fun ω => (boundaryHermitian ω k 0).reindex e)
  exact ((continuous_apply (e i)).comp hh).congr fun ω =>
    congrFun (sortedTuple_eigenvalues_reindex e (boundaryHermitian ω k 0)) (e i)

/-- The ordered energies at zero field increment are the original physical
energies after a permutation, including when levels repeat. -/
theorem ordered_at_zero (k : ℕ) (ω : PathPauliDisorder) :
    ∃ b : Equiv.Perm (Config k), orderedBoundaryEnergy ω k 0 =
      (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues ∘ b := by
  let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
  let e := Fintype.equivFin (Config k)
  let b := (e.trans (Tuple.sort (E ∘ e.symm))).trans e.symm
  refine ⟨b,?_⟩
  have h : boundaryHamiltonian ω k 0=pathHamiltonian (pathPauliDisorderShell ω (k+1)) := by
    simp only [boundaryHamiltonian,Complex.ofReal_zero,zero_smul,add_zero]
  have hv := eigenvalues_congr (boundaryHermitian ω k 0)
    (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian h
  change (boundaryHermitian ω k 0).eigenvalues=E at hv
  funext j
  change sortedTuple ((boundaryHermitian ω k 0).eigenvalues ∘ e.symm) (e j)=E (b j)
  rw [hv]
  rfl

#print axioms continuous_frozen_energy
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
