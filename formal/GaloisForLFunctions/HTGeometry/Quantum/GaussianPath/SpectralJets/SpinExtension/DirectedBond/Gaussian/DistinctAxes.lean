import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Gaussian.Labels

/-! # Each directed control is distinguished by the site carrying its X -/
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

private theorem terminal_X (n : ℕ) (j : Fin (n+1)) :
    (terminalLabel n 0).1 j=some 0 ↔ j=Fin.last n := by
  refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [terminalLabel,pauliIdentityLabel]

private theorem edge_X (n : ℕ) (i : Fin n) (j : Fin (n+1)) :
    (edgeLabel n i).1 j=some 0 ↔ j=i.castSucc := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun a => ?_) i
    · refine Fin.lastCases ?_ (fun b => ?_) j
      · simp [edgeLabel,lastBondLabel,show (2:Fin 3)≠0 by decide]
      · simp only [edgeLabel,Fin.lastCases_last,lastBondLabel,Fin.snoc_castSucc,terminal_X,
          Fin.castSucc_inj]
    · refine Fin.lastCases ?_ (fun b => ?_) j
      · simp [edgeLabel,liftedLabel]
      · simp only [edgeLabel,Fin.lastCases_castSucc,liftedLabel,Fin.snoc_castSucc,ih,
          Fin.castSucc_inj]

theorem fieldLabel_X (n : ℕ) (i j : Fin (n+1)) : (fieldLabels n i).1 j=some 0 ↔ j=i := by
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simpa only [fieldLabels,Fin.snoc_last] using terminal_X n j
  · simpa only [fieldLabels,Fin.snoc_castSucc] using edge_X n a j

/-- The N perturbations are N distinct Pauli coefficients. -/
theorem fieldLabels_injective (n : ℕ) : Function.Injective (fieldLabels n) := by
  intro i j h
  apply (fieldLabel_X n j i).mp
  rw [←h]
  exact (fieldLabel_X n i i).mpr rfl

#print axioms fieldLabels_injective
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
