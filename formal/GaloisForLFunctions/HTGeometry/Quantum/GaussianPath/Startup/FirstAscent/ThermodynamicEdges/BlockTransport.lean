import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.BlockWidths
import GaloisForLFunctions.HTGeometry.SiteFactorQubitPauliWeightLaw
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Subregister.Lift

/-! # Independence of spectral diameter from register padding -/
open Matrix Set Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
noncomputable section

variable {L N : ℕ}

/-- Extending a Pauli word by identities gives its supported register action. -/
theorem place_pauli (S : Finset (Fin N)) (e : Fin L ≃ S) (p : Fin L → Option (Fin 3)) :
    Subregister.place e (finitePauliMatrix p)=finitePauliMatrix (extendPacketPauliLabel S (p ∘ e.symm)) := by
  unfold Subregister.place
  rw [←liftLocalMatrix_finitePauliMatrix]
  congr 1
  ext x y
  change (∏ i, boolPauliOptionEntry (p i) (x (e i),y (e i))) =
    ∏ j, boolPauliOptionEntry (p (e.symm j)) (x j,y j)
  exact Fintype.prod_equiv e _ _ (fun i => by rw [Equiv.symm_apply_apply])

private theorem maximum_of_range {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    {f : I→ℝ} {g : J→ℝ} (h : range f ⊆ range g) :
    univ.sup' univ_nonempty f≤univ.sup' univ_nonempty g := by
  apply sup'_le
  intro i _
  obtain ⟨j,hj⟩ := h (mem_range_self i)
  exact hj ▸ le_sup' g (mem_univ j)

private theorem minimum_of_range {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    {f : I→ℝ} {g : J→ℝ} (h : range f ⊆ range g) :
    univ.inf' univ_nonempty g≤univ.inf' univ_nonempty f := by
  apply le_inf'
  intro i _
  obtain ⟨j,hj⟩ := h (mem_range_self i)
  exact hj ▸ inf'_le g (mem_univ j)

/-- A copied local Hamiltonian keeps both energy edges in the larger register. -/
theorem place_width (S : Finset (Fin N)) (e : Fin L ≃ S)
    (B : selfAdjoint (Register L)) (H : selfAdjoint (Register N)) (he : H.val=Subregister.place e B.val) :
    circuitHamiltonianSpectralWidth H=circuitHamiltonianSpectralWidth B := by
  let q := Equiv.arrowCongr e (Equiv.refl Bool)
  have hr : range H.2.isHermitian.eigenvalues=range B.2.isHermitian.eigenvalues := by
    obtain ⟨X,hX⟩ := H
    change X=Subregister.place e B.val at he
    subst X
    exact (range_eigenvalues_liftLocalMatrix S (isHermitian_reindex q B.2.isHermitian)).trans
      (range_eigenvalues_reindex q B.2.isHermitian)
  exact congrArg₂ (·-·) (le_antisymm (maximum_of_range hr.subset) (maximum_of_range hr.symm.subset))
    (le_antisymm (minimum_of_range hr.symm.subset) (minimum_of_range hr.subset))

#print axioms place_width
end
end GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
