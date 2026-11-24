import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.GaussianCommutant
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.SpectralAlgebra

/-! # Connectivity of physical one-site transitions between two energy sectors -/

open Matrix MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpectralJets.TerminalCrossings
open UntouchedSites FirstGate.Boundary
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- If labels agree across every nonzero matrix entry in two bases, the
two labelled diagonal operators intertwine the original matrix. -/
theorem intertwine_of_entries (V W : unitaryGroup I ℂ) (A : Mat I) (d e : I→ℂ)
    (h : ∀ i j, (star V.val*A*W.val) i j≠0 → d i=e j) :
    spectralFunction V d*A=A*spectralFunction W e := by
  let M := star V.val*A*W.val
  have hd : diagonal d*M=M*diagonal e := by
    ext i j
    rw [diagonal_mul,mul_diagonal]
    by_cases hz : M i j=0
    · simp only [hz,mul_zero,zero_mul]
    · rw [h i j hz,mul_comm]
  have hv (B : Mat I) : V.val*(star V.val*B)=B := by rw [←mul_assoc,V.property.2,one_mul]
  calc spectralFunction V d*A=V.val*(diagonal d*M)*star W.val := by
         change (V.val*diagonal d*star V.val)*A=_
         simp only [M,mul_assoc,W.property.2,mul_one]
       _ = V.val*(M*diagonal e)*star W.val := by rw [hd]
       _ = A*spectralFunction W e := by
         change _=A*(W.val*diagonal e*star W.val)
         simp only [M,mul_assoc,hv]

private theorem labels_of_scalar (V : unitaryGroup I ℂ) (d : I→ℂ) (c : ℂ)
    (h : spectralFunction V d=c • (1:Mat I)) : ∀ i, d i=c := by
  have he : diagonal d=c • (1:Mat I) := by
    apply (Unitary.conjStarAlgAut ℂ _ V).injective
    rw [map_smul,map_one]
    exact h
  intro i
  simpa only [diagonal_apply_eq,Matrix.smul_apply,one_apply_eq,smul_eq_mul,mul_one] using
    congrArg (fun M : Mat I => M i i) he

/-- The bipartite transitions supplied by identity and the three physical
Paulis at any site connect the energy basis to every comparison basis.
Scalar labels are the only ones agreeing across all allowed transitions. -/
theorem gaussian_boundary_transition_labels :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n : ℕ,
      let I := Fin (n+2)→Bool
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      let hH := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)).isHermitian
      let V := hH.eigenvectorUnitary
      ∀ v : Fin (n+2), ∀ W : unitaryGroup I ℂ, ∀ d e : I→ℂ,
        (∀ A : Mat I, A=1 ∨ (∃ a : Fin 3, A=spin v a) →
          ∀ i j, (star V.val*A*W.val) i j≠0 → d i=e j) →
          ∃ c : ℂ, (∀ i, d i=c) ∧ ∀ j, e j=c := by
  filter_upwards [gaussian_one_site_scalar] with ω h n
  intro I H hH V v W d e hentry
  let P := spectralFunction V d
  let Q := spectralFunction W e
  have he : P=Q := by
    simpa only [mul_one,one_mul] using intertwine_of_entries V W 1 d e (hentry 1 (Or.inl rfl))
  have hP : H*P=P*H := by
    have hs : H=spectralFunction V (RCLike.ofReal ∘ hH.eigenvalues) := hH.spectral_theorem
    rw [hs]
    change (Unitary.conjStarAlgAut ℂ _ V) _*(Unitary.conjStarAlgAut ℂ _ V) _=_
    rw [←map_mul]
    change _=(Unitary.conjStarAlgAut ℂ _ V) _*(Unitary.conjStarAlgAut ℂ _ V) _
    rw [←map_mul]
    apply congrArg _
    simp only [diagonal_mul_diagonal]
    exact congrArg diagonal (funext fun i => mul_comm _ _)
  have hp (a : Fin 3) : spin v a*P=P*spin v a := by
    have hh := intertwine_of_entries V W (spin v a) d e (hentry _ (Or.inr ⟨a,rfl⟩))
    change P*spin v a=spin v a*Q at hh
    rw [←he] at hh
    exact hh.symm
  obtain hscalar := h n v P hP hp
  exact ⟨_,labels_of_scalar V d _ hscalar,labels_of_scalar W e _ (he.symm.trans hscalar)⟩

#print axioms gaussian_boundary_transition_labels
end
end GaloisForLFunctions.HTGeometry.SpectralJets.TerminalCrossings
