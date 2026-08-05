import GaloisForLFunctions.HTGeometry.ArbitraryGraphLocalHamiltonianGenericityLaw

/-!
# Relabelling the physical carrier of a spectral realization

A physical realization of a packaged spectral system is diagonalized by a
rectangular unitary eigenbasis.  Relabelling the physical index type along an
equivalence carries the eigenbasis, the Hamiltonian and every probe along with
it and leaves the spectral system — hence every spectral conclusion — untouched.

This is what lets a network induction move its carrier between the nested
product produced by successive leaf attachments and the site product
`∀ v, A v` on which subsystem locality is expressed.
-/

open scoped Matrix BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- **Relabelled carriers keep maximal projective rank.**  Relabelling the
physical index type of a realization transports its eigenbasis, Hamiltonian and
probes without touching the packaged spectral system, so the relabelled
Hamiltonian still has maximally projective spectrum. -/
theorem reindex_hamiltonian_maximallyProjective
    (X : GoodObserverSpectralSystem.{u})
    (R : @GoodObserverSpectralSystem.PhysicalRealization
      X X.stateFintype X.stateDecidableEq)
    {Q : Type u} [Fintype Q] [DecidableEq Q] :
    letI : Fintype X.State := X.stateFintype
    letI : DecidableEq X.State := X.stateDecidableEq
    letI : Fintype R.PhysicalState := R.physicalFintype
    letI : DecidableEq R.PhysicalState := R.physicalDecidableEq
    ∀ (e : R.PhysicalState ≃ Q)
      (hHermitian : (Matrix.reindex e e R.hamiltonian).IsHermitian),
      MaximallyProjectiveEnergy hHermitian.eigenvalues := by
  letI : Fintype X.State := X.stateFintype
  letI : DecidableEq X.State := X.stateDecidableEq
  letI : Fintype R.PhysicalState := R.physicalFintype
  letI : DecidableEq R.PhysicalState := R.physicalDecidableEq
  intro e hHermitian
  refine
    letI R' : @GoodObserverSpectralSystem.PhysicalRealization
        X X.stateFintype X.stateDecidableEq :=
      { PhysicalState := Q
        physicalFintype := inferInstance
        physicalDecidableEq := inferInstance
        basis := R.basis.submatrix e.symm id
        star_basis_mul_basis := ?_
        basis_mul_star_basis := ?_
        hamiltonian := Matrix.reindex e e R.hamiltonian
        hamiltonian_eq_diagonal := ?_
        physicalProbe := fun s q => Matrix.reindex e e (R.physicalProbe s q)
        transition_eq_coordinate := ?_ }
    ?_
  · rw [Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv R.basisᴴ R.basis id e.symm id,
      R.star_basis_mul_basis]
    rfl
  · show R.basis.submatrix (⇑e.symm) (⇑(Equiv.refl X.State)) *
        (R.basis.submatrix (⇑e.symm) (⇑(Equiv.refl X.State)))ᴴ = 1
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      R.basis_mul_star_basis, Matrix.submatrix_one_equiv]
  · show Matrix.reindex e e R.hamiltonian =
      R.basis.submatrix (⇑e.symm) (⇑(Equiv.refl X.State)) *
        Matrix.diagonal (fun i => (X.energy i : ℂ)) *
        (R.basis.submatrix (⇑e.symm) (⇑(Equiv.refl X.State)))ᴴ
    rw [Matrix.conjTranspose_submatrix]
    rw [show Matrix.diagonal (fun i => (X.energy i : ℂ)) =
        (Matrix.diagonal (fun i => (X.energy i : ℂ))).submatrix
          (⇑(Equiv.refl X.State)) id from rfl]
    rw [Matrix.submatrix_mul_equiv R.basis
      (Matrix.diagonal (fun i => (X.energy i : ℂ))) (⇑e.symm)
      (Equiv.refl X.State) id]
    rw [show ((R.basis * Matrix.diagonal (fun i => (X.energy i : ℂ))).submatrix
        (⇑e.symm) id) =
      (R.basis * Matrix.diagonal (fun i => (X.energy i : ℂ))).submatrix
        (⇑e.symm) (⇑(Equiv.refl X.State)) from rfl]
    rw [Matrix.submatrix_mul_equiv
      (R.basis * Matrix.diagonal (fun i => (X.energy i : ℂ)))
      R.basisᴴ (⇑e.symm) (Equiv.refl X.State) (⇑e.symm)]
    show R.hamiltonian.submatrix (⇑e.symm) (⇑e.symm) = _
    rw [R.hamiltonian_eq_diagonal]
  · intro s q
    show X.transition s q =
      (R.basis.submatrix (⇑e.symm) id)ᴴ *
        Matrix.reindex e e (R.physicalProbe s q) *
        R.basis.submatrix (⇑e.symm) id
    rw [Matrix.conjTranspose_submatrix]
    show X.transition s q =
      R.basisᴴ.submatrix id (⇑e.symm) *
        (R.physicalProbe s q).submatrix (⇑e.symm) (⇑e.symm) *
        R.basis.submatrix (⇑e.symm) id
    rw [Matrix.submatrix_mul_equiv R.basisᴴ (R.physicalProbe s q)
        id e.symm (⇑e.symm),
      Matrix.submatrix_mul_equiv (R.basisᴴ * R.physicalProbe s q)
        R.basis id e.symm id]
    exact R.transition_eq_coordinate s q
  · rename_i R'
    have hmax :=
      GoodObserverSpectralSystem.PhysicalRealization.hamiltonianEigenvalues_maximallyProjective
        X R'
    have heq :
        (GoodObserverSpectralSystem.PhysicalRealization.hamiltonian_isHermitian
          X R').eigenvalues = hHermitian.eigenvalues := by
      apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        (GoodObserverSpectralSystem.PhysicalRealization.hamiltonian_isHermitian
          X R') hHermitian).2
      rfl
    rwa [heq] at hmax

end

end GaloisForLFunctions.HTGeometry
