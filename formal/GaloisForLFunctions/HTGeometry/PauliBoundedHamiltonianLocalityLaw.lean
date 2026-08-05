import GaloisForLFunctions.HTGeometry.PauliTwoLocalEmbedding

/-!
# Generic bounded-weight Pauli Hamiltonians are literally local

The spectral genericity family is realized here as a bundled self-adjoint
Hamiltonian in the same computational basis used by the exact Pauli-transfer
experiment.  Its Pauli coordinates vanish above the prescribed weight.
Thus the generic spectral and permanent operational-locality theorems apply
to one matrix, rather than to unrelated representatives.
-/

open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Literal self-adjoint Hamiltonian obtained by evaluating the numbered
bounded-weight Pauli polynomial family at real coefficients. -/
def pauliBoundedHamiltonian {n q : ℕ}
    (p : Fin (Fintype.card (PauliBoundedLabel n q)) → ℝ) :
    selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) :=
  ⟨(pauliBoundedFinPolynomialMatrix n q).map
      (MvPolynomial.eval₂Hom (RingHom.id ℂ) fun t => (p t : ℂ)),
    isHermitian_pauliBoundedFinEval p⟩

/-- The bundled Hamiltonian is exactly its bounded Pauli expansion. -/
theorem pauliBoundedHamiltonian_eq_sum {n q : ℕ}
    (p : Fin (Fintype.card (PauliBoundedLabel n q)) → ℝ) :
    pauliBoundedHamiltonian p =
      ∑ P : PauliBoundedLabel n q,
        p (pauliBoundedLabelEquivFin n q P) • finitePauliSelfAdjoint P.1 := by
  apply Subtype.ext
  change
    (pauliBoundedFinPolynomialMatrix n q).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) fun t => (p t : ℂ)) =
      ((↑(∑ P : PauliBoundedLabel n q,
        p (pauliBoundedLabelEquivFin n q P) • finitePauliSelfAdjoint P.1) :
          selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)) :
        Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)
  ext x y
  rw [map_eval_pauliBoundedFinPolynomialMatrix,
    eval_pauliBoundedPolynomialMatrix]
  have hcoe :
      ((↑(∑ P : PauliBoundedLabel n q,
          p (pauliBoundedLabelEquivFin n q P) • finitePauliSelfAdjoint P.1) :
        selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)) :
        Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) =
        ∑ P : PauliBoundedLabel n q,
          (↑(p (pauliBoundedLabelEquivFin n q P)) : ℂ) • finitePauliMatrix P.1 := by
    have hsum := map_sum
      (AddSubgroup.subtype (selfAdjoint
        (Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)))
      (fun P : PauliBoundedLabel n q =>
        p (pauliBoundedLabelEquivFin n q P) • finitePauliSelfAdjoint P.1)
      Finset.univ
    change
      ((↑(∑ P : PauliBoundedLabel n q,
        p (pauliBoundedLabelEquivFin n q P) • finitePauliSelfAdjoint P.1) :
          selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)) :
        Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) =
        ∑ P : PauliBoundedLabel n q,
          ((↑(p (pauliBoundedLabelEquivFin n q P) • finitePauliSelfAdjoint P.1) :
            selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)) :
            Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) at hsum
    simpa only [selfAdjoint.val_smul, finitePauliSelfAdjoint,
      ← Complex.coe_smul] using hsum
  rw [hcoe]
  have happ := Matrix.sum_apply x y Finset.univ
    (fun P : PauliBoundedLabel n q =>
      (↑(p (pauliBoundedLabelEquivFin n q P)) : ℂ) • finitePauliMatrix P.1)
  rw [show
    (∑ P : PauliBoundedLabel n q,
      (↑(p (pauliBoundedLabelEquivFin n q P)) : ℂ) • finitePauliMatrix P.1) x y =
      ∑ P : PauliBoundedLabel n q,
        ((↑(p (pauliBoundedLabelEquivFin n q P)) : ℂ) • finitePauliMatrix P.1) x y by
    simpa using happ]
  apply Finset.sum_congr rfl
  intro P _
  rfl

/-- Every Pauli coordinate above the declared weight vanishes. -/
theorem pauliBoundedHamiltonian_repr_eq_zero_of_weight_gt {n q : ℕ}
    (p : Fin (Fintype.card (PauliBoundedLabel n q)) → ℝ)
    (P : Fin n → Option (Fin 3)) (hP : q < finitePauliWeight P) :
    ((finitePauliSelfAdjointBasis (Fin n)).repr (pauliBoundedHamiltonian p) :
      (Fin n → Option (Fin 3)) → ℝ) P = 0 := by
  rw [pauliBoundedHamiltonian_eq_sum, map_sum]
  simp only [map_smul]
  simp_rw [← finitePauliSelfAdjointBasis_apply,
    (finitePauliSelfAdjointBasis (Fin n)).repr_self]
  have hfun := Finsupp.coe_finsetSum Finset.univ
    (fun Q : PauliBoundedLabel n q =>
      p (pauliBoundedLabelEquivFin n q Q) • Finsupp.single Q.1 (1 : ℝ))
  rw [show
    (∑ Q : PauliBoundedLabel n q,
      p (pauliBoundedLabelEquivFin n q Q) • Finsupp.single Q.1 (1 : ℝ)) P =
      ∑ Q : PauliBoundedLabel n q,
        (p (pauliBoundedLabelEquivFin n q Q) • Finsupp.single Q.1 (1 : ℝ)) P by
    have happ := congrFun hfun P
    simpa using happ]
  apply Finset.sum_eq_zero
  intro Q _
  have hne : Q.1 ≠ P := by
    intro h
    subst h
    exact (Nat.not_lt_of_ge Q.2) hP
  simp [hne]

/-- The evaluated polynomial family satisfies the literal Pauli-support
definition of `q`-locality. -/
theorem pauliBoundedHamiltonian_hasPauliWeightAtMost {n q : ℕ}
    (p : Fin (Fintype.card (PauliBoundedLabel n q)) → ℝ) :
    HasPauliWeightAtMost (Fin n) q (pauliBoundedHamiltonian p) := by
  intro P hP
  exact pauliBoundedHamiltonian_repr_eq_zero_of_weight_gt p P hP

/-- Maximal projective independence is invariant under any finite relabeling. -/
theorem MaximallyProjectiveEnergy.comp_equiv
    {I J : Type*} [Fintype I] [Fintype J]
    {energy : I → ℝ} (hmax : MaximallyProjectiveEnergy energy)
    (e : J ≃ I) :
    MaximallyProjectiveEnergy (fun j => energy (e j)) := by
  intro k hbalanced hzero
  let k' : I → ℤ := fun i => k (e.symm i)
  have hbalanced' : SpectralCharacterBalanced k' := by
    unfold SpectralCharacterBalanced at hbalanced ⊢
    have hsum := e.bijective.sum_comp (fun i => k' i)
    have hleft : (∑ j, k' (e j)) = 0 := by
      simpa [k'] using hbalanced
    exact hsum.symm.trans hleft
  have hzero' : (∑ i, (k' i : ℝ) * energy i) = 0 := by
    have hsum := e.bijective.sum_comp
      (fun i => (k' i : ℝ) * energy i)
    have hleft : (∑ j, (k' (e j) : ℝ) * energy (e j)) = 0 := by
      simpa [k'] using hzero
    exact hsum.symm.trans hleft
  have hk' : k' = 0 := hmax k' hbalanced' hzero'
  funext j
  have hj := congrFun hk' (e j)
  simpa [k'] using hj

/-- A maximally projective bounded-weight Pauli Hamiltonian on a nonempty
register cannot be the zero Hamiltonian. -/
theorem pauliBoundedHamiltonian_ne_zero_of_maximallyProjective
    {n q : ℕ} (hn : 0 < n)
    (p : Fin (Fintype.card (PauliBoundedLabel n q)) → ℝ)
    (hmax : MaximallyProjectiveEnergy
      (isHermitian_pauliBoundedFinEval p).eigenvalues) :
    pauliBoundedHamiltonian p ≠ 0 := by
  intro hH
  have hmatrix :
      ((pauliBoundedHamiltonian p :
        selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)) :
        Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) = 0 := by
    exact congrArg Subtype.val hH
  have heigenzero : ∀ x,
      (isHermitian_pauliBoundedFinEval p).eigenvalues x = 0 := by
    intro x
    rw [(isHermitian_pauliBoundedFinEval p).eigenvalues_eq]
    change RCLike.re (dotProduct _
      (((pauliBoundedHamiltonian p :
        selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)) :
        Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) *ᵥ _)) = 0
    rw [hmatrix]
    simp
  let xFalse : FiniteQubitConfiguration (Fin n) := fun _ => false
  let xTrue : FiniteQubitConfiguration (Fin n) := fun _ => true
  have hne : xFalse ≠ xTrue := by
    intro h
    have hi := congrFun h ⟨0, hn⟩
    simp [xFalse, xTrue] at hi
  apply hne
  exact MaximallyProjectiveEnergy.injective hmax (by
    rw [heigenzero xFalse, heigenzero xTrue])

end

end GaloisForLFunctions.HTGeometry
