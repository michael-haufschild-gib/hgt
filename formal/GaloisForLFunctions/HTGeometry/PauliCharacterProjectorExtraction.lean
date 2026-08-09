import GaloisForLFunctions.HTGeometry.FinitePauliCharacterProjector
import GaloisForLFunctions.HTGeometry.PauliTwoLocalLabels

/-!
# Trivial-label conjugation and the empty register

The Pauli string of the all-identity label is the identity matrix, so conjugating by it does
nothing.  On an empty register that is the only label: there is a single paired-Pauli character and
its projector is the identity map, with no orthogonality argument left to make.

The projector's action on an invariant subspace is also recorded as a submodule inequality, which
is the form the extraction step is stated in.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The all-identity Pauli string is the identity matrix. -/
theorem finitePauliMatrix_const_none :
    finitePauliMatrix (fun _ : σ => (none : Option (Fin 3))) = 1 := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst hxy
    rw [Matrix.one_apply_eq]
    refine Finset.prod_eq_one fun s _ => ?_
    rw [boolPauliOptionEntry_none, if_pos rfl]
  · rw [Matrix.one_apply_ne hxy]
    obtain ⟨s, hs⟩ : ∃ s, x s ≠ y s := Function.ne_iff.mp hxy
    refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
    rw [boolPauliOptionEntry_none, if_neg hs]

/-- Conjugation by the all-identity paired Pauli is the identity map. -/
theorem finiteTwoReplicaPairedPauliConjugationLinear_const_none :
    finiteTwoReplicaPairedPauliConjugationLinear (fun _ : σ => (none : Option (Fin 3)))
      = LinearMap.id := by
  have hone : finiteTwoReplicaPairedPauli (fun _ : σ => (none : Option (Fin 3))) = 1 := by
    rw [finiteTwoReplicaPairedPauli, finitePauliMatrix_const_none,
      Matrix.one_kronecker_one]
  refine LinearMap.ext fun X => ?_
  change finiteTwoReplicaPairedPauli (fun _ : σ => (none : Option (Fin 3))) * X *
      finiteTwoReplicaPairedPauli (fun _ : σ => (none : Option (Fin 3))) = X
  rw [hone, Matrix.one_mul, Matrix.mul_one]

/-- The empty register carries exactly one paired-Pauli character. -/
theorem card_pauliLabel_of_isEmpty [IsEmpty σ] :
    Fintype.card (σ → Option (Fin 3)) = 1 :=
  Fintype.card_eq_one_iff.mpr ⟨fun _ => none, fun _ => Subsingleton.elim _ _⟩

/-- **On the empty register the character projector is the identity.** -/
theorem finiteTwoReplicaPauliCharacterProjector_of_isEmpty [IsEmpty σ]
    (P : σ → Option (Fin 3)) :
    finiteTwoReplicaPauliCharacterProjector P = LinearMap.id := by
  classical
  have hsign : finitePauliConjugationSign (fun _ : σ => (none : Option (Fin 3))) P = 1 := by
    rw [finitePauliConjugationSign]
    simp
  rw [finiteTwoReplicaPauliCharacterProjector, Fintype.card_eq_zero, pow_zero, inv_one,
    one_smul, Finset.sum_eq_single (fun _ : σ => (none : Option (Fin 3)))]
  · rw [finiteTwoReplicaPairedPauliConjugationLinear_const_none, hsign, one_smul]
  · intro Q _ hQ
    exact absurd (Subsingleton.elim Q _) hQ
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **A character projector maps an invariant subspace into itself.** -/
theorem finiteTwoReplicaPauliCharacterProjector_map_le_of_invariant
    (P : σ → Option (Fin 3)) (U : Submodule ℂ (FiniteTwoReplicaMatrix σ))
    (hU : ∀ Q : σ → Option (Fin 3),
      U.map (finiteTwoReplicaPairedPauliConjugationLinear Q) ≤ U) :
    U.map (finiteTwoReplicaPauliCharacterProjector P) ≤ U := by
  rintro _ ⟨X, hX, rfl⟩
  exact finiteTwoReplicaPauliCharacterProjector_mem_of_invariant P U hU hX

end

end GaloisForLFunctions.HTGeometry
