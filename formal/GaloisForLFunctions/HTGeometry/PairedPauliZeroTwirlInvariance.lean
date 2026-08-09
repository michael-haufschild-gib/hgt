import GaloisForLFunctions.HTGeometry.PauliVisibleQuotientDetectorCanonical
import GaloisForLFunctions.HTGeometry.FinitePauliCharacterProjector

/-!
# Paired-Pauli invariance of doubled Clifford averaging

Averaging over a finite group absorbs right translation of the averaging index, and paired-Pauli
conjugation is realized inside the strict product-Clifford code by the square of the quarter-turn
gate.  Doubled Clifford averaging is therefore unchanged by paired-Pauli conjugation of its input,
as an identity of operators, and its kernel is paired-Pauli invariant.

The canonical nonsinglet layer intersects that kernel with the canonical obstruction, so it inherits
the invariance; exact character projectors then preserve it, and every character component of a
member sum lies in it.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Doubled Clifford averaging absorbs paired-Pauli conjugation**, as an operator identity. -/
theorem finiteProductCliffordTwoReplicaTwirl_comp_pairedPauli (Q : V → Option (Fin 3)) :
    (finiteProductCliffordTwoReplicaTwirlLinear (V := V)).comp
        (finiteTwoReplicaPairedPauliConjugationLinear Q)
      = finiteProductCliffordTwoReplicaTwirlLinear :=
  LinearMap.ext fun X => finiteProductCliffordTwoReplicaTwirl_pairedPauli_input Q X

/-- The identity holds on the empty register, where no nonempty-support argument is available. -/
theorem finiteProductCliffordTwoReplicaTwirl_comp_pairedPauli_empty
    (Q : Fin 0 → Option (Fin 3)) :
    (finiteProductCliffordTwoReplicaTwirlLinear (V := Fin 0)).comp
        (finiteTwoReplicaPairedPauliConjugationLinear Q)
      = finiteProductCliffordTwoReplicaTwirlLinear :=
  finiteProductCliffordTwoReplicaTwirl_comp_pairedPauli Q

/-- **Character projectors preserve the canonical nonsinglet layer.** -/
theorem finiteTwoReplicaPauliCharacterProjector_mem_canonicalHiddenLayer (q : ℕ)
    (P : V → Option (Fin 3)) {X : FiniteTwoReplicaMatrix V}
    (hX : X ∈ canonicalTwoReplicaHiddenLayer V q) :
    finiteTwoReplicaPauliCharacterProjector P X ∈ canonicalTwoReplicaHiddenLayer V q :=
  finiteTwoReplicaPauliCharacterProjector_mem_of_invariant P
    (canonicalTwoReplicaHiddenLayer V q)
    (fun Q => canonicalTwoReplicaHiddenLayer_pairedPauli_invariant q Q) hX

/-- **Every hidden character component is recovered modulo the canonical nonsinglet layer.**  If a
sum of exact character components lies in the layer, so does each component. -/
theorem finiteTwoReplicaPauliCharacter_component_mem_canonicalHiddenLayer (q : ℕ)
    (x : (V → Option (Fin 3)) → FiniteTwoReplicaMatrix V)
    (hx : ∀ R, x R ∈ finiteTwoReplicaPauliCharacterSubspace R)
    (hsum : (∑ R, x R) ∈ canonicalTwoReplicaHiddenLayer V q)
    (P : V → Option (Fin 3)) :
    x P ∈ canonicalTwoReplicaHiddenLayer V q :=
  finiteTwoReplicaPauliCharacter_component_mem_of_sum_mem
    (canonicalTwoReplicaHiddenLayer V q)
    (fun Q => canonicalTwoReplicaHiddenLayer_pairedPauli_invariant q Q) x hx hsum P

end

end GaloisForLFunctions.HTGeometry
