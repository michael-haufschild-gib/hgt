import GaloisForLFunctions.HTGeometry.TwoReplicaPauliVisibleQuotientDetector
import GaloisForLFunctions.HTGeometry.CanonicalTwoReplicaObstruction

/-!
# The aggregate quotient detector at the canonical obstruction

The abstract detector law holds for any zero-character source and any paired-Pauli invariant
target.  Its concrete layer names both: the source is the swap-invariant sector of the canonical
two-replica Hall obstruction, and the target is that obstruction's zero-product-Clifford-twirl
layer.

Product-Clifford covariance makes the obstruction paired-Pauli invariant and the strict half-turn
identity makes the twirl kernel invariant, so both premises are discharged and the detector law
holds outright.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The hidden layer: the zero-product-Clifford-twirl part of the canonical obstruction. -/
def canonicalTwoReplicaHiddenLayer (σ : Type*) [Fintype σ] [DecidableEq σ] (q : ℕ) :
    Submodule ℂ (FiniteTwoReplicaMatrix σ) :=
  canonicalTwoReplicaQLocalObstruction σ q ⊓
    LinearMap.ker (finiteProductCliffordTwoReplicaTwirlLinear (V := σ))

/-- The visible source: the swap-invariant sector of the canonical obstruction. -/
def canonicalTwoReplicaVisibleSource (σ : Type*) [Fintype σ] [DecidableEq σ] (q : ℕ) :
    Submodule ℂ (FiniteTwoReplicaMatrix σ) :=
  canonicalTwoReplicaQLocalObstruction σ q ⊓
    LinearMap.range (finiteTwoReplicaSwapInvariantEmbed (V := σ))

/-- **The hidden layer is paired-Pauli invariant**, unconditionally. -/
theorem canonicalTwoReplicaHiddenLayer_pairedPauli_invariant (q : ℕ)
    (Q : σ → Option (Fin 3)) :
    (canonicalTwoReplicaHiddenLayer σ q).map
        (finiteTwoReplicaPairedPauliConjugationLinear Q)
      ≤ canonicalTwoReplicaHiddenLayer σ q :=
  finiteTwoReplicaQLocal_greatestMaximizer_zeroTwirl_pairedPauli_invariant q
    (canonicalTwoReplicaQLocalObstruction σ q)
    (fun W hW => le_canonicalTwoReplicaQLocalObstruction q W hW) Q

/-- **The visible source has exact zero paired-Pauli character**, unconditionally. -/
theorem canonicalTwoReplicaVisibleSource_le_zeroCharacter (q : ℕ) :
    canonicalTwoReplicaVisibleSource σ q ≤
      finiteTwoReplicaPauliCharacterSubspace (pauliCharacterZero (σ := σ)) :=
  finiteTwoReplicaQLocal_greatestMaximizer_swapSector_le_zeroCharacter
    (canonicalTwoReplicaQLocalObstruction σ q)

/-- **Exact hidden-kernel classification at the canonical layer.**  The single aggregate detector
vanishes exactly when every individual cutoff collective commutator of the source vector already
lies in the hidden layer. -/
theorem finiteTwoReplicaPauliVisibleQuotientDetector_canonical_mem_ker_iff (q : ℕ)
    (x : canonicalTwoReplicaVisibleSource σ q) :
    x ∈ LinearMap.ker (finiteTwoReplicaPauliVisibleQuotientDetector q
        (canonicalTwoReplicaVisibleSource σ q) (canonicalTwoReplicaHiddenLayer σ q))
      ↔ ∀ P : σ → Option (Fin 3),
          finiteTwoReplicaPauliCutoffCollective σ q P x
            ∈ canonicalTwoReplicaHiddenLayer σ q :=
  finiteTwoReplicaPauliVisibleQuotientDetector_mem_ker_iff q
    (canonicalTwoReplicaVisibleSource σ q) (canonicalTwoReplicaHiddenLayer σ q)
    (canonicalTwoReplicaVisibleSource_le_zeroCharacter q)
    (fun Q => canonicalTwoReplicaHiddenLayer_pairedPauli_invariant q Q) x

end

end GaloisForLFunctions.HTGeometry
