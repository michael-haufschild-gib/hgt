import Mathlib

/-!
# Minimal replica height of a projective spectral character

A fidelity `n`-replica expansion contains characters obtained by choosing
`n` positive and `n` negative energy labels, with repetition.  This file
identifies the exact minimum replica order of every balanced integer
character: it is the total positive coefficient mass.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- Total positive coefficient mass of an integer spectral character. -/
def spectralCharacterPositiveMass
    {I : Type*} [Fintype I] (k : I → ℤ) : ℕ :=
  ∑ i, (k i).toNat

/-- Projective, or balanced, spectral character: total coefficient zero. -/
def SpectralCharacterBalanced
    {I : Type*} [Fintype I] (k : I → ℤ) : Prop :=
  ∑ i, k i = 0

/-- Multiplicity form of realization by an `n`-replica fidelity moment.
The functions `p` and `q` record positive- and negative-phase label
multiplicities. -/
def SpectralCharacterReplicaRealizes
    {I : Type*} [Fintype I]
    (n : ℕ) (k : I → ℤ) : Prop :=
  ∃ p q : I → ℕ,
    (∑ i, p i) = n ∧
    (∑ i, q i) = n ∧
    ∀ i, k i = (p i : ℤ) - (q i : ℤ)

/-- Every replica realization has order at least the positive coefficient
mass of the character. -/
theorem spectralCharacterPositiveMass_le_of_replicaRealizes
    {I : Type*} [Fintype I]
    {n : ℕ} {k : I → ℤ}
    (h : SpectralCharacterReplicaRealizes n k) :
    spectralCharacterPositiveMass k ≤ n := by
  rcases h with ⟨p, q, hp, hq, hk⟩
  rw [← hp]
  unfold spectralCharacterPositiveMass
  apply Finset.sum_le_sum
  intro i hi
  rw [hk i]
  omega

/-- A balanced character has equal total positive and negative
coefficient masses. -/
theorem sum_toNat_eq_sum_neg_toNat_of_spectralCharacterBalanced
    {I : Type*} [Fintype I]
    {k : I → ℤ} (hk : SpectralCharacterBalanced k) :
    (∑ i, (k i).toNat) = ∑ i, (-k i).toNat := by
  have hsum :
      (∑ i, k i) =
        ((∑ i, (k i).toNat : ℕ) : ℤ) -
          ((∑ i, (-k i).toNat : ℕ) : ℤ) := by
    calc
      (∑ i, k i) =
          ∑ i, (((k i).toNat : ℤ) -
            ((-k i).toNat : ℤ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (k i).toNat_sub_toNat_neg.symm
      _ = ((∑ i, (k i).toNat : ℕ) : ℤ) -
          ((∑ i, (-k i).toNat : ℕ) : ℤ) := by
        rw [Finset.sum_sub_distrib]
        norm_cast
  rw [hk] at hsum
  omega

/-- Every balanced character is realized at its positive coefficient
mass. -/
theorem spectralCharacterReplicaRealizes_positiveMass_of_balanced
    {I : Type*} [Fintype I]
    {k : I → ℤ} (hk : SpectralCharacterBalanced k) :
    SpectralCharacterReplicaRealizes
      (spectralCharacterPositiveMass k) k := by
  refine
    ⟨fun i => (k i).toNat, fun i => (-k i).toNat, rfl, ?_, ?_⟩
  · exact
      (sum_toNat_eq_sum_neg_toNat_of_spectralCharacterBalanced hk).symm
  · intro i
    exact (k i).toNat_sub_toNat_neg.symm

/-- **Exact minimum-replica law.** For every balanced integer spectral
character, positive coefficient mass is both achievable and a lower bound
for every fidelity-replica realization. -/
theorem spectralCharacterPositiveMass_eq_minimumReplica
    {I : Type*} [Fintype I]
    {k : I → ℤ} (hk : SpectralCharacterBalanced k) :
    SpectralCharacterReplicaRealizes
        (spectralCharacterPositiveMass k) k ∧
      ∀ n, SpectralCharacterReplicaRealizes n k →
        spectralCharacterPositiveMass k ≤ n :=
  ⟨spectralCharacterReplicaRealizes_positiveMass_of_balanced hk,
    fun n hn =>
      show spectralCharacterPositiveMass k ≤ n from
        spectralCharacterPositiveMass_le_of_replicaRealizes hn⟩

/-! ## Conditioned-qubit detector orders -/

/-- Integer character of the first conditioned-qubit splitting relation.
The second coordinate is `0` for the positive energy branch and `1` for
the negative energy branch. -/
def conditionedQubitLayerOneCharacter :
    Fin 3 × Fin 2 → ℤ :=
  fun x =>
    !![-1, 1; 1, -1; 0, 0] x.1 x.2

/-- Integer character of the second conditioned-qubit splitting relation. -/
def conditionedQubitLayerTwoCharacter :
    Fin 3 × Fin 2 → ℤ :=
  fun x =>
    !![1, -1; -2, 2; 1, -1] x.1 x.2

/-- The first conditioned-qubit relation is projective. -/
theorem conditionedQubitLayerOneCharacter_balanced :
    SpectralCharacterBalanced conditionedQubitLayerOneCharacter := by
  norm_num [SpectralCharacterBalanced,
    conditionedQubitLayerOneCharacter, Fin.sum_univ_three,
    Fin.sum_univ_two, Fin.sum_univ_succ, Fintype.sum_prod_type]

/-- The second conditioned-qubit relation is projective. -/
theorem conditionedQubitLayerTwoCharacter_balanced :
    SpectralCharacterBalanced conditionedQubitLayerTwoCharacter := by
  norm_num [SpectralCharacterBalanced,
    conditionedQubitLayerTwoCharacter, Fin.sum_univ_three,
    Fin.sum_univ_two, Fin.sum_univ_succ, Fintype.sum_prod_type]

/-- The first conditioned-qubit relation has exact replica height two. -/
theorem conditionedQubitLayerOneCharacter_positiveMass :
    spectralCharacterPositiveMass
      conditionedQubitLayerOneCharacter = 2 := by
  norm_num [spectralCharacterPositiveMass,
    conditionedQubitLayerOneCharacter, Fin.sum_univ_three,
    Fin.sum_univ_two, Fin.sum_univ_succ, Fintype.sum_prod_type,
    Int.toNat_of_nonpos, Int.toNat_of_nonneg]

/-- The second conditioned-qubit relation has exact replica height four. -/
theorem conditionedQubitLayerTwoCharacter_positiveMass :
    spectralCharacterPositiveMass
      conditionedQubitLayerTwoCharacter = 4 := by
  have htwo : Int.toNat (2 : ℤ) = 2 := rfl
  norm_num [spectralCharacterPositiveMass,
    conditionedQubitLayerTwoCharacter, Fin.sum_univ_three,
    Fin.sum_univ_two, Fin.sum_univ_succ, Fintype.sum_prod_type,
    Int.toNat_of_nonpos, Int.toNat_of_nonneg, htwo]

/-- Exact detector-order theorem for the first layer: it is realized at
replica order two and at no smaller order. -/
theorem conditionedQubitLayerOneCharacter_minimumReplica :
    SpectralCharacterReplicaRealizes
        2 conditionedQubitLayerOneCharacter ∧
      ∀ n, SpectralCharacterReplicaRealizes
          n conditionedQubitLayerOneCharacter →
        2 ≤ n := by
  simpa [conditionedQubitLayerOneCharacter_positiveMass] using
    spectralCharacterPositiveMass_eq_minimumReplica
      conditionedQubitLayerOneCharacter_balanced

/-- Exact detector-order theorem for the second layer: it is realized at
replica order four and at no smaller order. -/
theorem conditionedQubitLayerTwoCharacter_minimumReplica :
    SpectralCharacterReplicaRealizes
        4 conditionedQubitLayerTwoCharacter ∧
      ∀ n, SpectralCharacterReplicaRealizes
          n conditionedQubitLayerTwoCharacter →
        4 ≤ n := by
  simpa [conditionedQubitLayerTwoCharacter_positiveMass] using
    spectralCharacterPositiveMass_eq_minimumReplica
      conditionedQubitLayerTwoCharacter_balanced

end GaloisForLFunctions.HTGeometry
