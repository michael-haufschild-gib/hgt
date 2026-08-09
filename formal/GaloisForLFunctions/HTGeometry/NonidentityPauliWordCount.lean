import GaloisForLFunctions.HTGeometry.PauliTwoLocalLabels
import GaloisForLFunctions.HTGeometry.CommutingPauliObserverRankDominance

/-!
# Counting the nonidentity Pauli words of bounded weight

A Pauli string is determined by its support together with one of three nontrivial single-qubit
labels at each active site.  Grouping the strings of a given weight by their support therefore
counts them as `3^k` per support, and the supports of size `k` are counted by a binomial
coefficient.

The weight-at-most-`q` nonidentity strings on `n` qubits are consequently `∑_{k=1}^q 3^k C(n,k)` in
number, which is the normalisation used by a fixed-locality Pauli ensemble.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {n : ℕ}

/-- The set of qubits a Pauli string acts on. -/
def pauliSupport (P : Fin n → Option (Fin 3)) : Finset (Fin n) :=
  Finset.univ.filter fun s => P s ≠ none

@[simp] theorem mem_pauliSupport {P : Fin n → Option (Fin 3)} {s : Fin n} :
    s ∈ pauliSupport P ↔ P s ≠ none := by
  simp [pauliSupport]

theorem pauliWeight_eq_card_pauliSupport (P : Fin n → Option (Fin 3)) :
    pauliWeight P = (pauliSupport P).card := rfl

/-- **Strings with a prescribed support are counted by three choices per active site.** -/
theorem card_filter_pauliSupport_eq (S : Finset (Fin n)) :
    (Finset.univ.filter fun P : Fin n → Option (Fin 3) => pauliSupport P = S).card
      = 3 ^ S.card := by
  classical
  have hset : (Finset.univ.filter fun P : Fin n → Option (Fin 3) => pauliSupport P = S)
      = Fintype.piFinset fun s =>
          if s ∈ S then (Finset.univ.erase (none : Option (Fin 3))) else {none} := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h s
      by_cases hs : s ∈ S
      · rw [if_pos hs, Finset.mem_erase]
        exact ⟨mem_pauliSupport.mp (h ▸ hs), Finset.mem_univ _⟩
      · rw [if_neg hs, Finset.mem_singleton]
        by_contra hne
        exact hs (h ▸ mem_pauliSupport.mpr hne)
    · intro h
      ext s
      rw [mem_pauliSupport]
      constructor
      · intro hne
        by_contra hs
        have := h s
        rw [if_neg hs, Finset.mem_singleton] at this
        exact hne this
      · intro hs
        have := h s
        rw [if_pos hs, Finset.mem_erase] at this
        exact this.1
  rw [hset, Fintype.card_piFinset]
  have hcard : ∀ s : Fin n,
      (if s ∈ S then (Finset.univ.erase (none : Option (Fin 3))) else {none}).card
        = if s ∈ S then 3 else 1 := by
    intro s
    by_cases hs : s ∈ S <;>
      simp [hs, Finset.card_erase_of_mem, Finset.card_univ]
  rw [Finset.prod_congr rfl fun s _ => hcard s, Finset.prod_ite]
  simp

/-- **The strings of a given weight are counted by supports times labels.** -/
theorem card_filter_pauliWeight_eq (k : ℕ) :
    (Finset.univ.filter fun P : Fin n → Option (Fin 3) => pauliWeight P = k).card
      = n.choose k * 3 ^ k := by
  classical
  have hmaps : Set.MapsTo pauliSupport
      ((Finset.univ.filter fun P : Fin n → Option (Fin 3) => pauliWeight P = k) :
        Set (Fin n → Option (Fin 3)))
      ((Finset.powersetCard k (Finset.univ : Finset (Fin n))) : Set (Finset (Fin n))) := by
    intro P hP
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hP
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by
      rw [← pauliWeight_eq_card_pauliSupport]; exact hP.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hterm : ∀ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
      ((Finset.univ.filter fun P : Fin n → Option (Fin 3) => pauliWeight P = k).filter
          fun P => pauliSupport P = S).card = 3 ^ k := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    have hfil : ((Finset.univ.filter fun P : Fin n → Option (Fin 3) => pauliWeight P = k).filter
        fun P => pauliSupport P = S)
        = Finset.univ.filter fun P : Fin n → Option (Fin 3) => pauliSupport P = S := by
      ext P
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨by rw [pauliWeight_eq_card_pauliSupport, h, hS.2], h⟩
    rw [hfil, card_filter_pauliSupport_eq, hS.2]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- The nonidentity Pauli strings of weight at most `q`. -/
def nonidentityPauliWords (n q : ℕ) : Finset (Fin n → Option (Fin 3)) :=
  Finset.univ.filter fun P => 1 ≤ pauliWeight P ∧ pauliWeight P ≤ q

theorem mem_nonidentityPauliWords {n q : ℕ} {P : Fin n → Option (Fin 3)} :
    P ∈ nonidentityPauliWords n q ↔ 1 ≤ pauliWeight P ∧ pauliWeight P ≤ q := by
  simp [nonidentityPauliWords]

/-- **The fixed-locality Pauli ensemble has `∑_{k=1}^q 3^k C(n,k)` terms.** -/
theorem card_nonidentityPauliWords (n q : ℕ) :
    (nonidentityPauliWords n q).card = Quantum.nonidentityPauliWeightCount n q := by
  classical
  have hmaps : Set.MapsTo pauliWeight ((nonidentityPauliWords n q) :
      Set (Fin n → Option (Fin 3))) ((Finset.Ico 1 (q + 1)) : Set ℕ) := by
    intro P hP
    have hP' := mem_nonidentityPauliWords.mp (by simpa using hP)
    simp only [Finset.mem_coe, Finset.mem_Ico]
    exact ⟨hP'.1, by omega⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hterm : ∀ k ∈ Finset.Ico 1 (q + 1),
      ((nonidentityPauliWords n q).filter fun P => pauliWeight P = k).card
        = n.choose k * 3 ^ k := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hfil : ((nonidentityPauliWords n q).filter fun P => pauliWeight P = k)
        = Finset.univ.filter fun P : Fin n → Option (Fin 3) => pauliWeight P = k := by
      ext P
      simp only [nonidentityPauliWords, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨⟨by omega, by omega⟩, h⟩
    rw [hfil, card_filter_pauliWeight_eq]
  rw [Finset.sum_congr rfl hterm, Finset.sum_Ico_eq_sum_range,
    Quantum.nonidentityPauliWeightCount]
  refine Finset.sum_congr (by simp) fun j _ => ?_
  rw [show 1 + j = j + 1 from by omega, mul_comm]

end GaloisForLFunctions.HTGeometry
