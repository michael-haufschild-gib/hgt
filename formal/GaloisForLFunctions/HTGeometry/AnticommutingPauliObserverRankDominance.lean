import GaloisForLFunctions.HTGeometry.CommutingPauliObserverRankDominance

/-!
# Anticommuting Pauli observer-rank dominance

A pairwise anticommuting Pauli family becomes linearly independent after one
binary affine coordinate is adjoined.  It therefore has at most `2n + 1`
members on `n` qubits.  For locality order at least two, this entire
noncommuting carrier is too small to beat the exact product-input observer
rank inside the full local Pauli coefficient space.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Quantum

open NQubitPauliOperator Module Submodule
open Quantum.StabilizerGroup

variable {n : ℕ}

/-- A Pauli symplectic vector with one affine binary coordinate adjoined. -/
def augmentedPauliVector (p : NQubitPauliOperator n) :
    (Fin (n + n) → ZMod 2) × ZMod 2 :=
  (toSymplectic p, 1)

/-- Augmented symplectic vectors of a pairwise anticommuting Pauli family are
linearly independent over `F₂`. -/
theorem augmentedPauliVector_linearIndependent
    (A : Finset (NQubitPauliOperator n))
    (hanti : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → symplecticInner p q = 1) :
    LinearIndependent (ZMod 2)
      (fun p : {p // p ∈ A} => augmentedPauliVector p.1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hsum p
  have hlast : ∑ i, c i = 0 := by
    have h := congrArg Prod.snd hsum
    simpa [augmentedPauliVector, Prod.snd_sum] using h
  have hfirst : ∑ i, c i • toSymplectic i.1 = 0 := by
    have h := congrArg Prod.fst hsum
    simpa [augmentedPauliVector, Prod.fst_sum] using h
  have hpair := congrArg
    (fun v => sympBilinForm n v (toSymplectic p.1)) hfirst
  have hpair' :
      ∑ i, c i * symplecticInner i.1 p.1 = 0 := by
    simpa [map_sum, map_smul, symplecticBilinear_toSymplectic] using hpair
  have hsplit :
      (∑ i, c i * symplecticInner i.1 p.1) =
        ∑ i, if i = p then 0 else c i := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hip : i = p
    · subst i
      have hself : symplecticInner p.1 p.1 = 0 := by
        unfold symplecticInner PauliOperator.symplecticProductSingle
        apply Finset.sum_eq_zero
        intro j hj
        rw [mul_comm ((p.1 j).toSymplecticSingle.2)
          ((p.1 j).toSymplecticSingle.1), CharTwo.add_self_eq_zero]
      simp [hself]
    · have hv := hanti i.1 i.2 p.1 p.2 (by
        intro hv
        apply hip
        exact Subtype.ext hv)
      simp [hip, hv]
  have hexclude :
      (∑ i, if i = p then (0 : ZMod 2) else c i) = 0 := by
    rw [← hsplit]
    exact hpair'
  have htotal :
      (∑ i, if i = p then c i else (0 : ZMod 2)) +
        (∑ i, if i = p then (0 : ZMod 2) else c i) = 0 := by
    rw [← Finset.sum_add_distrib]
    calc
      ∑ x, ((if x = p then c x else 0) + if x = p then 0 else c x) =
          ∑ x, c x := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hxp : x = p <;> simp [hxp]
      _ = 0 := hlast
  rw [hexclude, add_zero] at htotal
  simpa using htotal

/-- Every pairwise anticommuting `n`-qubit Pauli family has at most
`2n + 1` members. -/
theorem card_pairwiseAnticommutingPauli_le
    (A : Finset (NQubitPauliOperator n))
    (hanti : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → symplecticInner p q = 1) :
    A.card ≤ 2 * n + 1 := by
  classical
  have hli := augmentedPauliVector_linearIndependent A hanti
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_coe, Module.finrank_prod] at hcard
  have hfun : Module.finrank (ZMod 2) (Fin (n + n) → ZMod 2) = n + n := by
    simp
  have hscalar : Module.finrank (ZMod 2) (ZMod 2) = 1 := by
    simp
  rw [hfun, hscalar] at hcard
  omega

private lemma pred_le_choose_two (n : ℕ) : n - 1 ≤ n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.choose]
      simp

/-- At locality order at least two, the first two commuting-capacity terms
already dominate the maximal anticommuting carrier dimension. -/
theorem two_mul_add_one_le_commutingPauliCapacity
    (n q : ℕ) (hn : 2 ≤ n) (hq : 2 ≤ q) :
    2 * n + 1 ≤ commutingPauliCapacity n q := by
  have hsmall : 2 * n + 1 ≤
      ∑ j ∈ Finset.range 2,
        (2 ^ (j + 1) - 1) * n.choose (j + 1) := by
    have heval :
        (∑ j ∈ Finset.range 2,
          (2 ^ (j + 1) - 1) * n.choose (j + 1)) =
          n + 3 * n.choose 2 := by
      norm_num [Finset.sum_range_succ]
    rw [heval]
    have hchoose := pred_le_choose_two n
    omega
  apply hsmall.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono hq
  · intro j hjq hj2
    exact Nat.zero_le _

/-- The observer-stationary codimension never exceeds the transverse
codimension of a pairwise anticommuting Pauli carrier. -/
theorem pairwiseAnticommutingPauli_card_add_observerRank_le_pauliWeightCount
    (A : Finset (NQubitPauliOperator n)) (q : ℕ)
    (hn : 2 ≤ n) (hq : 2 ≤ q)
    (hanti : ∀ p ∈ A, ∀ r ∈ A, p ≠ r → symplecticInner p r = 1) :
    A.card + productInputObserverRank n q ≤ nonidentityPauliWeightCount n q := by
  have hcard := card_pairwiseAnticommutingPauli_le A hanti
  have hcapacity := two_mul_add_one_le_commutingPauliCapacity n q hn hq
  have hmain := commutingPauliCapacity_add_observerRank_le_pauliWeightCount n q
  omega

end Quantum
