import GaloisForLFunctions.HTGeometry.ProjectiveHorizonReciprocalNumerator
import GaloisForLFunctions.HTGeometry.DerivationIterateLeibniz

/-!
# The relations between the jets of a coordinate and the jets of its reciprocal

A coordinate times its reciprocal is one, so from the first derivative on the binomial combination
of the two jet sequences vanishes.  In each such relation a term pairs a jet of the coordinate with
a jet of the reciprocal whose orders add to the order of the relation.

Both factors of a term have order below `n` only when the order of the relation is below `2n-1`.
So from order `2n-1` on the relation splits into a part carrying one unknown jet of the coordinate,
a part carrying one unknown jet of the reciprocal, and a part in which both orders are at least `n`.
That is the sense in which the deep relations are linear in the missing jets.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C : Type*} [Field C]

theorem freeJetShift_iterate_freeCoordinate (k : ℕ) :
    (⇑(freeJetShift C))^[k] (freeCoordinate C ℕ 0) = freeCoordinate C ℕ k := by
  induction k with
  | zero => rw [Function.iterate_zero_apply]
  | succ k ih => rw [Function.iterate_succ_apply', ih, freeJetShift_freeCoordinate]

/-- **The reciprocal relations.**  From the first order on, the binomial combination of the jets of
the base coordinate against the jets of its reciprocal vanishes. -/
theorem recipLeibniz {m : ℕ} (hm : 0 < m) :
    ∑ k ∈ Finset.range (m + 1),
      (Nat.choose m k) • (freeCoordinate C ℕ k * recipJet C (m - k)) = 0 := by
  have hmul : freeCoordinate C ℕ 0 * recipBase C = 1 :=
    mul_inv_cancel₀ (freeScalarJetCoordinate_ne_zero 0)
  have h := derivation_iterate_mul_eq_zero_of_mul_eq_one (freeJetShift C) hmul hm
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [freeJetShift_iterate_freeCoordinate]
  rfl

/-- The tail of a reciprocal relation, reindexed: the terms whose reciprocal order is below `n`
carry the unknown jets of the reciprocal against known jets of the coordinate. -/
theorem recip_tail_reindex (n m : ℕ) (hnm : n ≤ m + 1) :
    ∑ k ∈ Finset.Ico (m + 1 - n) (m + 1),
        (Nat.choose m k) • (freeCoordinate C ℕ k * recipJet C (m - k)) =
      ∑ j ∈ Finset.range n,
        (Nat.choose m j) • (freeCoordinate C ℕ (m - j) * recipJet C j) := by
  refine (Finset.sum_nbij' (fun k => m - k) (fun j => m - j) ?_ ?_ ?_ ?_ ?_).symm.symm
  · intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_range]
    omega
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.mem_Ico]
    omega
  · intro k hk
    rw [Finset.mem_Ico] at hk
    omega
  · intro j hj
    rw [Finset.mem_range] at hj
    omega
  · intro k hk
    rw [Finset.mem_Ico] at hk
    have h1 : m - (m - k) = k := by omega
    have h2 : Nat.choose m (m - k) = Nat.choose m k := Nat.choose_symm (by omega)
    rw [h1, h2]

/-- **The deep reciprocal relations are linear in the missing jets.**  From order `2n-1` on, a
reciprocal relation is the sum of a part linear in the jets of the coordinate below order `n`, a
part linear in the jets of the reciprocal below order `n`, and a part all of whose orders are at
least `n`. -/
theorem recip_relation_split {n m : ℕ} (hm : 0 < m) (hnm : 2 * n ≤ m + 1) :
    (∑ k ∈ Finset.range n,
        (Nat.choose m k) • (freeCoordinate C ℕ k * recipJet C (m - k))) +
      (∑ j ∈ Finset.range n,
        (Nat.choose m j) • (freeCoordinate C ℕ (m - j) * recipJet C j)) +
      (∑ k ∈ Finset.Ico n (m + 1 - n),
        (Nat.choose m k) • (freeCoordinate C ℕ k * recipJet C (m - k))) = 0 := by
  have hsplit :
      ∑ k ∈ Finset.range (m + 1),
          (Nat.choose m k) • (freeCoordinate C ℕ k * recipJet C (m - k)) =
        (∑ k ∈ Finset.range n,
            (Nat.choose m k) • (freeCoordinate C ℕ k * recipJet C (m - k))) +
          (∑ k ∈ Finset.Ico n (m + 1 - n),
            (Nat.choose m k) • (freeCoordinate C ℕ k * recipJet C (m - k))) +
          ∑ k ∈ Finset.Ico (m + 1 - n) (m + 1),
            (Nat.choose m k) • (freeCoordinate C ℕ k * recipJet C (m - k)) := by
    have e1 := Finset.sum_Ico_consecutive
      (fun k => (Nat.choose m k) • (freeCoordinate C ℕ k * recipJet C (m - k)))
      (Nat.zero_le n) (show n ≤ m + 1 by omega)
    have e2 := Finset.sum_Ico_consecutive
      (fun k => (Nat.choose m k) • (freeCoordinate C ℕ k * recipJet C (m - k)))
      (show n ≤ m + 1 - n by omega) (show m + 1 - n ≤ m + 1 by omega)
    rw [Finset.range_eq_Ico (m + 1), ← e1, ← e2, Finset.range_eq_Ico n]
    ring
  have h := recipLeibniz (C := C) hm
  rw [hsplit, recip_tail_reindex (C := C) n m (by omega)] at h
  rw [← h]
  ring

end

end GaloisForLFunctions.HTGeometry
