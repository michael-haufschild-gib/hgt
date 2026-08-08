import GaloisForLFunctions.RHTower.MobiusReciprocalAllocationJacobian

/-!
# Parity-coalesced full-mass cube

This module formalizes exact finite parity and Wold-drift core of Route E coalesced full-mass
relation.  Coalescing two coordinates when source arity is even produces an odd number of
replacement coordinates without deleting source mass.  Explicit shift packets realize both
terminal drifts +1 and -1 for every odd source arity and every even source arity at least four.
At arity two robust coalesced packet has only downward drift, exactly matching paper boundary.
-/

namespace RHTower

open Finset

/-- Upward alternating shifts for an odd packet of length 2m+1. -/
def oddUpShiftPacket (m : ℕ) : List ℤ :=
  List.replicate (m + 1) 1 ++ List.replicate m (-1)

/-- Downward alternating shifts for an odd packet of length 2m+1. -/
def oddDownShiftPacket (m : ℕ) : List ℤ :=
  List.replicate m 1 ++ List.replicate (m + 1) (-1)

/-- Downward shifts for a coalesced packet from even source arity 2m.
First -1 is merged coordinate. -/
def evenCoalescedDownShiftPacket (m : ℕ) : List ℤ :=
  [-1] ++ List.replicate (m - 1) 1 ++ List.replicate (m - 1) (-1)

/-- Upward shifts for a coalesced packet from even source arity 2m, available for m at least 2.
First -1 is again merged coordinate. -/
def evenCoalescedUpShiftPacket (m : ℕ) : List ℤ :=
  [-1] ++ List.replicate m 1 ++ List.replicate (m - 2) (-1)

theorem oddUpShiftPacket_length (m : ℕ) :
    (oddUpShiftPacket m).length = 2 * m + 1 := by
  simp [oddUpShiftPacket]
  omega

theorem oddDownShiftPacket_length (m : ℕ) :
    (oddDownShiftPacket m).length = 2 * m + 1 := by
  simp [oddDownShiftPacket]
  omega

theorem oddUpShiftPacket_sum (m : ℕ) :
    (oddUpShiftPacket m).sum = 1 := by
  simp [oddUpShiftPacket]

theorem oddDownShiftPacket_sum (m : ℕ) :
    (oddDownShiftPacket m).sum = -1 := by
  simp [oddDownShiftPacket]

theorem oddUpShiftPacket_values (m : ℕ) {e : ℤ}
    (he : e ∈ oddUpShiftPacket m) :
    e = 1 ∨ e = -1 := by
  rcases List.mem_append.mp he with he | he
  · exact Or.inl (List.mem_replicate.mp he).2
  · exact Or.inr (List.mem_replicate.mp he).2

theorem oddDownShiftPacket_values (m : ℕ) {e : ℤ}
    (he : e ∈ oddDownShiftPacket m) :
    e = 1 ∨ e = -1 := by
  rcases List.mem_append.mp he with he | he
  · exact Or.inl (List.mem_replicate.mp he).2
  · exact Or.inr (List.mem_replicate.mp he).2

theorem evenCoalescedDownShiftPacket_length {m : ℕ} (hm : 1 ≤ m) :
    (evenCoalescedDownShiftPacket m).length = 2 * m - 1 := by
  simp [evenCoalescedDownShiftPacket]
  omega

theorem evenCoalescedUpShiftPacket_length {m : ℕ} (hm : 2 ≤ m) :
    (evenCoalescedUpShiftPacket m).length = 2 * m - 1 := by
  simp [evenCoalescedUpShiftPacket]
  omega

theorem evenCoalescedDownShiftPacket_sum (m : ℕ) :
    (evenCoalescedDownShiftPacket m).sum = -1 := by
  simp [evenCoalescedDownShiftPacket]

theorem evenCoalescedUpShiftPacket_sum {m : ℕ} (hm : 2 ≤ m) :
    (evenCoalescedUpShiftPacket m).sum = 1 := by
  simp [evenCoalescedUpShiftPacket]
  omega

theorem evenCoalescedDownShiftPacket_head (m : ℕ) :
    (evenCoalescedDownShiftPacket m).head? = some (-1) := by
  simp [evenCoalescedDownShiftPacket]

theorem evenCoalescedUpShiftPacket_head (m : ℕ) :
    (evenCoalescedUpShiftPacket m).head? = some (-1) := by
  simp [evenCoalescedUpShiftPacket]

theorem evenCoalescedDownShiftPacket_values (m : ℕ) {e : ℤ}
    (he : e ∈ evenCoalescedDownShiftPacket m) :
    e = 1 ∨ e = -1 := by
  simp only [evenCoalescedDownShiftPacket, List.mem_append, List.mem_singleton] at he
  rcases he with he | he
  · rcases he with he | he
    · exact Or.inr he
    · exact Or.inl (List.mem_replicate.mp he).2
  · exact Or.inr (List.mem_replicate.mp he).2

theorem evenCoalescedUpShiftPacket_values (m : ℕ) {e : ℤ}
    (he : e ∈ evenCoalescedUpShiftPacket m) :
    e = 1 ∨ e = -1 := by
  simp only [evenCoalescedUpShiftPacket, List.mem_append, List.mem_singleton] at he
  rcases he with he | he
  · rcases he with he | he
    · exact Or.inr he
    · exact Or.inl (List.mem_replicate.mp he).2
  · exact Or.inr (List.mem_replicate.mp he).2

/-- Every odd positive source arity admits source-predeclared +1 and -1 full-terminal drift
packets, both retaining all coordinates. -/
theorem exists_twoSided_fullMass_shiftPackets_of_odd
    {d : ℕ} (hd : Odd d) :
    ∃ up down : List ℤ,
      up.length = d ∧ down.length = d ∧
      (∀ e ∈ up, e = 1 ∨ e = -1) ∧
      (∀ e ∈ down, e = 1 ∨ e = -1) ∧
      up.sum = 1 ∧ down.sum = -1 := by
  rcases hd with ⟨m, rfl⟩
  refine ⟨oddUpShiftPacket m, oddDownShiftPacket m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [two_mul, add_assoc] using oddUpShiftPacket_length m
  · simpa [two_mul, add_assoc] using oddDownShiftPacket_length m
  · exact fun e he => oddUpShiftPacket_values m he
  · exact fun e he => oddDownShiftPacket_values m he
  · exact oddUpShiftPacket_sum m
  · exact oddDownShiftPacket_sum m

/-- Every even source arity at least four admits two coalesced full-mass packets of odd
coordinate count d-1, with merged-coordinate shift -1 and total drifts +1 and -1. -/
theorem exists_twoSided_fullMass_shiftPackets_of_even
    {d : ℕ} (hd : Even d) (h4 : 4 ≤ d) :
    ∃ up down : List ℤ,
      up.length = d - 1 ∧ down.length = d - 1 ∧
      up.head? = some (-1) ∧ down.head? = some (-1) ∧
      (∀ e ∈ up, e = 1 ∨ e = -1) ∧
      (∀ e ∈ down, e = 1 ∨ e = -1) ∧
      up.sum = 1 ∧ down.sum = -1 := by
  rcases hd with ⟨m, rfl⟩
  have hm : 2 ≤ m := by omega
  refine ⟨evenCoalescedUpShiftPacket m, evenCoalescedDownShiftPacket m,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [two_mul] using evenCoalescedUpShiftPacket_length hm
  · simpa [two_mul] using evenCoalescedDownShiftPacket_length (le_trans (by omega) hm)
  · exact evenCoalescedUpShiftPacket_head m
  · exact evenCoalescedDownShiftPacket_head m
  · exact fun e he => evenCoalescedUpShiftPacket_values m he
  · exact fun e he => evenCoalescedDownShiftPacket_values m he
  · exact evenCoalescedUpShiftPacket_sum hm
  · exact evenCoalescedDownShiftPacket_sum m

/-- Exact two-active-block boundary: coalescence leaves one coordinate, whose robust prescribed
shift is -1. -/
theorem two_activeBlocks_coalesce_to_downward_singleton :
    evenCoalescedDownShiftPacket 1 = [-1] ∧
      (evenCoalescedDownShiftPacket 1).sum = -1 := by
  simp [evenCoalescedDownShiftPacket]

/-- Reversing every coordinate in an odd full-mass packet reverses product sign. -/
theorem prod_coordinateReversals_eq_neg_of_odd
    {R : Type*} [CommRing R] {d : ℕ} (hd : Odd d)
    (source target : Fin d → R) (hreverses : ∀ i, target i = -source i) :
    ∏ i, target i = -∏ i, source i := by
  simp_rw [hreverses]
  rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin, hd.neg_one_pow]
  simp

/-- Packet of individual unit grade shifts stays within coordinate count at every corner. -/
theorem abs_subset_sum_le_card_of_unitShifts
    {ι : Type*} [Fintype ι] (shift : ι → ℤ)
    (hunit : ∀ i, shift i = 1 ∨ shift i = -1) (S : Finset ι) :
    |∑ i ∈ S, shift i| ≤ Fintype.card ι := by
  calc
    |∑ i ∈ S, shift i| ≤ ∑ i ∈ S, |shift i| := abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ S, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rcases hunit i with h | h <;> simp [h]
    _ = S.card := by simp
    _ ≤ Fintype.card ι := by
      exact_mod_cast Finset.card_le_univ S

end RHTower
