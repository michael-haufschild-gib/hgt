import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheActivityGapOfBalancedUnitaryDivisors

/-!
# Sharp separation of the two unitary midpoint boundary sizes

Radial birth-and-death balance prices a small subset of size j by r−2j.
A full face costs 2^(r−1). Every missing low-rank configuration in the
comparison with that face contributes twice its distance from the middle
rank. With all single blocks small the first rank alone costs 2(r−2)
additional edges. A one-exchange boundary attains this price exactly.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Number of single-block births that change which side is below the square root. -/
def unitaryEdgeCount (k : ℕ) := ∑ p ∈ k.primeFactors,(unitaryPivots k p).card

private def edgePrice (r j : ℕ) : ℝ := (r:ℝ)-2*j

private theorem edge_rank_price (k : ℕ) :
    (unitaryEdgeCount k:ℝ)=∑ S ∈ smallUnitarySubsets k,edgePrice k.primeFactors.card S.card := by
  have flux := unitaryPivots_radial_flux k (fun _ => (1:ℝ))
  simp only [sum_const,nsmul_eq_mul,mul_one] at flux
  rw [unitaryEdgeCount,Nat.cast_sum,flux]
  refine sum_congr rfl fun S hs => ?_
  have le := card_le_card (mem_powerset.mp (mem_filter.mp hs).1)
  rw [Nat.cast_sub le,edgePrice]
  ring

-- Reflection within the remaining r−1 blocks pairs two ranks of total price two.
private theorem face_edge_price {k p : ℕ} (hp : p∈k.primeFactors) :
    (∑ S ∈ (k.primeFactors.erase p).powerset,edgePrice k.primeFactors.card S.card)=(2:ℝ)^(k.primeFactors.card-1) := by
  let P := k.primeFactors
  let B := P.erase p
  let w := edgePrice P.card
  have size : B.card=P.card-1 := card_erase_of_mem hp
  have one : 1≤P.card := card_pos.mpr ⟨p,hp⟩
  have rev : (∑ S ∈ B.powerset,w (B \ S).card)=∑ S ∈ B.powerset,w S.card := by
    apply sum_nbij' (fun S => B \ S) (fun S => B \ S)
    · exact fun _ _ => mem_powerset.mpr sdiff_subset
    · exact fun _ _ => mem_powerset.mpr sdiff_subset
    · exact fun _ hs => Finset.sdiff_sdiff_eq_self (mem_powerset.mp hs)
    · exact fun _ hs => Finset.sdiff_sdiff_eq_self (mem_powerset.mp hs)
    · exact fun _ _ => rfl
  have pair : (∑ S ∈ B.powerset,(w S.card+w (B \ S).card))=∑ _S ∈ B.powerset,(2:ℝ) := by
    refine sum_congr rfl fun S hs => ?_
    have sub := mem_powerset.mp hs
    rw [card_sdiff_of_subset sub]
    dsimp only [w,edgePrice]
    rw [Nat.cast_sub (card_le_card sub),size,Nat.cast_sub one,Nat.cast_one]
    ring
  rw [sum_add_distrib,rev,sum_const,card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,size] at pair
  change (∑ S ∈ B.powerset,w S.card)=(2:ℝ)^(P.card-1)
  linarith only [pair]

/-- Exact integer boundary cost by rank. The reference face is corrected
only at ranks j below r/2; each surplus there costs 2(r−2j). -/
theorem unitary_edge_rank_expansion {k : ℕ} (hk : 1<k) :
    let r := k.primeFactors.card
    (unitaryEdgeCount k:ℝ)-(2:ℝ)^(r-1)=
      ∑ j ∈ range (r+1), ((smallUnitaryRankCount k j:ℝ)-((r-1).choose j:ℝ))*(2*((r-2*j:ℕ):ℝ)) := by
  intro r
  obtain ⟨p,hp⟩ := Nat.nonempty_primeFactors.mpr hk
  have gap := unitary_cut_rank_price_gap hk hp (edgePrice r)
  rw [←edge_rank_price,face_edge_price hp] at gap
  refine gap.trans (sum_congr rfl fun j _ => ?_)
  congr 1
  have split : max j (r-j)=j+(r-2*j) := by omega
  rw [edgePrice,edgePrice,split,Nat.cast_add]
  ring

/-- A block larger than the square root produces exactly a face boundary. -/
theorem dominant_unitary_edge_count {k p : ℕ} (hk : 1<k) (hp : p∈k.primeFactors)
    (big : k<(p^k.factorization p)^2) : unitaryEdgeCount k=2^(k.primeFactors.card-1) := by
  have eq := edge_rank_price k
  rw [small_unitary_subsets_of_dominant hk hp big,face_edge_price hp] at eq
  exact_mod_cast eq

/-- Absence of a dominant block forces a boundary gap of two times
the number of blocks beyond the first two. -/
theorem balanced_unitary_edge_count {k : ℕ} (hk : 1<k)
    (bal : ∀ p∈k.primeFactors,(p^k.factorization p)^2≤k) :
    let r := k.primeFactors.card
    2^(r-1)+2*(r-2)≤unitaryEdgeCount k := by
  intro r
  obtain ⟨p,hp⟩ := Nat.nonempty_primeFactors.mpr hk
  have three : 3≤r := three_le_card_balanced_unitary_support hk bal
  have anti : Antitone (edgePrice r) := fun i j h => by
    dsimp only [edgePrice]
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h) (by norm_num)) _
  have paid := balanced_unitary_rank_price_gap hk hp bal anti
  have price : edgePrice r 1-edgePrice r (r-1)=2*((r-2:ℕ):ℝ) := by
    simp only [edgePrice,Nat.cast_sub (by omega : 1≤r),Nat.cast_sub (by omega : 2≤r),Nat.cast_one,Nat.cast_ofNat]
    ring
  rw [face_edge_price hp,←edge_rank_price] at paid
  change (2:ℝ)^(r-1)+(edgePrice r 1-edgePrice r (r-1)) ≤ (unitaryEdgeCount k:ℝ) at paid
  rw [price] at paid
  exact_mod_cast paid

/-- The least possible boundary size detects a prime-power block above
the square root on every nontrivial conductor. -/
theorem unitary_edge_face_equality_iff {k : ℕ} (hk : 1<k) :
    unitaryEdgeCount k=2^(k.primeFactors.card-1) ↔ ∃ p∈k.primeFactors,k<(p^k.factorization p)^2 := by
  constructor
  · intro eq
    by_contra! absent
    have three := three_le_card_balanced_unitary_support hk absent
    have floor := balanced_unitary_edge_count hk absent
    change 2^(k.primeFactors.card-1)+2*(k.primeFactors.card-2)≤unitaryEdgeCount k at floor
    rw [eq] at floor
    omega
  · rintro ⟨p,hp,big⟩
    exact dominant_unitary_edge_count hk hp big

/-- Exchanging a singleton with the opposite corner attains the first
boundary size above the full face. -/
theorem one_exchange_attains_balanced_edge_floor {k p : ℕ} (hp : p∈k.primeFactors)
    (lo : (p^k.factorization p)^2<k) (hi : k<(2*p^k.factorization p)^2)
    (rank : 3≤k.primeFactors.card) :
    let r := k.primeFactors.card
    unitaryEdgeCount k=2^(r-1)+2*(r-2) := by
  intro r
  have exactCount := one_exchange_boundary_size hp lo hi
  change unitaryEdgeCount k=2^(k.primeFactors.erase p).card-2+2*(k.primeFactors.erase p).card at exactCount
  rw [card_erase_of_mem hp] at exactCount
  have pos : 2≤2^(r-1) := by
    simpa only [pow_one] using (Nat.pow_le_pow_right (by decide : 0<2) (by omega : 1≤r-1))
  change unitaryEdgeCount k=2^(r-1)-2+2*(r-1) at exactCount
  omega

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
