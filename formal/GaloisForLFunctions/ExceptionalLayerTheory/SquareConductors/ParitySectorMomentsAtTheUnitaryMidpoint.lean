import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.EveryValueOfTheFivePrimeMidpoint

/-!
# Parity-sector moments at the unitary midpoint

Varrin's sector trace formula (arXiv:2610.37750, equation 4.10) sums powers
of sector masses for one-dimensional sectors. For small unitary divisors the
even and odd sectors can exchange masses on the same five primes. Removing
the unit marks the even sector and recovers the signed midpoint from the
change of the two-copy count.
-/

open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
noncomputable section
open scoped Classical

/-- Prime-power subproducts are coprime precisely on disjoint blocks. -/
theorem primePowerSubset_coprime_iff {k : ℕ} {S T : Finset ℕ}
    (hs : S ⊆ k.primeFactors) (ht : T ⊆ k.primeFactors) :
    (primePowerSubset k S).Coprime (primePowerSubset k T) ↔ Disjoint S T := by
  constructor
  · intro h
    apply disjoint_left.mpr
    intro p hp hq
    obtain ⟨hpr,hd,hk⟩ := Nat.mem_primeFactors.mp (hs hp)
    have hpow := dvd_pow_self p (hpr.factorization_pos_of_dvd hk hd).ne'
    have ha : p ∣ primePowerSubset k S := hpow.trans (dvd_prod_of_mem _ hp)
    have hb : p ∣ primePowerSubset k T := hpow.trans (dvd_prod_of_mem _ hq)
    exact hpr.coprime_iff_not_dvd.mp (h.of_dvd_left ha) hb
  · intro h
    apply Nat.Coprime.prod_left
    intro p hp
    apply Nat.Coprime.prod_right
    intro q hq
    apply Nat.Coprime.pow
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (hs hp))
      (Nat.prime_of_mem_primeFactors (ht hq))).mpr (fun e => disjoint_left.mp h hp (e ▸ hq))

/-- Complementation selects exactly half of the prime-power cube for k>1. -/
theorem twice_card_smallUnitarySubsets {k : ℕ} (hk : 1 < k) :
    2*(smallUnitarySubsets k).card = 2^k.primeFactors.card := by
  let P := k.primeFactors
  let small (S : Finset ℕ) := primePowerSubset k S ≤ primePowerSubset k (P \ S)
  have flip (S : Finset ℕ) (hs : S ⊆ P) : small (P \ S) ↔ ¬small S := by
    dsimp only [small]
    rw [Finset.sdiff_sdiff_eq_self hs, not_le]
    refine ⟨fun h => h.lt_of_ne ?_, LT.lt.le⟩
    intro he
    have hc := (primePowerSubset_coprime_iff hs (show P \ S ⊆ P from sdiff_subset)).mpr
      (disjoint_left.mpr (fun x hx h => (mem_sdiff.mp h).2 hx))
    have hm : primePowerSubset k S * primePowerSubset k (P \ S) = k := by
      rw [primePowerSubset,primePowerSubset,mul_comm,prod_sdiff hs]
      exact (Nat.prod_primeFactors_pow_factorization (by omega : k ≠ 0)).symm
    rw [he] at hc hm
    change (primePowerSubset k S).gcd (primePowerSubset k S) = 1 at hc
    rw [Nat.gcd_self] at hc
    rw [hc,one_mul] at hm
    omega
  have same : (P.powerset.filter small).card = (P.powerset.filter (fun S => ¬small S)).card := by
    apply card_nbij' (fun S => P \ S) (fun S => P \ S)
    · intro S hS
      obtain ⟨hS,hm⟩ := mem_filter.mp hS
      exact mem_filter.mpr ⟨mem_powerset.mpr sdiff_subset,fun h => (flip S (mem_powerset.mp hS)).mp h hm⟩
    · intro S hS
      obtain ⟨hS,hm⟩ := mem_filter.mp hS
      exact mem_filter.mpr ⟨mem_powerset.mpr sdiff_subset,(flip S (mem_powerset.mp hS)).mpr hm⟩
    · exact fun S hS => Finset.sdiff_sdiff_eq_self (mem_powerset.mp (mem_filter.mp hS).1)
    · exact fun S hS => Finset.sdiff_sdiff_eq_self (mem_powerset.mp (mem_filter.mp hS).1)
  have hall := P.powerset.card_filter_add_card_filter_not small
  rw [← same,card_powerset] at hall
  exact (two_mul _).trans hall

/-- Counts of the even and odd sectors of a finite family of block subsets. -/
def unitaryParityCounts (F : Finset (Finset ℕ)) : ℕ × ℕ :=
  ((F.filter fun S => Even S.card).card,(F.filter fun S => ¬Even S.card).card)

/-- Number of ordered j-tuples drawn from a single sector, summed over both sectors. -/
def unitarySectorMoment (F : Finset (Finset ℕ)) (j : ℕ) : ℕ :=
  (unitaryParityCounts F).1^j + (unitaryParityCounts F).2^j

theorem unitaryParityCounts_total (F : Finset (Finset ℕ)) :
    (unitaryParityCounts F).1 + (unitaryParityCounts F).2 = F.card :=
  F.card_filter_add_card_filter_not _

theorem unitaryParityCounts_diff (k : ℕ) :
    ((unitaryParityCounts (smallUnitarySubsets k)).1 : ℤ) -
      (unitaryParityCounts (smallUnitarySubsets k)).2 = unitaryHalfWeight k := by
  let F := smallUnitarySubsets k
  have h := sum_filter_add_sum_filter_not F (fun S : Finset ℕ => Even S.card)
    (fun S => (-1:ℤ)^S.card)
  rw [sum_congr rfl (fun S hS => (mem_filter.mp hS).2.neg_one_pow),
    sum_congr rfl (fun S hS => (Nat.not_even_iff_odd.mp (mem_filter.mp hS).2).neg_one_pow)] at h
  simpa [unitaryHalfWeight,unitaryParityCounts,F,sub_eq_add_neg] using h

/-- The two-copy count measures the square of the midpoint weight exactly. -/
theorem unitarySectorMoment_two (k : ℕ) :
    2*(unitarySectorMoment (smallUnitarySubsets k) 2 : ℤ) =
      ((smallUnitarySubsets k).card : ℤ)^2 + (unitaryHalfWeight k)^2 := by
  rw [← unitaryParityCounts_total, ← unitaryParityCounts_diff]
  simp only [unitarySectorMoment,Nat.cast_add,Nat.cast_pow]
  ring

/-- All sector moments, including all normalized Rényi power sums, fail to
determine the sign on arbitrarily late integers on any fixed five-prime support. -/
theorem cofinal_opposite_unitarySectorMoments {P : Finset ℕ} (h5 : P.card = 5)
    (hp : ∀ p ∈ P, Nat.Prime p) (B : ℕ) :
    ∃ k > B, ∃ l > B, k.primeFactors = P ∧ l.primeFactors = P ∧
      unitaryHalfWeight k = 2 ∧ unitaryHalfWeight l = -2 ∧
      unitaryParityCounts (smallUnitarySubsets k) = (9,7) ∧
      unitaryParityCounts (smallUnitarySubsets l) = (7,9) ∧
      ∀ j, unitarySectorMoment (smallUnitarySubsets k) j =
        unitarySectorMoment (smallUnitarySubsets l) j := by
  obtain ⟨k,hk,hkP,hkW⟩ := (cofinal_range_of_five_prime_midpoint h5 hp 2).mpr
    ⟨⟨2,by decide⟩,by norm_num⟩ (max B 1)
  obtain ⟨l,hl,hlP,hlW⟩ := (cofinal_range_of_five_prime_midpoint h5 hp (-2)).mpr
    ⟨⟨4,by decide⟩,by norm_num⟩ (max B 1)
  have total (n : ℕ) (hn : 1 < n) (hnP : n.primeFactors=P) :
      (unitaryParityCounts (smallUnitarySubsets n)).1 +
        (unitaryParityCounts (smallUnitarySubsets n)).2 = 16 := by
    have h := twice_card_smallUnitarySubsets hn
    rw [hnP,h5] at h
    rw [unitaryParityCounts_total]
    omega
  have h₁ := total k ((le_max_right _ _).trans_lt hk) hkP
  have h₂ := total l ((le_max_right _ _).trans_lt hl) hlP
  have d₁ := unitaryParityCounts_diff k
  have d₂ := unitaryParityCounts_diff l
  rw [hkW] at d₁
  rw [hlW] at d₂
  have e₁ : unitaryParityCounts (smallUnitarySubsets k) = (9,7) := Prod.ext (by omega) (by omega)
  have e₂ : unitaryParityCounts (smallUnitarySubsets l) = (7,9) := Prod.ext (by omega) (by omega)
  exact ⟨k,(le_max_left _ _).trans_lt hk,l,(le_max_left _ _).trans_lt hl,hkP,hlP,hkW,hlW,e₁,e₂,
    fun j => by simp only [unitarySectorMoment,e₁,e₂,add_comm]⟩

/-- Deleting the empty block subset marks the even sector. The loss of
two-copy coincidences recovers the signed weight exactly, including its sign. -/
theorem unitaryHalfWeight_of_marked_sector (k : ℕ) :
    unitaryHalfWeight k = (unitarySectorMoment (smallUnitarySubsets k) 2 : ℤ) -
      unitarySectorMoment ((smallUnitarySubsets k).erase ∅) 2 + 1 - (smallUnitarySubsets k).card := by
  let F := smallUnitarySubsets k
  have h0 : ∅ ∈ F := by
    refine mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),?_⟩
    simp only [primePowerSubset,prod_empty]
    exact prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1).pos _
  have even0 : Even (∅ : Finset ℕ).card := ⟨0,rfl⟩
  have ins : insert (∅ : Finset ℕ) (F.erase ∅) = F := insert_erase h0
  have he : (unitaryParityCounts F).1 = (unitaryParityCounts (F.erase ∅)).1 + 1 := by
    conv_lhs => rw [← ins]
    simp [unitaryParityCounts,filter_insert,even0]
  have ho : (unitaryParityCounts F).2 = (unitaryParityCounts (F.erase ∅)).2 := by
    conv_lhs => rw [← ins]
    simp [unitaryParityCounts,filter_insert,even0]
  rw [← unitaryParityCounts_diff,← unitaryParityCounts_total]
  change ((unitaryParityCounts F).1 : ℤ) - (unitaryParityCounts F).2 =
    (unitarySectorMoment F 2 : ℤ) - unitarySectorMoment (F.erase ∅) 2 + 1 -
      ((unitaryParityCounts F).1 + (unitaryParityCounts F).2 : ℕ)
  simp only [unitarySectorMoment,he,ho,Nat.cast_add,Nat.cast_one,Nat.cast_pow]
  ring


end
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
