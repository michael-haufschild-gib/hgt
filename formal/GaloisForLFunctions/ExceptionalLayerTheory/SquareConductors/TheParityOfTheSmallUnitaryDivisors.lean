import GaloisForLFunctions.RHTower.Sieve.TruncatedMoebius
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Choose.Sum

/-!
# Parity at the smaller unitary divisor

A subset of the prime-power factors of k and its complement give coprime
integers with product k. In even parity their signs agree. A factor larger
than its complementary product removes itself from every small divisor.
-/

open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Product of the full prime powers attached to a subset of the prime support. -/
def primePowerSubset (k : ℕ) (S : Finset ℕ) : ℕ := ∏ p ∈ S,p^k.factorization p

/-- Signed count of unitary divisors on the smaller side of the square root. -/
def unitaryHalfWeight (k : ℕ) : ℤ :=
  ∑ S ∈ k.primeFactors.powerset.filter
    (fun S => primePowerSubset k S ≤ primePowerSubset k (k.primeFactors \ S)), (-1:ℤ)^S.card

private theorem complement_twice {S P : Finset ℕ} (h : S ⊆ P) : P \ (P \ S)=S := by
  ext p
  simp only [mem_sdiff]
  exact ⟨fun hh => by by_contra hn; exact hh.2 ⟨hh.1,hn⟩,fun hp => ⟨h hp,fun hh => hh.2 hp⟩⟩

private theorem subset_product_pos {k : ℕ} {S : Finset ℕ} (h : S ⊆ k.primeFactors) :
    0 < primePowerSubset k S := prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors (h hp)).pos _

private theorem complementary_prime_power_products {k : ℕ} (hk : 0 < k) {S : Finset ℕ} (h : S ⊆ k.primeFactors) :
    primePowerSubset k S*primePowerSubset k (k.primeFactors \ S)=k := by
  rw [primePowerSubset,primePowerSubset,mul_comm,prod_sdiff h,←Nat.prod_primeFactors_pow_factorization hk.ne']

private theorem complementary_products_ne {k : ℕ} (hk : 1 < k) {S : Finset ℕ} (h : S ⊆ k.primeFactors) :
    primePowerSubset k S ≠ primePowerSubset k (k.primeFactors \ S) := by
  have hc : (primePowerSubset k S).Coprime (primePowerSubset k (k.primeFactors \ S)) := by
    apply Nat.Coprime.prod_left
    intro p hp
    apply Nat.Coprime.prod_right
    intro q hq
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors (h hp))
      (Nat.prime_of_mem_primeFactors (mem_sdiff.mp hq).1)).mpr (fun he => (mem_sdiff.mp hq).2 (he ▸ hp)))
  intro hsame
  rw [←hsame] at hc
  have hone := Nat.coprime_self.mp hc
  have hm := complementary_prime_power_products (by omega : 0 < k) h
  rw [←hsame,hone,one_mul] at hm
  omega

private theorem complement_sign {k : ℕ} (hpar : Even k.primeFactors.card) {S : Finset ℕ} (h : S ⊆ k.primeFactors) :
    (-1:ℤ)^S.card=(-1:ℤ)^(k.primeFactors \ S).card := by
  have hlen : S.card+(k.primeFactors \ S).card=k.primeFactors.card := by
    rw [card_sdiff_of_subset h]; have := card_le_card h; omega
  have hmul : (-1:ℤ)^S.card*(-1:ℤ)^(k.primeFactors \ S).card=1 := by rw [←pow_add,hlen,hpar.neg_one_pow]
  have hsq : (-1:ℤ)^S.card*(-1:ℤ)^S.card=1 := by rw [←mul_pow]; norm_num
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) (hsq.trans hmul.symm)

/-- The smaller unitary divisors have zero total sign whenever a nonunit
has an even number of distinct primes, with arbitrary multiplicities. -/
theorem unitary_half_weight_even {k : ℕ} (hk : 1 < k) (hpar : Even k.primeFactors.card) :
    unitaryHalfWeight k=0 := by
  let P := k.primeFactors
  let small (S : Finset ℕ) := primePowerSubset k S ≤ primePowerSubset k (P \ S)
  have flip {S : Finset ℕ} (h : S ⊆ P) : small (P \ S) ↔ ¬small S := by
    dsimp only [small]
    rw [complement_twice h,not_le]
    exact le_iff_lt_of_ne (Ne.symm (complementary_products_ne hk h))
  have same : (∑ S ∈ P.powerset.filter small,(-1:ℤ)^S.card) =
      ∑ S ∈ P.powerset.filter (fun S => ¬small S),(-1:ℤ)^S.card := by
    apply sum_nbij' (fun S => P \ S) (fun S => P \ S)
    · intro S hS
      obtain ⟨hs,hsm⟩ := mem_filter.mp hS
      have h := mem_powerset.mp hs
      exact mem_filter.mpr ⟨mem_powerset.mpr sdiff_subset,(fun hneg => (flip h).mp hneg hsm)⟩
    · intro S hS
      obtain ⟨hs,hsm⟩ := mem_filter.mp hS
      exact mem_filter.mpr ⟨mem_powerset.mpr sdiff_subset,(flip (mem_powerset.mp hs)).mpr hsm⟩
    · exact fun S hS => complement_twice (mem_powerset.mp (mem_filter.mp hS).1)
    · exact fun S hS => complement_twice (mem_powerset.mp (mem_filter.mp hS).1)
    · exact fun S hS => complement_sign hpar (mem_powerset.mp (mem_filter.mp hS).1)
  have total := sum_filter_add_sum_filter_not P.powerset small (fun S => (-1:ℤ)^S.card)
  have hn : P.Nonempty := Nat.nonempty_primeFactors.mpr hk
  rw [sum_powerset_neg_one_pow_card_of_nonempty hn,←same] at total
  change (∑ S ∈ P.powerset.filter small,(-1:ℤ)^S.card)=0
  omega

#print axioms unitary_half_weight_even

/-- A dominant prime-power block leaves the complete alternating sum on
the remaining blocks. This gives one on pure powers and zero otherwise. -/
theorem unitary_half_weight_dominant {k p : ℕ} (hk : 1 < k) (hp : p ∈ k.primeFactors)
    (hbig : k < (p^k.factorization p)^2) :
    unitaryHalfWeight k=if k.primeFactors.erase p=∅ then 1 else 0 := by
  let P := k.primeFactors
  let small (S : Finset ℕ) := primePowerSubset k S ≤ primePowerSubset k (P \ S)
  have large {S : Finset ℕ} (hs : S ⊆ P) (hpS : p ∈ S) : ¬small S := by
    have hd : p^k.factorization p ∣ primePowerSubset k S := dvd_prod_of_mem _ hpS
    have hl := Nat.le_of_dvd (subset_product_pos hs) hd
    have hm := complementary_prime_power_products (by omega : 0 < k) hs
    intro h
    have hsq := (Nat.mul_le_mul hl hl).trans (Nat.mul_le_mul_left (primePowerSubset k S) h)
    rw [hm,←pow_two] at hsq
    omega
  have hset : P.powerset.filter small=(P.erase p).powerset := by
    ext S
    simp only [mem_filter,mem_powerset]
    constructor
    · rintro ⟨hs,hsm⟩ q hq
      exact mem_erase.mpr ⟨fun he => large hs (he ▸ hq) hsm,hs hq⟩
    · intro h
      have hs := h.trans (erase_subset p P)
      have hpn : p ∉ S := fun hh => (mem_erase.mp (h hh)).1 rfl
      have hn := large (S:=P \ S) sdiff_subset (mem_sdiff.mpr ⟨hp,hpn⟩)
      dsimp only [small] at hn ⊢
      rw [complement_twice hs] at hn
      exact ⟨hs,(lt_of_not_ge hn).le⟩
  change (∑ S ∈ P.powerset.filter small,(-1:ℤ)^S.card)=_
  rw [hset,sum_powerset_neg_one_pow_card]

#print axioms unitary_half_weight_dominant

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
