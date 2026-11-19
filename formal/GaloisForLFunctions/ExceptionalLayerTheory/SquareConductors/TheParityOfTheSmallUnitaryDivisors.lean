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
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Product of the full prime powers attached to a subset of the prime support. -/
def primePowerSubset (k : ℕ) (S : Finset ℕ) : ℕ := ∏ p ∈ S,p^k.factorization p

/-- Subsets whose full prime-power product is on the smaller side. -/
def smallUnitarySubsets (k : ℕ) : Finset (Finset ℕ) :=
  k.primeFactors.powerset.filter
    (fun S => primePowerSubset k S ≤ primePowerSubset k (k.primeFactors \ S))

/-- Signed count of unitary divisors on the smaller side of the square root. -/
def unitaryHalfWeight (k : ℕ) : ℤ := ∑ S ∈ smallUnitarySubsets k, (-1:ℤ)^S.card

private theorem complement_twice {S P : Finset ℕ} (h : S ⊆ P) : P \ (P \ S)=S := by
  ext p
  simp only [mem_sdiff]
  exact ⟨fun hh => by by_contra hn; exact hh.2 ⟨hh.1,hn⟩,fun hp => ⟨h hp,fun hh => hh.2 hp⟩⟩

private theorem subset_product_pos {k : ℕ} {S : Finset ℕ} (h : S ⊆ k.primeFactors) :
    0 < primePowerSubset k S := prod_pos fun _ hp => pow_pos (Nat.prime_of_mem_primeFactors (h hp)).pos _

private theorem complementary_prime_power_products {k : ℕ} (hk : 0 < k) {S : Finset ℕ} (h : S ⊆ k.primeFactors) :
    primePowerSubset k S*primePowerSubset k (k.primeFactors \ S)=k := by
  unfold primePowerSubset
  rw [mul_comm,prod_sdiff h]
  exact (Nat.prod_primeFactors_pow_factorization hk.ne').symm

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
  change (primePowerSubset k S).gcd (primePowerSubset k S)=1 at hc
  rw [Nat.gcd_self] at hc
  have hm := complementary_prime_power_products (by omega : 0 < k) h
  rw [←hsame,hc,one_mul] at hm
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
    exact ⟨fun hh => lt_of_le_of_ne hh (Ne.symm (complementary_products_ne hk h)),LT.lt.le⟩
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
  have hn : P.Nonempty := Nat.nonempty_primeFactors.mpr hk
  let v := ∑ S ∈ P.powerset.filter small,(-1:ℤ)^S.card
  have twice : v+v=0 := calc
    _ = v+∑ S ∈ P.powerset.filter (fun S => ¬small S),(-1:ℤ)^S.card := congrArg (v+·) same
    _ = ∑ S ∈ P.powerset,(-1:ℤ)^S.card := sum_filter_add_sum_filter_not _ _ _
    _ = 0 := sum_powerset_neg_one_pow_card_of_nonempty hn
  change v=0
  linarith only [twice]

/-- A dominant prime-power block leaves every subset of the other blocks
on the smaller side. -/
theorem small_unitary_subsets_of_dominant {k p : ℕ} (hk : 1 < k) (hp : p ∈ k.primeFactors)
    (hbig : k < (p^k.factorization p)^2) :
    smallUnitarySubsets k=(k.primeFactors.erase p).powerset := by
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
  change P.powerset.filter small=(P.erase p).powerset
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

/-- The dominant-block price is one on pure powers and zero otherwise. -/
theorem unitary_half_weight_dominant {k p : ℕ} (hk : 1 < k) (hp : p ∈ k.primeFactors)
    (hbig : k < (p^k.factorization p)^2) :
    unitaryHalfWeight k=if k.primeFactors.erase p=∅ then 1 else 0 := by
  rw [unitaryHalfWeight,small_unitary_subsets_of_dominant hk hp hbig,sum_powerset_neg_one_pow_card]

/-- An integer supported on a single prime has unit weight, including all
proper powers of that prime. -/
theorem unitary_half_weight_singleton {k p : ℕ} (hk : 1 < k) (hs : k.primeFactors={p}) :
    unitaryHalfWeight k=1 := by
  have hp : p ∈ k.primeFactors := by rw [hs]; exact mem_singleton_self p
  have hprod := Nat.prod_primeFactors_pow_factorization (by omega : k ≠ 0)
  rw [hs,prod_singleton] at hprod
  have hbig : k < (p^k.factorization p)^2 := by rw [←hprod]; nlinarith only [hk]
  rw [unitary_half_weight_dominant hk hp hbig,hs]
  simp

/-- Three prime-power blocks below the square root have exactly four
small subset products, the unit and the three individual blocks. -/
theorem unitary_half_weight_balanced_triple {k : ℕ} (hk : 1 < k) (hthree : k.primeFactors.card=3)
    (hbal : ∀ p ∈ k.primeFactors, (p^k.factorization p)^2 < k) : unitaryHalfWeight k= -2 := by
  let P := k.primeFactors
  let small (S : Finset ℕ) := primePowerSubset k S ≤ primePowerSubset k (P \ S)
  have below {S : Finset ℕ} (hs : S ⊆ P) (hcard : S.card ≤ 1) :
      primePowerSubset k S < primePowerSubset k (P \ S) := by
    have hm := complementary_prime_power_products (by omega : 0 < k) hs
    have hsq : (primePowerSubset k S)^2 < k := by
      by_cases hz : S.card=0
      · rw [card_eq_zero.mp hz]
        simpa only [primePowerSubset,prod_empty,one_pow] using hk
      · obtain ⟨p,rfl⟩ := card_eq_one.mp (by omega : S.card=1)
        simpa only [primePowerSubset,prod_singleton] using hbal p (hs (mem_singleton_self p))
    by_contra! h
    exact hsq.not_ge (hm.symm.trans_le ((Nat.mul_le_mul_left (primePowerSubset k S) h).trans_eq
      (pow_two _).symm))
  have hset : P.powerset.filter small=P.powerset.filter (fun S => S.card ≤ 1) := by
    ext S
    simp only [mem_filter,mem_powerset,and_congr_right_iff]
    intro hs
    constructor
    · intro hsm
      by_contra! hmany
      have hc : (P \ S).card ≤ 1 := by
        rw [card_sdiff_of_subset hs]
        change k.primeFactors.card-S.card ≤ 1
        omega
      have h := below (S:=P \ S) sdiff_subset hc
      rw [complement_twice hs] at h
      exact h.not_ge hsm
    · exact fun h => (below hs h).le
  change (∑ S ∈ P.powerset.filter small,(-1:ℤ)^S.card)= -2
  rw [hset,_root_.RHTower.Sieve.sum_powerset_filter_card_le P 1 (fun j => (-1:ℤ)^j)]
  change (∑ j ∈ range (1+1),k.primeFactors.card.choose j • (-1:ℤ)^j)= -2
  rw [hthree]
  norm_num [sum_range_succ]

/-- Every surviving integer other than a pure prime power has odd support
of size at least three, with all prime-power blocks strictly below its square root. -/
theorem unitary_half_weight_support {k : ℕ} (hk : 1 < k) (hw : unitaryHalfWeight k ≠ 0)
    (hmulti : k.primeFactors.card ≠ 1) :
    Odd k.primeFactors.card ∧ 3 ≤ k.primeFactors.card ∧
      ∀ p ∈ k.primeFactors, (p^k.factorization p)^2 < k := by
  have hodd := Nat.not_even_iff_odd.mp (fun he => hw (unitary_half_weight_even hk he))
  refine ⟨hodd,?_,?_⟩
  · obtain ⟨j,hj⟩ := hodd
    omega
  · intro p hp
    have hne : k.primeFactors.erase p ≠ ∅ := by
      intro hz
      have hc := Finset.card_erase_of_mem hp
      rw [hz,card_empty] at hc
      have hpos := card_pos.mpr (show k.primeFactors.Nonempty from ⟨p,hp⟩)
      omega
    have hle : (p^k.factorization p)^2 ≤ k := by
      by_contra! hh
      exact hw ((unitary_half_weight_dominant hk hp hh).trans (if_neg hne))
    apply hle.lt_of_ne
    intro heq
    have hs : ({p}:Finset ℕ) ⊆ k.primeFactors := singleton_subset_iff.mpr hp
    have hprod := complementary_prime_power_products (by omega : 0 < k) hs
    have hn := complementary_products_ne hk hs
    have hsingle : primePowerSubset k {p}=p^k.factorization p := by simp [primePowerSubset]
    rw [hsingle] at hprod hn
    rw [pow_two] at heq
    exact hn (Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.prime_of_mem_primeFactors hp).pos _)
      (heq.trans hprod.symm))

/-- Every small subset omits at least one block. If every block is below
the square root, it must omit at least two. -/
theorem small_unitary_subset_card {k : ℕ} (hk : 1 < k) {S : Finset ℕ}
    (hS : S ∈ smallUnitarySubsets k) :
    S.card < k.primeFactors.card ∧
      ((∀ p ∈ k.primeFactors, (p^k.factorization p)^2 < k) →
        S.card+1 < k.primeFactors.card) := by
  obtain ⟨hs,hsmall⟩ := mem_filter.mp hS
  have hsub := mem_powerset.mp hs
  have hm := complementary_prime_power_products (by omega : 0 < k) hsub
  have hlt := lt_of_le_of_ne hsmall (complementary_products_ne hk hsub)
  have hc := card_sdiff_of_subset hsub
  have hcomp : (k.primeFactors \ S).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.mp h] at hlt
    have hpos := subset_product_pos hsub
    simp only [primePowerSubset,prod_empty] at hlt
    change 0 < ∏ p ∈ S,p^k.factorization p at hpos
    omega
  have hpos := card_pos.mpr hcomp
  refine ⟨by omega,?_⟩
  intro hbal
  by_contra! hcard
  obtain ⟨q,hq⟩ := card_eq_one.mp (by omega : (k.primeFactors \ S).card=1)
  have hqmem : q ∈ k.primeFactors \ S := by rw [hq]; exact mem_singleton_self q
  have hb := hbal q (mem_sdiff.mp hqmem).1
  have hsingle : primePowerSubset k (k.primeFactors \ S)=q^k.factorization q := by
    rw [hq]; simp only [primePowerSubset,prod_singleton]
  rw [hsingle] at hsmall hm
  exact hb.not_ge (hm.symm.trans_le ((Nat.mul_le_mul_right _ hsmall).trans_eq (pow_two _).symm))

/-- For two prime-power blocks with the larger block a prime, only the
unit and the smaller block contribute to the weighted small-divisor sum. -/
theorem small_unitary_pair_price (w : ℕ → ℤ) {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : 0<a) (hlt : p^a<q) :
    (∑ S ∈ smallUnitarySubsets (p^a*q),w (primePowerSubset (p^a*q) S))=w 1+w (p^a) := by
  let k := p^a*q
  have hpa := pow_pos hp.pos a
  have hpq := (Nat.le_of_dvd hpa (dvd_pow_self p ha.ne')).trans_lt hlt
  have hqnd := Nat.not_dvd_of_pos_of_lt hpa hlt
  have hpnd : ¬p ∣ q := fun h => hpq.ne ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
  have hP : k.primeFactors=({p,q}:Finset ℕ) := by
    dsimp only [k]
    rw [Nat.primeFactors_mul hpa.ne' hq.ne_zero,Nat.primeFactors_pow p ha.ne',hp.primeFactors,hq.primeFactors]
    simp
  have hqexp : k.factorization q=1 := by
    dsimp only [k]
    rw [Nat.factorization_mul hpa.ne' hq.ne_zero,Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hqnd,hq.factorization_self,zero_add]
  have hpexp : k.factorization p=a := by
    dsimp only [k]
    rw [Nat.factorization_mul hpa.ne' hq.ne_zero,Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpnd,Nat.factorization_pow_self hp,add_zero]
  have hk := hq.one_lt.trans_le (Nat.le_mul_of_pos_left q hpa)
  have hbig : k < (q^k.factorization q)^2 := by
    rw [hqexp,pow_one,pow_two]
    exact Nat.mul_lt_mul_of_pos_right hlt hq.pos
  have hqmem : q ∈ k.primeFactors := by simp [hP]
  change (∑ S ∈ smallUnitarySubsets k,w (primePowerSubset k S))=_
  rw [small_unitary_subsets_of_dominant hk hqmem hbig,hP]
  simp [Finset.powerset_insert,primePowerSubset,hpq.ne,hpq.ne.symm,hpexp,add_comm]

/-- Any normalization assigning the unit weight one and killing all
two-block products forces weight minus one on every prime-power block
and total weight minus two on every balanced triple. -/
theorem small_unitary_pair_rigidity (w : ℕ → ℤ) (hunit : w 1=1) :
    (∀ p q a : ℕ, p.Prime → q.Prime → 0<a → p^a<q →
      (∑ S ∈ smallUnitarySubsets (p^a*q),w (primePowerSubset (p^a*q) S))=0) ↔
    (∀ p a : ℕ, p.Prime → 0<a → w (p^a)= -1) ∧
      (∀ k : ℕ, 1<k → k.primeFactors.card=3 →
        (∀ p ∈ k.primeFactors, (p^k.factorization p)^2<k) →
        (∑ S ∈ smallUnitarySubsets k,w (primePowerSubset k S))= -2) := by
  constructor
  · intro h
    have hv (p a : ℕ) (hp : p.Prime) (ha : 0<a) : w (p^a)= -1 := by
      obtain ⟨q,hqle,hq⟩ := Nat.exists_infinite_primes (p^a+1)
      have hr := h p q a hp hq ha hqle
      rw [small_unitary_pair_price w hp hq ha hqle,hunit] at hr
      omega
    refine ⟨hv,fun k hk ht hb => ?_⟩
    rw [←unitary_half_weight_balanced_triple hk ht hb]
    apply sum_congr rfl
    intro S hS
    have hc := (small_unitary_subset_card hk hS).2 hb
    rw [ht] at hc
    rcases Nat.eq_zero_or_pos S.card with he | he
    · rw [card_eq_zero.mp he]
      simp [primePowerSubset,hunit]
    · obtain ⟨p,hp⟩ := card_eq_one.mp (by omega : S.card=1)
      have hps : p ∈ S := by rw [hp]; exact mem_singleton_self p
      have hmem := mem_powerset.mp (mem_filter.mp hS).1 hps
      obtain ⟨hprime,hd,hk0⟩ := Nat.mem_primeFactors.mp hmem
      rw [hp]
      simp [primePowerSubset,hv p _ hprime (hprime.factorization_pos_of_dvd hk0 hd)]
  · rintro ⟨h,_⟩ p q a hp hq ha hlt
    rw [small_unitary_pair_price w hp hq ha hlt,hunit,h p a hp ha]
    norm_num

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
