import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePivotalBlockAtTheUnitaryMidpoint
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A two-vertex change at the unitary square root

A block strictly between half the square root and the square root makes
the signed cube cut differ from a single-coordinate cut at exactly two
vertices. An odd cofactor times the preceding power of two realizes this
configuration without any restriction on the number of prime blocks.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem product_and_complement {k : ℕ} (hk : k ≠ 0) {S : Finset ℕ} (hs : S ⊆ k.primeFactors) :
    primePowerSubset k S * primePowerSubset k (k.primeFactors \ S) = k := by
  rw [primePowerSubset,primePowerSubset,mul_comm,prod_sdiff hs]
  exact (Nat.prod_primeFactors_pow_factorization hk).symm

/-- Replacing the full opposite face vertex by the distinguished singleton
gives the entire small-divisor downset. -/
theorem small_unitary_subsets_one_exchange {k p : ℕ} (hp : p ∈ k.primeFactors)
    (hl : (p^k.factorization p)^2 < k) (hu : k < (2*p^k.factorization p)^2) :
    let B := k.primeFactors.erase p
    smallUnitarySubsets k = insert {p} (B.powerset.erase B) := by
  let P := k.primeFactors
  let B := P.erase p
  let b := p^k.factorization p
  have hk := (Nat.mem_primeFactors.mp hp).2.2
  have hs : ({p} : Finset ℕ) ⊆ P := singleton_subset_iff.mpr hp
  have mon {S A : Finset ℕ} (hSA : S ⊆ A) (hA : A ⊆ P) : primePowerSubset k S ≤ primePowerSubset k A :=
    prod_le_prod_of_subset_of_one_le hSA (fun _ _ => Nat.zero_le _)
      (fun q hq _ => Nat.succ_le_of_lt (pow_pos (Nat.prime_of_mem_primeFactors (hA hq)).pos _))
  have big {S : Finset ℕ} (hS : S ⊆ P) (hps : p ∈ S) (hne : S ≠ {p}) :
      k < (primePowerSubset k S)^2 := by
    obtain ⟨q,hq,hqp⟩ : ∃ q ∈ S, q ≠ p := by
      by_contra! h
      exact hne (Subset.antisymm (fun q hq => mem_singleton.mpr (h q hq)) (singleton_subset_iff.mpr hps))
    have hpr := Nat.mem_primeFactors.mp (hS hq)
    have he := hpr.1.factorization_pos_of_dvd hk hpr.2.1
    have htwo : 2 ≤ q^k.factorization q := (Nat.one_lt_pow (by omega) hpr.1.one_lt)
    have hpair := mon (show insert q {p} ⊆ S from insert_subset hq (singleton_subset_iff.mpr hps)) hS
    simp only [primePowerSubset,prod_insert (by simpa using hqp : q ∉ ({p} : Finset ℕ)),prod_singleton] at hpair
    exact hu.trans_le (Nat.pow_le_pow_left ((Nat.mul_le_mul_right b htwo).trans hpair) 2)
  have single : {p} ∈ smallUnitarySubsets k := by
    refine mem_filter.mpr ⟨mem_powerset.mpr hs,(unitarySubset_small_iff_square (Nat.pos_of_ne_zero hk) hs).mpr ?_⟩
    simpa only [primePowerSubset,prod_singleton] using hl.le
  have sdiff : P \ {p} = B := sdiff_singleton_eq_erase _ _
  have notB : B ∉ smallUnitarySubsets k := by
    intro h
    have hcomp : P \ B = {p} := sdiff ▸ Finset.sdiff_sdiff_eq_self hs
    have hle := (mem_filter.mp h).2
    change primePowerSubset k B ≤ primePowerSubset k (P \ B) at hle
    rw [hcomp] at hle
    have hm := product_and_complement hk hs
    change primePowerSubset k {p} * primePowerSubset k (P \ {p}) = k at hm
    rw [sdiff] at hm
    have hh := (Nat.mul_le_mul_left (primePowerSubset k {p}) hle)
    rw [hm] at hh
    exact hl.not_ge (by simpa only [primePowerSubset,prod_singleton,pow_two] using hh)
  intro B'
  change smallUnitarySubsets k = insert {p} (B.powerset.erase B)
  ext S
  rw [mem_insert,mem_erase,mem_powerset]
  constructor
  · intro hm
    by_cases he : S={p}
    · exact Or.inl he
    obtain ⟨hS,hcut⟩ := mem_filter.mp hm
    have hSP := mem_powerset.mp hS
    have hsmall := (unitarySubset_small_iff_square (Nat.pos_of_ne_zero hk) hSP).mp hcut
    have hno : p ∉ S := fun hh => (big hSP hh he).not_ge hsmall
    exact Or.inr ⟨fun h => notB (h ▸ hm),fun q hq =>
      mem_erase.mpr ⟨fun eq => hno (eq ▸ hq),hSP hq⟩⟩
  · rintro (rfl | ⟨hne,hSB⟩)
    · exact single
    have hSP := hSB.trans (erase_subset ..)
    have hpC : p ∈ P \ S := mem_sdiff.mpr ⟨hp,fun hh => notMem_erase p P (hSB hh)⟩
    have hC : P \ S ≠ {p} := by
      intro he
      have h := congrArg (fun T => P \ T) he
      change P \ (P \ S) = P \ {p} at h
      rw [Finset.sdiff_sdiff_eq_self hSP,sdiff] at h
      exact hne h
    have hbig := big sdiff_subset hpC hC
    have hlarge := mt (unitarySubset_small_iff_square (Nat.pos_of_ne_zero hk)
      (S:=P \ S) sdiff_subset).mp hbig.not_ge
    change ¬ primePowerSubset k (P \ S) ≤ primePowerSubset k (P \ (P \ S)) at hlarge
    rw [Finset.sdiff_sdiff_eq_self hSP] at hlarge
    exact mem_filter.mpr ⟨mem_powerset.mpr hSP,(lt_of_not_ge hlarge).le⟩

/-- Every additive price sees only the exchange of the two exceptional
vertices. The background is a full cube on the other blocks. -/
theorem unitary_one_exchange_price {A : Type*} [AddCommGroup A] {k p : ℕ} (hp : p ∈ k.primeFactors)
    (hl : (p^k.factorization p)^2 < k) (hu : k < (2*p^k.factorization p)^2) (f : Finset ℕ → A) :
    let B := k.primeFactors.erase p
    (∑ S ∈ smallUnitarySubsets k, f S) + f B = f {p} + ∑ S ∈ B.powerset, f S := by
  intro B
  have hno : {p} ∉ B.powerset.erase B := by
    intro h
    exact notMem_erase p k.primeFactors (mem_powerset.mp (mem_erase.mp h).2 (mem_singleton_self p))
  rw [small_unitary_subsets_one_exchange hp hl hu,sum_insert hno,add_assoc,
    sum_erase_add _ _ (mem_powerset.mpr Subset.rfl)]

/-- A nearly dominant block forces the same price at every odd rank,
including ranks where the general balanced price is not determined. -/
theorem unitary_half_weight_one_exchange {k p : ℕ} (hp : p ∈ k.primeFactors)
    (hl : (p^k.factorization p)^2 < k) (hu : k < (2*p^k.factorization p)^2)
    (he : Even (k.primeFactors.erase p).card) (hn : (k.primeFactors.erase p).Nonempty) :
    unitaryHalfWeight k = -2 := by
  have h := unitary_one_exchange_price hp hl hu (fun S => (-1:ℤ)^S.card)
  simp only [he.neg_one_pow,card_singleton,pow_one,sum_powerset_neg_one_pow_card,
    if_neg (nonempty_iff_ne_empty.mp hn),add_zero] at h
  change (∑ S ∈ smallUnitarySubsets k, (-1:ℤ)^S.card) = _
  linarith only [h]

/-- Adjoin the largest power of two below an odd cofactor. -/
def dyadicUnitaryCompletion (m : ℕ) : ℕ := 2^(Nat.log 2 m)*m

private theorem dyadic_completion_data {m : ℕ} (hm : 1 < m) (hodd : ¬ 2 ∣ m) :
    let k := dyadicUnitaryCompletion m
    k.primeFactors = insert 2 m.primeFactors ∧ k.factorization 2 = Nat.log 2 m ∧
      (2^k.factorization 2)^2 < k ∧ k < (2*2^k.factorization 2)^2 := by
  intro k
  let a := Nat.log 2 m
  have ha : 0 < a := Nat.log_pos (by decide) hm
  have hm0 : m ≠ 0 := by omega
  have hb : 0 < 2^a := pow_pos (by decide) _
  have hl : 2^a < m := by
    apply (Nat.pow_log_le_self 2 hm0).lt_of_ne
    intro he
    exact hodd (he ▸ dvd_pow_self 2 ha.ne')
  have hu := Nat.lt_pow_succ_log_self (by decide : 1 < 2) m
  change m < 2^(a+1) at hu
  rw [pow_succ] at hu
  have factor : k.factorization 2 = a := by
    change (2^a*m).factorization 2 = _
    rw [Nat.factorization_mul hb.ne' hm0,Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,Nat.factorization_eq_zero_of_not_dvd hodd,add_zero]
  refine ⟨?_,factor,?_,?_⟩
  · change (2^a*m).primeFactors = _
    rw [Nat.primeFactors_mul hb.ne' hm0,Nat.primeFactors_pow 2 ha.ne',Nat.prime_two.primeFactors,
      singleton_union]
  · rw [factor,pow_two]
    exact Nat.mul_lt_mul_of_pos_left hl hb
  · rw [factor]
    change 2^a*m < (2*2^a)^2
    calc _ < 2^a*(2^a*2) := Nat.mul_lt_mul_of_pos_left hu hb
         _ ≤ _ := by nlinarith only [Nat.zero_le ((2^a)^2)]

/-- Every odd cofactor with a positive even number of primes gives price
minus two after dyadic completion. No size conditions between its primes
are required. -/
theorem dyadic_completion_midpoint {m : ℕ} (hm : 1 < m) (hodd : ¬ 2 ∣ m)
    (he : Even m.primeFactors.card) : unitaryHalfWeight (dyadicUnitaryCompletion m) = -2 := by
  obtain ⟨hs,_,hl,hu⟩ := dyadic_completion_data hm hodd
  have h2 : 2 ∉ m.primeFactors := fun h => hodd (Nat.mem_primeFactors.mp h).2.1
  have hp : 2 ∈ (dyadicUnitaryCompletion m).primeFactors := hs ▸ mem_insert_self ..
  have hB : (dyadicUnitaryCompletion m).primeFactors.erase 2 = m.primeFactors := by
    rw [hs,erase_insert h2]
  exact unitary_half_weight_one_exchange hp hl hu (hB ▸ he) (hB ▸ Nat.nonempty_primeFactors.mpr hm)

private theorem odd_cofactor_of_rank (r : ℕ) :
    ∃ m : ℕ, 0 < m ∧ ¬ 2 ∣ m ∧ m.primeFactors.card = r := by
  induction r with
  | zero => exact ⟨1,by decide,by decide,by simp⟩
  | succ r ih =>
    obtain ⟨m,hm,hodd,hr⟩ := ih
    obtain ⟨p,hpbig,hp⟩ := Nat.exists_infinite_primes (m+2)
    have hp2 : ¬ 2 ∣ p := by
      intro hd
      rcases (Nat.dvd_prime hp).mp hd with hh|hh <;> omega
    have hpm : p ∉ m.primeFactors := by
      intro h
      have := Nat.le_of_dvd hm (Nat.mem_primeFactors.mp h).2.1
      omega
    refine ⟨p*m,Nat.mul_pos hp.pos hm,fun hd => (Nat.prime_two.dvd_mul.mp hd).elim hp2 hodd,?_⟩
    rw [Nat.primeFactors_mul hp.ne_zero hm.ne',hp.primeFactors,singleton_union,card_insert_of_notMem hpm,hr]

/-- Balanced integers of every odd block count at least three realize
the triple price exactly. -/
theorem balanced_minus_two_at_every_odd_rank (r : ℕ) :
    ∃ k : ℕ, k.primeFactors.card = 2*r+3 ∧
      (∀ p ∈ k.primeFactors, (p^k.factorization p)^2 < k) ∧ unitaryHalfWeight k = -2 := by
  obtain ⟨m,_,hodd,hr⟩ := odd_cofactor_of_rank (2*r+2)
  have hm : 1 < m := Nat.nonempty_primeFactors.mp (card_pos.mp (by omega))
  have he : Even m.primeFactors.card := ⟨r+1,by omega⟩
  let k := dyadicUnitaryCompletion m
  have hneg := dyadic_completion_midpoint hm hodd he
  obtain ⟨hs,_,_,_⟩ := dyadic_completion_data hm hodd
  have hk : k.primeFactors.card = 2*r+3 := by
    rw [show k.primeFactors = _ from hs,card_insert_of_notMem (fun h => hodd (Nat.mem_primeFactors.mp h).2.1),hr]
  refine ⟨k,hk,fun p hp => ?_,hneg⟩
  have hprime := Nat.mem_primeFactors.mp hp
  have hk1 := Nat.nonempty_primeFactors.mp ⟨p,hp⟩
  rcases lt_trichotomy ((p^k.factorization p)^2) k with h|h|h
  · exact h
  · have hh := congrArg (fun n : ℕ => n.factorization p) h
    rw [← pow_mul,Nat.factorization_pow_self hprime.1] at hh
    have := hprime.1.factorization_pos_of_dvd hprime.2.2 hprime.2.1
    omega
  · have hh := unitary_half_weight_dominant hk1 hp h
    change unitaryHalfWeight k = -2 at hneg
    rw [hneg] at hh
    split_ifs at hh

private theorem dyadic_cofactor_le_sqrt {m X : ℕ} (hk : dyadicUnitaryCompletion m ≤ X) :
    m ≤ Nat.sqrt (2*X) := by
  apply Nat.le_sqrt.mpr
  have h := Nat.lt_pow_succ_log_self (by decide : 1<2) m
  rw [pow_succ] at h
  calc m*m ≤ (2^Nat.log 2 m*2)*m := Nat.mul_le_mul_right m h.le
       _ = 2*dyadicUnitaryCompletion m := by unfold dyadicUnitaryCompletion; ring
       _ ≤ _ := Nat.mul_le_mul_left 2 hk

/-- The entire dyadically completed family costs only a square root times
one logarithm in the priced midpoint sum. The signs can represent either
adjacent window, coprimality restrictions, and arbitrary subsampling. -/
theorem dyadic_midpoint_price_bound (S : Finset ℕ) (X : ℕ) (w : ℕ → ℝ)
    (hS : ∀ k ∈ S, k ≤ X ∧ ∃ m : ℕ, 1<m ∧ ¬ 2 ∣ m ∧ Even m.primeFactors.card ∧
      k=dyadicUnitaryCompletion m) (hw : ∀ k ∈ S, |w k| ≤ 1) :
    |∑ k ∈ S, w k*Real.log k*(unitaryHalfWeight k:ℝ)| ≤
      2*Real.log X*((Nat.sqrt (2*X):ℝ)+1) := by
  have sub : S ⊆ (range (Nat.sqrt (2*X)+1)).image dyadicUnitaryCompletion := by
    intro k hk
    obtain ⟨hle,m,_,_,_,rfl⟩ := hS k hk
    exact mem_image.mpr ⟨m,mem_range.mpr (Nat.lt_succ_of_le (dyadic_cofactor_le_sqrt hle)),rfl⟩
  have hc := (card_le_card sub).trans card_image_le
  rw [card_range] at hc
  have hl := Real.log_natCast_nonneg X
  have point (k : ℕ) (hk : k ∈ S) : |w k*Real.log k*(unitaryHalfWeight k:ℝ)| ≤ 2*Real.log X := by
    obtain ⟨hle,m,hm,hodd,he,hk'⟩ := hS k hk
    have hpos : 0 < k := by rw [hk',dyadicUnitaryCompletion]; positivity
    have hprice : unitaryHalfWeight k = -2 := hk' ▸ dyadic_completion_midpoint hm hodd he
    rw [hprice,abs_mul,abs_mul,abs_of_nonneg (Real.log_natCast_nonneg k)]
    have h := mul_le_mul (hw k hk) (Real.log_le_log (Nat.cast_pos.mpr hpos)
      (Nat.cast_le.mpr hle)) (Real.log_natCast_nonneg k) zero_le_one
    norm_num at h ⊢
    linarith only [h]
  calc _ ≤ ∑ k ∈ S, |w k*Real.log k*(unitaryHalfWeight k:ℝ)| := abs_sum_le_sum_abs ..
       _ ≤ ∑ _k ∈ S, 2*Real.log X := sum_le_sum point
       _ = 2*Real.log X*(S.card:ℝ) := by rw [sum_const,nsmul_eq_mul,mul_comm]
       _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (by positivity)

#print axioms dyadic_midpoint_price_bound
#print axioms dyadic_completion_midpoint
#print axioms balanced_minus_two_at_every_odd_rank
#print axioms small_unitary_subsets_one_exchange
#print axioms unitary_one_exchange_price
#print axioms unitary_half_weight_one_exchange
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
