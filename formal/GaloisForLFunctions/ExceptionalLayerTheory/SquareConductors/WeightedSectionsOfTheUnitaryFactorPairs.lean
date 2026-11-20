import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePivotalBlockAtTheUnitaryMidpoint
import Mathlib.Algebra.BigOperators.Associated

/-!
# Weighted sections of unitary factor pairs

Selecting whole prime-power blocks gives all coprime ordered factorizations
of a positive integer. Both the size of the chosen factor and its prime
support can be kept in a weighted sum over any arithmetic section.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem subset_factor_pos {k : ℕ} {S : Finset ℕ} (hs : S ⊆ k.primeFactors) :
    0 < primePowerSubset k S :=
  prod_pos fun _ hp => pow_pos (Nat.prime_of_mem_primeFactors (hs hp)).pos _

private theorem subset_complement_eq {k : ℕ} (hk : 0 < k) {S : Finset ℕ}
    (hs : S ⊆ k.primeFactors) :
    primePowerSubset k S*primePowerSubset k (k.primeFactors \ S)=k := by
  unfold primePowerSubset
  rw [mul_comm,prod_sdiff hs]
  exact (Nat.prod_primeFactors_pow_factorization hk.ne').symm

private theorem subset_complement_coprime {k : ℕ} {S : Finset ℕ} (hs : S ⊆ k.primeFactors) :
    (primePowerSubset k S).Coprime (primePowerSubset k (k.primeFactors \ S)) := by
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  apply Nat.Coprime.pow
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (hs hp))
    (Nat.prime_of_mem_primeFactors (mem_sdiff.mp hq).1)).mpr (fun he => (mem_sdiff.mp hq).2 (he ▸ hp))

private theorem support_of_subset {k : ℕ} {S : Finset ℕ} (hs : S ⊆ k.primeFactors) :
    (primePowerSubset k S).primeFactors=S := by
  ext p
  constructor
  · intro hp
    obtain ⟨hp',hd,_⟩ := Nat.mem_primeFactors.mp hp
    unfold primePowerSubset at hd
    obtain ⟨q,hq,hdiv⟩ := hp'.prime.exists_mem_finset_dvd hd
    have he := (Nat.prime_dvd_prime_iff_eq hp' (Nat.prime_of_mem_primeFactors (hs hq))).mp
      (hp'.dvd_of_dvd_pow hdiv)
    simpa only [he] using hq
  · intro hp
    obtain ⟨hp',hd,hk⟩ := Nat.mem_primeFactors.mp (hs hp)
    exact Nat.mem_primeFactors.mpr ⟨hp',(dvd_pow_self p (hp'.factorization_pos_of_dvd hk hd).ne').trans
      (dvd_prod_of_mem (fun q => q^k.factorization q) hp),(subset_factor_pos hs).ne'⟩

private theorem reconstruct_unitary {k d : ℕ} (hk : 0 < k) (hd : d ∣ k)
    (hc : d.Coprime (k/d)) : primePowerSubset k d.primeFactors=d := by
  have hm := Nat.mul_div_cancel' hd
  have hdp : 0 < d := Nat.pos_of_dvd_of_pos hd hk
  have hrp : 0 < k/d := Nat.div_pos (Nat.le_of_dvd hk hd) hdp
  calc primePowerSubset k d.primeFactors = ∏ p ∈ d.primeFactors,p^d.factorization p := by
         apply prod_congr rfl
         intro p hp
         obtain ⟨hpr,hpd,_⟩ := Nat.mem_primeFactors.mp hp
         have hn := hpr.coprime_iff_not_dvd.mp (hc.of_dvd_left hpd)
         have hfac := congrArg (fun n : ℕ => n.factorization p) hm
         simp only [Nat.factorization_mul hdp.ne' hrp.ne',Finsupp.add_apply,
           Nat.factorization_eq_zero_of_not_dvd hn,add_zero] at hfac
         rw [hfac]
       _ = d := (Nat.prod_primeFactors_pow_factorization hdp.ne').symm

/-- Reindex a weighted section of the block cube by its actual unitary
divisors. The prime support of the chosen divisor recovers the full pattern. -/
theorem unitary_sum_on_divisor_section {M : Type*} [AddCommMonoid M]
    {k : ℕ} (hk : 0<k) (test : ℕ → Prop) [DecidablePred test] (w : ℕ → Finset ℕ → M) :
    (∑ S ∈ k.primeFactors.powerset.filter (fun S => test (primePowerSubset k S)),
      w (primePowerSubset k S) S)=
    ∑ d ∈ k.divisors.filter (fun d => d.Coprime (k/d) ∧ test d), w d d.primeFactors := by
  apply sum_nbij' (primePowerSubset k) Nat.primeFactors
  · intro S hS
    obtain ⟨inside,cond⟩ := mem_filter.mp hS
    have sub := mem_powerset.mp inside
    have mul := subset_complement_eq hk sub
    have div := Nat.mul_div_cancel_left (primePowerSubset k (k.primeFactors \ S)) (subset_factor_pos sub)
    rw [mul] at div
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨⟨_,mul.symm⟩,hk.ne'⟩,
      div.symm ▸ subset_complement_coprime sub,cond⟩
  · intro d hd
    obtain ⟨div,cop,cond⟩ := mem_filter.mp hd
    have hdvd := (Nat.mem_divisors.mp div).1
    exact mem_filter.mpr ⟨mem_powerset.mpr (Nat.primeFactors_mono hdvd hk.ne'),
      (reconstruct_unitary hk hdvd cop).symm ▸ cond⟩
  · exact fun S hS => support_of_subset (mem_powerset.mp (mem_filter.mp hS).1)
  · exact fun d hd => reconstruct_unitary hk (Nat.mem_divisors.mp (mem_filter.mp hd).1).1
      (mem_filter.mp hd).2.1
  · intro S hS
    rw [support_of_subset (mem_powerset.mp (mem_filter.mp hS).1)]

/-- The prime support after removing the full power of p. -/
theorem unitary_cofactor_primeFactors (k p : ℕ) :
    (ordCompl[p] k).primeFactors=k.primeFactors.erase p := by
  rw [←Nat.support_factorization,Nat.factorization_ordCompl,Finsupp.support_erase,Nat.support_factorization]

private theorem cofactor_product {k p : ℕ} {S : Finset ℕ} (sub : S⊆(ordCompl[p] k).primeFactors) :
    primePowerSubset (ordCompl[p] k) S=primePowerSubset k S := by
  rw [unitary_cofactor_primeFactors] at sub
  apply prod_congr rfl
  intro q hq
  rw [Nat.factorization_ordCompl,Finsupp.erase_ne (mem_erase.mp (sub hq)).1]

private theorem small_square {k : ℕ} (hk : 0<k) {S : Finset ℕ} (hs : S⊆k.primeFactors) :
    S∈smallUnitarySubsets k ↔ (primePowerSubset k S)^2≤k := by
  simp only [smallUnitarySubsets,mem_filter,mem_powerset,hs,true_and,unitarySubset_small_iff_square hk hs]

private theorem block_cap {k p d : ℕ} (hp : p∈k.primeFactors) :
    (p^k.factorization p*d)^2≤k ↔ p^k.factorization p*d^2≤ordCompl[p] k := by
  let b := p^k.factorization p
  let n := ordCompl[p] k
  have pos : 0<b := pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  have prod : b*n=k := Nat.ordProj_mul_ordCompl_eq_self k p
  change (b*d)^2≤k ↔ b*d^2≤n
  rw [show (b*d)^2=b*(b*d^2) by ring,←prod]
  exact ⟨fun h => Nat.le_of_mul_le_mul_left h pos,fun h => Nat.mul_le_mul_left b h⟩

/-- Exact arithmetic detection window on the conductor with its full
p-power removed. The endpoints are squared integers. -/
theorem unitary_pivot_cofactor_window {k p : ℕ} (hp : p∈k.primeFactors) (S : Finset ℕ) :
    let n := ordCompl[p] k
    let d := primePowerSubset n S
    S∈unitaryPivots k p ↔ S⊆n.primeFactors ∧ d^2≤k ∧ n<p^k.factorization p*d^2 := by
  intro n d
  have support : n.primeFactors=k.primeFactors.erase p := unitary_cofactor_primeFactors k p
  have big (u : ℕ) : k<(p^k.factorization p*u)^2 ↔ n<p^k.factorization p*u^2 := by
    simpa only [not_le] using not_congr (block_cap (d:=u) hp)
  rw [unitaryPivots,mem_filter,mem_powerset,←support]
  apply and_congr_right
  intro sub
  have eq : d=primePowerSubset k S := cofactor_product (k:=k) (p:=p) sub
  rw [eq,big]

/-- Forcing p absent, present, or deleting it from the conductor gives
three explicit cuts on the same cofactor divisor. -/
theorem unitary_cofactor_cut_sections {k p : ℕ} (hp : p∈k.primeFactors) {S : Finset ℕ}
    (sub : S⊆(ordCompl[p] k).primeFactors) :
    let n := ordCompl[p] k
    let d := primePowerSubset n S
    (S∈smallUnitarySubsets k ↔ d^2≤k) ∧
      (insert p S∈smallUnitarySubsets k ↔ p^k.factorization p*d^2≤n) ∧
      (S∈smallUnitarySubsets n ↔ d^2≤n) := by
  intro n d
  have hk := Nat.pos_of_ne_zero (Nat.mem_primeFactors.mp hp).2.2
  have eq : d=primePowerSubset k S := cofactor_product (k:=k) (p:=p) sub
  have ss := sub
  rw [unitary_cofactor_primeFactors] at ss
  have ps := ss.trans (erase_subset p k.primeFactors)
  have fresh : p∉S := fun h => notMem_erase p k.primeFactors (ss h)
  refine ⟨?_,?_,small_square (Nat.ordCompl_pos p hk.ne') sub⟩
  · rw [eq]
    exact small_square hk ps
  · rw [small_square hk (insert_subset hp ps),
      show primePowerSubset k (insert p S)=p^k.factorization p*primePowerSubset k S from prod_insert fresh,
      block_cap hp]
    rw [eq]

#print axioms unitary_cofactor_cut_sections
#print axioms unitary_pivot_cofactor_window
#print axioms unitary_sum_on_divisor_section
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
