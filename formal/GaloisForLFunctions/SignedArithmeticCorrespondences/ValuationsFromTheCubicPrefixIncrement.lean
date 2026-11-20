import GaloisForLFunctions.SignedArithmeticCorrespondences.CountingTheTrianglesOfThePrimeContactMatrix
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PrimePowerMangoldtReindex

/-!
# Prime valuations in consecutive cubic spectra

The cubic spectral increment is a sum of triangular numbers of the
prime valuations. Its defect under multiplication is exactly a positive
Gram form on the valuation rows. In particular its vanishing detects
coprimality of two integers using only three scalar increments.
-/
noncomputable section
open Finset ArithmeticFunction
open scoped ArithmeticFunction.vonMangoldt
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
namespace GaloisForLFunctions.SignedArithmeticCorrespondences.PrimeContactMoments

/-- The difference between the cubic traces after and before adding site n. -/
def jump (n : ℕ) : ℝ := Matrix.trace ((primeContactMatrix 0 n)^3)-
  Matrix.trace ((primeContactMatrix 0 (n-1))^3)

private theorem jump_divisors {n : ℕ} (hn : n≠0) : jump n=6*∑ t∈n.divisors,trianglePrice t := by
  obtain ⟨B,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simpa [jump] using cubic_prefix_increment B

private theorem split_by_prime {n t : ℕ} (hn : n≠0) (ht : t∈n.divisors) :
    trianglePrice t=∑ p∈n.primeFactors,if p∣t then trianglePrice t else 0 := by
  classical
  by_cases h : Λ t=0
  · simp [trianglePrice,h]
  obtain ⟨p,b,hp,hb,hpow⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp h)
  have hpdiv : p∣t := hpow ▸ dvd_pow_self p hb.ne'
  have hpmem := Nat.mem_primeFactors.mpr ⟨hp,hpdiv.trans (Nat.dvd_of_mem_divisors ht),hn⟩
  rw [sum_eq_single_of_mem p hpmem,if_pos hpdiv]
  intro q hq hne
  apply if_neg
  intro hqd
  rw [←hpow] at hqd
  have hqp := Nat.prime_of_mem_primeFactors hq
  exact hne ((Nat.prime_dvd_prime_iff_eq hqp hp).mp (hqp.dvd_of_dvd_pow hqd))

private def triangular (v : ℝ) := v*(v-1)/2

private theorem sum_first_powers (n : ℕ) : (∑ j∈range n,(j:ℝ))=triangular n := by
  induction n with
  | zero => simp [triangular]
  | succ n ih => rw [sum_range_succ,ih]; push_cast; unfold triangular; ring

private theorem prime_share {p n : ℕ} (hp : p.Prime) (hn : n≠0) :
    (∑ t∈n.divisors,if p∣t then trianglePrice t else 0)=
      triangular (n.factorization p)*Real.log p^3 := by
  rw [show (∑ t∈n.divisors,if p∣t then trianglePrice t else 0)=
      ∑ j∈range (n.factorization p),(Λ*Λ) (p^(j+1))*Real.log p from
    sum_divisors_primePower_mangoldt hp hn (Λ*Λ)]
  have hterm (j : ℕ) : (Λ*Λ) (p^(j+1))*Real.log p=(j:ℝ)*Real.log p^3 := by
    rw [GaloisForLFunctions.HTGeometry.vonMangoldt_mul_self_prime_pow hp (Nat.succ_pos j)]
    push_cast;ring
  simp_rw [hterm]
  rw [←sum_mul,sum_first_powers]

/-- A closed formula for the size of the cubic trace jump. Each prime
contributes once per unordered pair of its occurrences in n. -/
theorem cubic_jump_valuations {n : ℕ} (hn : n≠0) :
    jump n=3*∑ p∈n.primeFactors,(n.factorization p:ℝ)*((n.factorization p:ℝ)-1)*Real.log p^3 := by
  rw [jump_divisors hn,sum_congr rfl (fun _ ht => split_by_prime hn ht),sum_comm]
  have h := sum_congr rfl (fun p (hp : p∈n.primeFactors) => prime_share (Nat.prime_of_mem_primeFactors hp) hn)
  rw [h,mul_sum,mul_sum]
  exact sum_congr rfl fun p _ => by unfold triangular;ring

private theorem supported_jump {n : ℕ} (hn : n≠0) {P : Finset ℕ} (hP : n.primeFactors⊆P) :
    jump n=3*∑ p∈P,(n.factorization p:ℝ)*((n.factorization p:ℝ)-1)*Real.log p^3 := by
  rw [cubic_jump_valuations hn]
  congr 1
  apply sum_subset hP
  intro p _ hp
  have hz : n.factorization p=0 := by
    simpa only [←Nat.support_factorization,Finsupp.notMem_support_iff] using hp
  rw [hz,Nat.cast_zero,zero_mul,zero_mul]

/-- Polarization of cubic trace increments recovers the valuation inner product. -/
theorem cubic_jump_product_defect {m n : ℕ} (hm : m≠0) (hn : n≠0) :
    jump (m*n)-jump m-jump n =
      6*∑ p∈m.primeFactors ∪ n.primeFactors,
        (m.factorization p:ℝ)*(n.factorization p:ℝ)*Real.log p^3 := by
  let P := m.primeFactors∪n.primeFactors
  have hp : (m*n).primeFactors=P := Nat.primeFactors_mul hm hn
  rw [supported_jump (mul_ne_zero hm hn) hp.le,
    supported_jump hm (show m.primeFactors⊆P from subset_union_left),
    supported_jump hn (show n.primeFactors⊆P from subset_union_right),
    mul_sum,mul_sum,mul_sum,mul_sum,←sum_sub_distrib,←sum_sub_distrib]
  refine sum_congr rfl fun p _ => ?_
  rw [Nat.factorization_mul hm hn,Finsupp.add_apply,Nat.cast_add]
  ring

/-- Coprimality is precisely additivity of the scalar spectral increment. -/
theorem cubic_jump_additive_iff_coprime {m n : ℕ} (hm : m≠0) (hn : n≠0) :
    jump (m*n)=jump m+jump n ↔ m.Coprime n := by
  let P := m.primeFactors∪n.primeFactors
  have hnon (p : ℕ) (h : p∈P) :
      0≤(m.factorization p:ℝ)*(n.factorization p:ℝ)*Real.log p^3 := by
    have hprime : p.Prime := (mem_union.mp h).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (pow_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)) _)
  have h := cubic_jump_product_defect hm hn
  constructor
  · intro he
    have hz : (∑ p∈P,(m.factorization p:ℝ)*(n.factorization p:ℝ)*Real.log p^3)=0 := by linarith only [h,he]
    by_contra hnc
    obtain ⟨p,hp,hdm,hdn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hmem : p∈P := mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hp,hdm,hm⟩)
    have hterm := (sum_eq_zero_iff_of_nonneg hnon).mp hz p hmem
    have hmp : (0:ℝ)<m.factorization p := Nat.cast_pos.mpr (hp.factorization_pos_of_dvd hm hdm)
    have hnp : (0:ℝ)<n.factorization p := Nat.cast_pos.mpr (hp.factorization_pos_of_dvd hn hdn)
    have hl := Real.log_pos (show (1:ℝ)<p by exact_mod_cast hp.one_lt)
    exact (mul_pos (mul_pos hmp hnp) (pow_pos hl 3)).ne' hterm
  · intro hc
    have hz : (∑ p∈P,(m.factorization p:ℝ)*(n.factorization p:ℝ)*Real.log p^3)=0 := by
      apply sum_eq_zero
      intro p hP
      have hp : p.Prime := (mem_union.mp hP).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
      by_cases hd : p∣m
      · rw [Nat.factorization_eq_zero_of_not_dvd (fun he => (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,hp,hd,he⟩) hc),Nat.cast_zero,mul_zero,zero_mul]
      · rw [Nat.factorization_eq_zero_of_not_dvd hd,Nat.cast_zero,zero_mul,zero_mul]
    linarith only [h,hz]

end GaloisForLFunctions.SignedArithmeticCorrespondences.PrimeContactMoments
