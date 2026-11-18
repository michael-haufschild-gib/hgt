import GaloisForLFunctions.QuantitativeFactorizationMatching.OreDeficiencyAndCascadeConservation
import GaloisForLFunctions.RHTower.Sieve.BuchstabIdentity

/-!
# Signed terminal rows below a prime prefix

Deleting the least remaining prime partitions the nonunit squarefree tails
without multiplicities. The singleton tails give a prime boundary and every
longer tail gives a smaller quotient row with the opposite sign. Legendre
inversion also reads the entire remaining row directly at any stopping level.
-/

noncomputable section

open Finset ArithmeticFunction RHTower.Sieve
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Nonunit tails above a lower bound for the next prime. -/
def roughTails (L U y : ℕ) : Finset ℕ :=
  (squarefreeOf (Ioc (max 1 L) U)).filter (fun n => y < n.minFac)

/-- Surplus measured with the sign of the single-prime tails. -/
def tailBalance (L U y : ℕ) : ℤ := -∑ n ∈ roughTails L U y, μ n

/-- Membership with both sharp endpoints explicit. -/
theorem mem_roughTails {L U y n : ℕ} :
    n ∈ roughTails L U y ↔ 1 < n ∧ L < n ∧ n ≤ U ∧ Squarefree n ∧ y < n.minFac := by
  simp [roughTails,squarefreeOf,lt_min_iff,max_lt_iff,and_assoc]

private theorem append_smallest {m p : ℕ} (hm : 1 < m) (hp : p.Prime) (h : p < m.minFac) :
    (m*p).minFac = p ∧ m.Coprime p := by
  have hnd : ¬p ∣ m := fun hd => (Nat.minFac_le_of_dvd hp.two_le hd).not_gt h
  have hc := (hp.coprime_iff_not_dvd.mpr hnd).symm
  have hn : m*p ≠ 1 := by have := Nat.mul_le_mul_left m hp.two_le; omega
  have hd := Nat.minFac_prime hn
  have hle := Nat.minFac_le_of_dvd hp.two_le (dvd_mul_left p m)
  refine ⟨le_antisymm hle ?_,hc⟩
  rcases hd.dvd_mul.mp (Nat.minFac_dvd (m*p)) with hdvd | hdvd
  · exact h.le.trans (Nat.minFac_le_of_dvd hd.two_le hdvd)
  · exact ((Nat.prime_dvd_prime_iff_eq hd hp).1 hdvd).ge

/-- The least-prime fibre splits into a singleton and images of one smaller row. -/
theorem roughTails_minFac_fibre {L U y p : ℕ} (hp : p.Prime) (hpy : y<p) (hpU : p≤U) :
    (roughTails L U y).filter (fun n => n.minFac = p) =
      (if L<p then {p} else ∅) ∪
        (roughTails (L/p) (U/p) p).image (· * p) := by
  ext n
  constructor
  · intro hn
    obtain ⟨hn,hmin⟩ := mem_filter.mp hn
    obtain ⟨hn1,hL,hU,hsq,_⟩ := mem_roughTails.mp hn
    by_cases he : n=p
    · subst n; exact mem_union_left _ (by simp [hL])
    · apply mem_union_right
      have hdiv : p ∣ n := hmin ▸ Nat.minFac_dvd n
      let m := n / p
      have heq : m*p = n := Nat.div_mul_cancel hdiv
      have hc := Nat.squarefree_mul_iff.mp (show Squarefree (m*p) from heq ▸ hsq)
      have hm : 1<m := by
        by_contra! hh
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hh with h0 | h1
        · rw [h0,zero_mul] at heq; omega
        · rw [h1,one_mul] at heq; exact he heq.symm
      have hmp := Nat.minFac_prime (by omega : m ≠ 1)
      have hf : m.minFac ∣ n := heq ▸ dvd_mul_of_dvd_left (Nat.minFac_dvd m) p
      have hle : p ≤ m.minFac := hmin ▸ Nat.minFac_le_of_dvd hmp.two_le hf
      have hne : p ≠ m.minFac := fun h => (hp.coprime_iff_not_dvd.1 hc.1.symm)
        (h ▸ Nat.minFac_dvd m)
      exact mem_image.mpr ⟨m,mem_roughTails.mpr ⟨hm,(Nat.div_lt_iff_lt_mul hp.pos).2 (heq ▸ hL),
        (Nat.le_div_iff_mul_le hp.pos).2 (heq ▸ hU),hc.2.1,lt_of_le_of_ne hle hne⟩,heq⟩
  · intro hn
    rcases mem_union.mp hn with hs | ht
    · split_ifs at hs with hl
      · obtain rfl := mem_singleton.mp hs
        exact mem_filter.mpr ⟨mem_roughTails.mpr ⟨hp.one_lt,hl,hpU,Irreducible.squarefree hp,
          hp.minFac_eq ▸ hpy⟩,hp.minFac_eq⟩
      · exact False.elim (notMem_empty _ hs)
    · obtain ⟨m,hm,rfl⟩ := mem_image.mp ht
      obtain ⟨hm1,hL,hU,hmSq,hmin⟩ := mem_roughTails.mp hm
      obtain ⟨hmin',hc⟩ := append_smallest hm1 hp hmin
      have hn1 := hm1.trans_le (Nat.le_mul_of_pos_right m hp.pos)
      exact mem_filter.mpr ⟨mem_roughTails.mpr ⟨hn1,(Nat.div_lt_iff_lt_mul hp.pos).1 hL,
        (Nat.le_div_iff_mul_le hp.pos).1 hU,Nat.squarefree_mul_iff.mpr ⟨hc,hmSq,
          Irreducible.squarefree hp⟩,hmin' ▸ hpy⟩,hmin'⟩

private theorem singleton_disjoint (L U : ℕ) {p : ℕ} (hp : p.Prime) :
    Disjoint (if L < p then ({p} : Finset ℕ) else ∅)
      ((roughTails (L/p) (U/p) p).image (· * p)) := by
  split_ifs
  · apply disjoint_left.mpr
    intro n hn h
    obtain rfl := mem_singleton.mp hn
    obtain ⟨m,hm,he⟩ := mem_image.mp h
    have he' : m*p = 1*p := by simpa using he
    have hone := Nat.eq_of_mul_eq_mul_right hp.pos he'
    have := (mem_roughTails.mp hm).1
    omega
  · exact disjoint_empty_left

/-- Sharp signed recurrence. Each child has a strictly larger least-prime
threshold and upper endpoint at most half the parent's. The unit tail is
excluded at every level, so a prime endpoint is charged exactly once. -/
theorem tailBalance_recursion (L U y : ℕ) :
    tailBalance L U y =
      (((Nat.primesLE U).filter (fun p => max L y < p)).card : ℤ) -
      ∑ p ∈ (Nat.primesLE U).filter (fun p => y < p), tailBalance (L/p) (U/p) p := by
  classical
  let P := (Nat.primesLE U).filter (fun p => y<p)
  have hs : ∀ n ∈ roughTails L U y, n.minFac ∈ P := by
    intro n hn
    obtain ⟨hn1,_,hU,_,hmin⟩ := mem_roughTails.mp hn
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr
      ⟨(Nat.minFac_le (by omega)).trans hU,Nat.minFac_prime (by omega)⟩,hmin⟩
  have hrow (p : ℕ) (hp : p ∈ P) :
      ∑ n ∈ (roughTails L U y).filter (fun n => n.minFac = p), μ n =
        (if L < p then -1 else 0) + tailBalance (L/p) (U/p) p := by
    obtain ⟨hpU,hpy⟩ := mem_filter.mp hp
    obtain ⟨hple,hpr⟩ := Nat.mem_primesLE.mp hpU
    rw [roughTails_minFac_fibre hpr hpy hple,sum_union (singleton_disjoint L U hpr)]
    congr 1
    · split_ifs <;> simp [moebius_apply_prime hpr]
    · rw [sum_image (fun _ _ _ _ he => Nat.eq_of_mul_eq_mul_right hpr.pos he),tailBalance,
        ← sum_neg_distrib]
      apply sum_congr rfl
      intro m hm
      obtain ⟨hm1,_,_,_,ht⟩ := mem_roughTails.mp hm
      rw [isMultiplicative_moebius.map_mul_of_coprime (append_smallest hm1 hpr ht).2,
        moebius_apply_prime hpr,mul_neg_one]
  have hpr : (P.filter (fun p => L<p)) = (Nat.primesLE U).filter (fun p => max L y<p) := by
    ext p; simp [P,max_lt_iff,and_assoc,and_comm,and_left_comm]
  have hcount : (∑ p ∈ P, (if L<p then (-1:ℤ) else 0)) =
      -(((Nat.primesLE U).filter (fun p => max L y<p)).card : ℤ) := by
    rw [← sum_filter,hpr]; simp
  change -(∑ n ∈ roughTails L U y, μ n) = _ - ∑ p ∈ P, _
  rw [← sum_fiberwise_of_maps_to hs, sum_congr rfl hrow, sum_add_distrib,hcount]
  ring

/-- Exact divisor inversion of any terminal row at its own two endpoints. -/
theorem tailBalance_divisor_inversion (L U y : ℕ) :
    tailBalance L U y = -∑ n ∈ Ioc (max 1 L) U, μ n *
      ∑ d ∈ (n.gcd (siftModulus (y+1))).divisors, μ d := by
  unfold tailBalance roughTails squarefreeOf
  rw [sum_filter,sum_filter]
  congr 1
  apply sum_congr rfl
  intro n hn
  have h1 := (le_max_left 1 L).trans_lt (mem_Ioc.mp hn).1
  have h0 : 0 < n := by omega
  rw [← rho_eq_sum_divisors_moebius h0]
  by_cases hsq : Squarefree n
  · rw [if_pos hsq]
    by_cases h : y<n.minFac
    · have hr := rho_eq_one_of h0 (fun p hp => h.trans_le
        (Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hp).two_le (Nat.dvd_of_mem_primeFactors hp)))
      simp only [if_pos h,hr, Nat.cast_one,mul_one]
    · have hm : n.minFac ∈ n.primeFactors := Nat.mem_primeFactors.mpr
        ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd n,h0.ne'⟩
      have hz := rho_eq_zero_of_lt (z := y+1) hm (by omega)
      simp [h,hz]
  · simp [hsq,moebius_eq_zero_of_not_squarefree hsq]

/-- The root row gives the actual Möbius prefix at every integer cutoff. -/
theorem root_balance_eq_prefix (X : ℕ) :
    ∑ n ∈ Icc 1 X, μ n = (if X=0 then 0 else 1) - tailBalance 0 X 0 := by
  have hz : siftModulus 1 = 1 := by simp [siftModulus,Nat.primesBelow]
  rw [tailBalance_divisor_inversion]
  simp only [Nat.zero_add,hz,Nat.gcd_one_right,Nat.divisors_one,sum_singleton,
    ArithmeticFunction.moebius_apply_one,mul_one,max_eq_left (Nat.zero_le 1)]
  cases X with
  | zero => simp
  | succ X =>
    have he : Icc 1 (X+1) = insert 1 (Ioc 1 (X+1)) := by ext n; simp; omega
    rw [he,sum_insert (by simp)]
    simp

end GaloisForLFunctions.RestrictedFactorizationCalculus
