import GaloisForLFunctions.RHTower.MobiusFriableLargestPrimeDecomposition

/-!
# Splitting smooth windows by the largest prime

Removing one copy of the largest prime factor gives a disjoint
partition for every pair of cutoffs, with repeated prime factors retained.
-/
open Finset
open scoped Classical
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev smooth (y Z : ℕ) := RHTower.Sieve.smoothUpTo (Nat.primesLE y) Z

private def block (Z p : ℕ) := (smooth p (Z/p)).image (fun m => p*m)

private theorem greatest {p Z n : ℕ} (hp : p.Prime) (hn : n ∈ block Z p) :
    p ∈ n.primeFactors ∧ ∀ q ∈ n.primeFactors,q ≤ p := by
  obtain ⟨m,hm,rfl⟩ := mem_image.mp hn
  obtain ⟨⟨mp,_⟩,fac⟩ := RHTower.mem_smoothUpTo_iff.mp hm
  have pos : p*m ≠ 0 := Nat.mul_ne_zero hp.ne_zero (by omega)
  refine ⟨Nat.mem_primeFactors.mpr ⟨hp,dvd_mul_right ..,pos⟩,?_⟩
  intro q hq
  obtain ⟨prime,dvd,_⟩ := Nat.mem_primeFactors.mp hq
  rcases prime.dvd_mul.mp dvd with atP|atM
  · exact Nat.le_of_dvd hp.pos atP
  · exact fac q (Nat.mem_primeFactors.mpr ⟨prime,atM,by omega⟩)

private theorem disjoint_blocks (y Z : ℕ) :
    (↑(Nat.primesLE y) : Set ℕ).PairwiseDisjoint (block Z) := by
  intro p hp q hq ne
  apply disjoint_left.mpr
  intro n hn hm
  have P := greatest (Nat.mem_primesLE.mp hp).2 hn
  have Q := greatest (Nat.mem_primesLE.mp hq).2 hm
  exact ne (le_antisymm (Q.2 _ P.1) (P.2 _ Q.1))

private theorem all_blocks (y Z : ℕ) :
    (smooth y Z).erase 1 = (Nat.primesLE y).biUnion (block Z) := by
  ext n
  constructor
  · intro hn
    obtain ⟨hne,hs⟩ := mem_erase.mp hn
    obtain ⟨⟨lo,hi⟩,small⟩ := RHTower.mem_smoothUpTo_iff.mp hs
    have nonempty := Nat.nonempty_primeFactors.mpr (show 1 < n by omega)
    let p := n.primeFactors.max' nonempty
    have hp : p ∈ n.primeFactors := max'_mem _ nonempty
    obtain ⟨prime,dvd,_⟩ := Nat.mem_primeFactors.mp hp
    have eq := Nat.mul_div_cancel' dvd
    have mp := Nat.div_pos (Nat.le_of_dvd (by omega) dvd) prime.pos
    refine mem_biUnion.mpr ⟨p,Nat.mem_primesLE.mpr ⟨small p hp,prime⟩,mem_image.mpr ⟨n/p,?_,eq⟩⟩
    refine RHTower.mem_smoothUpTo_iff.mpr ⟨⟨mp,Nat.div_le_div_right hi⟩,?_⟩
    intro q hq
    have sub : n/p ∣ n := calc
      n/p ∣ p*(n/p) := dvd_mul_left ..
      _ = n := eq
    have qdvd := (Nat.dvd_of_mem_primeFactors hq).trans sub
    exact le_max' _ _ (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hq,qdvd,by omega⟩)
  · intro hn
    obtain ⟨p,hp,member⟩ := mem_biUnion.mp hn
    obtain ⟨pc,prime⟩ := Nat.mem_primesLE.mp hp
    have f := greatest prime member
    obtain ⟨m,hm,rfl⟩ := mem_image.mp member
    obtain ⟨⟨mp,mZ⟩,_⟩ := RHTower.mem_smoothUpTo_iff.mp hm
    have first : p ≤ p*m := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left p mp
    refine mem_erase.mpr ⟨by have := prime.one_lt;omega,RHTower.mem_smoothUpTo_iff.mpr ?_⟩
    exact ⟨⟨prime.pos.trans_le first,(Nat.mul_le_mul_left p mZ).trans (Nat.mul_div_le Z p)⟩,
      fun q hq => (f.2 q hq).trans pc⟩

/-- Splitting by the largest prime applies to every additive weight and
both independent cutoffs. The unit is omitted on both sides. -/
theorem sum_smooth_nonunits_by_largest_prime {A : Type*} [AddCommMonoid A] (f : ℕ → A)
    (y Z : ℕ) :
    ∑ n ∈ (RHTower.Sieve.smoothUpTo (Nat.primesLE y) Z).erase 1,f n =
      ∑ p ∈ Nat.primesLE y,∑ m ∈ RHTower.Sieve.smoothUpTo (Nat.primesLE p) (Z/p),f (p*m) := by
  rw [all_blocks,Finset.sum_biUnion (disjoint_blocks y Z)]
  apply sum_congr rfl
  intro p hp
  exact sum_image (fun m _ n _ eq => Nat.eq_of_mul_eq_mul_left (Nat.mem_primesLE.mp hp).2.pos eq)

/-- The exact smooth-number recurrence, valid beyond the first prime square. -/
theorem count_smooth_by_largest_prime (y Z : ℕ) :
    (RHTower.Sieve.smoothUpTo (Nat.primesLE y) Z).card = (if 0 < Z then 1 else 0) +
      ∑ p ∈ Nat.primesLE y,(RHTower.Sieve.smoothUpTo (Nat.primesLE p) (Z/p)).card := by
  have count := sum_smooth_nonunits_by_largest_prime (fun _ => (1:ℕ)) y Z
  simp only [sum_const, nsmul_one, Nat.cast_id] at count
  by_cases hZ : 0 < Z
  · have one : 1 ∈ smooth y Z := RHTower.mem_smoothUpTo_iff.mpr ⟨⟨le_rfl,hZ⟩,by simp⟩
    rw [if_pos hZ,←count,Nat.add_comm,card_erase_add_one one]
  · have one : 1 ∉ smooth y Z := fun h => hZ (RHTower.mem_smoothUpTo_iff.mp h).1.2
    rw [if_neg hZ,zero_add,←count,erase_eq_of_notMem one]

end GaloisForLFunctions.RestrictedFactorizationCalculus
