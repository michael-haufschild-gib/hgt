import GaloisForLFunctions.BiScaleUncertainty.CubicSievePhaseRecovery
import GaloisForLFunctions.BiScaleUncertainty.EvenPrimePairMomentCalculus

/-!
# Actual finite odd-prime sieve families

Four-point divisor weights realize each coordinate at twice an odd prime.
Finite sums cover every cutoff and arbitrary real coefficients. Their literal
sieve responses are parity times centered residue rows, with exact coordinate
and response formulas also valid for empty sectors and zero coefficients.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

private theorem divisors_two_prime {p q : ℕ} (hp : Nat.Prime p) :
    q ∣ 2*p ↔ q = 1 ∨ q = 2 ∨ q = p ∨ q = 2*p := by
  constructor
  · rintro ⟨t,ht⟩
    have h2 : 2 ∣ q*t := by rw [← ht]; exact dvd_mul_right 2 p
    rcases Nat.prime_two.dvd_mul.mp h2 with hq | ht2
    · obtain ⟨a,rfl⟩ := hq
      have hp' : p = a*t := by nlinarith [ht]
      rcases hp.eq_one_or_self_of_dvd a ⟨t,hp'⟩ with ha | ha
      · right; left; omega
      · right; right; right; omega
    · obtain ⟨a,rfl⟩ := ht2
      have hp' : p = q*a := by nlinarith [ht]
      rcases hp.eq_one_or_self_of_dvd q ⟨a,hp'⟩ with hq | hq
      · exact Or.inl hq
      · exact Or.inr (Or.inr (Or.inl hq))
  · rintro (rfl | rfl | rfl | rfl) <;> simp

/-- A literal divisor-weight atom supported at one, two, an odd prime, and twice that prime. -/
def oddPrimeAtom (p d : ℕ) : ℝ :=
  (if d = 1 then 1 else 0) - (if d = 2 then 2 else 0) -
    (if d = p then (p : ℝ) else 0) + (if d = 2*p then ((2*p : ℕ) : ℝ) else 0)

private theorem coordinate_point (N t : ℕ) (ht : t ∈ Finset.Icc 1 N) (q : ℕ) :
    selbergMultiplesCoord N (fun d => if d = t then (t : ℝ) else 0) q =
      if q ∣ t then 1 else 0 := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp ht).1)
  unfold selbergMultiplesCoord
  rw [Finset.sum_filter]
  calc
    _ = ∑ d ∈ Finset.Icc 1 N, if d = t then (if q ∣ t then (1 : ℝ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : d = t
      · subst d; simp [ht0]
      · simp [hd]
    _ = _ := by simp [ht]

/-- The atom has exactly one nonzero multiples coordinate. -/
theorem coordinate_oddPrimeAtom {N p : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hN : 2*p ≤ N) (q : ℕ) :
    selbergMultiplesCoord N (oddPrimeAtom p) q = if q = 2*p then 1 else 0 := by
  have hp3 : 3 ≤ p := by obtain ⟨j,hj⟩ := ho; have := hp.two_le; omega
  have h1 : 1 ∈ Finset.Icc 1 N := by simp; omega
  have h2 : 2 ∈ Finset.Icc 1 N := by simp; omega
  have hpm : p ∈ Finset.Icc 1 N := by simp; omega
  have h2p : 2*p ∈ Finset.Icc 1 N := by simp; omega
  have hx : selbergMultiplesCoord N (oddPrimeAtom p) q =
      selbergMultiplesCoord N (fun d => if d = 1 then (1 : ℝ) else 0) q -
      selbergMultiplesCoord N (fun d => if d = 2 then (2 : ℝ) else 0) q -
      selbergMultiplesCoord N (fun d => if d = p then (p : ℝ) else 0) q +
      selbergMultiplesCoord N (fun d => if d = 2*p then ((2*p : ℕ) : ℝ) else 0) q := by
    simp only [selbergMultiplesCoord,oddPrimeAtom,sub_div,add_div,
      Finset.sum_sub_distrib,Finset.sum_add_distrib]
  have hc1 := coordinate_point N 1 h1 q
  have hc2 := coordinate_point N 2 h2 q
  norm_num only [Nat.cast_one,Nat.cast_ofNat] at hc1 hc2
  rw [hx,hc1,hc2,coordinate_point N p hpm,coordinate_point N (2*p) h2p]
  simp only [Nat.dvd_one,Nat.dvd_prime Nat.prime_two,Nat.dvd_prime hp,divisors_two_prime hp]
  by_cases hq1 : q = 1 <;> by_cases hq2 : q = 2 <;>
    by_cases hqp : q = p <;> by_cases hq2p : q = 2*p <;> simp_all
  all_goals omega

/-- Admissible odd-prime modes at a given cutoff; zero cutoff gives an empty sector. -/
def oddPrimeModes (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ Odd p ∧ 2*p ≤ N)

/-- Membership records only primality, oddness, and the actual cutoff. -/
theorem mem_oddPrimeModes {N p : ℕ} :
    p ∈ oddPrimeModes N ↔ Nat.Prime p ∧ Odd p ∧ 2*p ≤ N := by
  unfold oddPrimeModes
  simp only [Finset.mem_filter,Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · rintro ⟨hp,ho,hN⟩
    exact ⟨⟨by have := hp.two_le; omega,by omega⟩,hp,ho,hN⟩

instance oddPrimeMode_neZero {N : ℕ} (p : oddPrimeModes N) : NeZero (p : ℕ) :=
  ⟨(mem_oddPrimeModes.mp p.property).1.ne_zero⟩

/-- Arbitrary finite odd-prime coefficients realized by explicit actual divisor weights. -/
def primeFamilyWeight (N : ℕ) (a : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ p : oddPrimeModes N, a p * oddPrimeAtom p d

/-- Exact coordinate profile, including every zero and every order outside the prime sector. -/
theorem coordinate_primeFamilyWeight (N : ℕ) (a : ℕ → ℝ) (q : ℕ) :
    selbergMultiplesCoord N (primeFamilyWeight N a) q =
      ∑ p : oddPrimeModes N, if q = 2*(p : ℕ) then a p else 0 := by
  unfold selbergMultiplesCoord primeFamilyWeight
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  have hp := mem_oddPrimeModes.mp p.property
  have heq := coordinate_oddPrimeAtom hp.1 hp.2.1 hp.2.2 q
  change (∑ d ∈ (Finset.Icc 1 N).filter (fun d => q ∣ d), a p * oddPrimeAtom p d / d) = _
  simp_rw [mul_div_assoc]
  rw [← Finset.mul_sum,← selbergMultiplesCoord,heq]
  split_ifs <;> simp

/-- Each retained prime coefficient is recovered exactly at twice its prime. -/
theorem coordinate_primeFamilyWeight_at (N : ℕ) (a : ℕ → ℝ) (p : oddPrimeModes N) :
    selbergMultiplesCoord N (primeFamilyWeight N a) (2*(p : ℕ)) = a p := by
  rw [coordinate_primeFamilyWeight]
  have heq (q : oddPrimeModes N) : (2*(p : ℕ) = 2*(q : ℕ)) ↔ q = p := by
    constructor
    · intro h; apply Subtype.ext; omega
    · intro h; simp [h]
  simp_rw [heq]
  simp

private theorem response_point (N t : ℕ) (ht : t ∈ Finset.Icc 1 N) (w : ℝ) (n : ℕ) :
    sieveSeq N (fun d => if d = t then w else 0) n = if t ∣ n then w else 0 := by
  unfold sieveSeq
  rw [Finset.sum_filter]
  calc
    _ = ∑ d ∈ Finset.Icc 1 N, if d = t then (if t ∣ n then w else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : d = t
      · subst d; simp
      · simp [hd]
    _ = _ := by simp [ht]

/-- Every atom is a parity sign times a centered prime residue row. -/
theorem sieveSeq_oddPrimeAtom {N p : ℕ} [NeZero p] (hp : Nat.Prime p) (ho : Odd p)
    (hN : 2*p ≤ N) (n : ℕ) :
    sieveSeq N (oddPrimeAtom p) n = (if 2 ∣ n then 1 else -1) * residueRow p (n : ZMod p) := by
  have hp3 : 3 ≤ p := by obtain ⟨j,hj⟩ := ho; have := hp.two_le; omega
  have h1 : 1 ∈ Finset.Icc 1 N := by simp; omega
  have h2 : 2 ∈ Finset.Icc 1 N := by simp; omega
  have hpm : p ∈ Finset.Icc 1 N := by simp; omega
  have h2p : 2*p ∈ Finset.Icc 1 N := by simp; omega
  have hx : sieveSeq N (oddPrimeAtom p) n =
      sieveSeq N (fun d => if d = 1 then (1 : ℝ) else 0) n -
      sieveSeq N (fun d => if d = 2 then (2 : ℝ) else 0) n -
      sieveSeq N (fun d => if d = p then (p : ℝ) else 0) n +
      sieveSeq N (fun d => if d = 2*p then ((2*p : ℕ) : ℝ) else 0) n := by
    simp only [sieveSeq,oddPrimeAtom,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [hx,response_point N 1 h1,response_point N 2 h2,
    response_point N p hpm,response_point N (2*p) h2p]
  have hd : 2*p ∣ n ↔ 2 ∣ n ∧ p ∣ n := by
    constructor
    · intro h
      exact ⟨dvd_trans (dvd_mul_right 2 p) h,dvd_trans (dvd_mul_left p 2) h⟩
    · exact fun h => ho.coprime_two_left.mul_dvd_of_dvd_of_dvd h.1 h.2
  simp only [one_dvd,ite_true,residueRow,ZMod.natCast_eq_zero_iff,hd]
  by_cases h2n : 2 ∣ n <;> by_cases hpn : p ∣ n <;> simp [h2n,hpn] <;> ring

/-- The family response is literally a parity sign times the sum of independent residue rows. -/
theorem sieveSeq_primeFamilyWeight (N : ℕ) (a : ℕ → ℝ) (n : ℕ) :
    sieveSeq N (primeFamilyWeight N a) n =
      (if 2 ∣ n then 1 else -1) * ∑ p : oddPrimeModes N, a p * residueRow p (n : ZMod p) := by
  unfold sieveSeq primeFamilyWeight
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.mul_sum]
  have hp := mem_oddPrimeModes.mp p.property
  rw [← sieveSeq,sieveSeq_oddPrimeAtom hp.1 hp.2.1 hp.2.2]
  ring

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
