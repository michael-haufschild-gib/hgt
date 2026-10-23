import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Data.Nat.Prime.Pow
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Liouville parity at the cubic roughness boundary

Negative Liouville sign detects primes strictly below the cube of the least
prime factor. Prime cubes attain the boundary. On the resulting pair support,
the binary prime count is exactly a signed combination of Liouville moments.
These identities assert no positive lower bound for that count.
-/

namespace GaloisForLFunctions.Goldbach

open ArithmeticFunction Finset
open scoped BigOperators

set_option autoImplicit false

/-- Multiplying the least-factor bound over the prime factorization. -/
theorem minFac_pow_cardFactors_le (n : ℕ) :
    n.minFac ^ cardFactors n ≤ max 1 n := by
  by_cases hn : n = 0
  · subst n
    simp only [cardFactors_zero, pow_zero, max_eq_left (Nat.zero_le 1), le_refl]
  have listBound : ∀ l : List ℕ, (∀ p ∈ l, n.minFac ≤ p) →
      n.minFac ^ l.length ≤ l.prod := by
    intro l
    induction l with
    | nil =>
        intro _
        simp only [List.length_nil, pow_zero, List.prod_nil, le_refl]
    | cons p l ih =>
        intro hl
        rw [List.length_cons, pow_succ, List.prod_cons]
        calc
          n.minFac ^ l.length * n.minFac ≤ l.prod * p :=
            Nat.mul_le_mul
              (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))
              (hl p (List.mem_cons_self))
          _ = p * l.prod := Nat.mul_comm _ _
  calc
    n.minFac ^ cardFactors n ≤ n.primeFactorsList.prod :=
      listBound _ fun p hp => Nat.minFac_le_of_dvd
        (Nat.prime_of_mem_primeFactorsList hp).two_le
        (Nat.dvd_of_mem_primeFactorsList hp)
    _ = n := Nat.prod_primeFactorsList hn
    _ ≤ max 1 n := le_max_right _ _

/-- The negative-parity detector becomes exact below the least-factor cube. -/
theorem prime_iff_liouville_eq_neg_one_and_lt_minFac_cube (n : ℕ) :
    n.Prime ↔ liouville n = -1 ∧ n < n.minFac ^ 3 := by
  constructor
  · intro hp
    constructor
    · rw [liouville_apply hp.ne_zero, cardFactors_apply_prime hp, pow_one]
    · rw [hp.minFac_eq]
      calc
        n = n * 1 := (Nat.mul_one _).symm
        _ < n * (n * n) := Nat.mul_lt_mul_of_pos_left
          (by nlinarith [hp.two_le]) hp.pos
        _ = n ^ 3 := by ring
  · rintro ⟨hsign, hlt⟩
    have hn : n ≠ 0 := by
      intro h
      subst n
      simp only [ArithmeticFunction.map_zero] at hsign
      omega
    have hb : n.minFac ^ cardFactors n ≤ n := by
      simpa only [max_eq_right (Nat.one_le_iff_ne_zero.mpr hn)] using
        minFac_pow_cardFactors_le n
    have hc : cardFactors n < 3 := by
      by_contra hc
      have hp := Nat.pow_le_pow_right (Nat.minFac_pos n) (by omega : 3 ≤ cardFactors n)
      exact (not_le_of_gt hlt) (hp.trans hb)
    have hcases : cardFactors n = 0 ∨ cardFactors n = 1 ∨ cardFactors n = 2 := by omega
    rcases hcases with hzero | hone | htwo
    · rw [liouville_apply hn, hzero, pow_zero] at hsign
      omega
    · exact cardFactors_eq_one_iff_prime.mp hone
    · rw [liouville_apply hn, htwo] at hsign
      norm_num at hsign

/-- Prime cubes are negative-parity composites exactly on the boundary. -/
theorem prime_cube_parity_boundary (p : Nat.Primes) :
    liouville ((p : ℕ) ^ 3) = -1 ∧
      ¬ ((p : ℕ) ^ 3).Prime ∧
      ((p : ℕ) ^ 3).minFac = (p : ℕ) := by
  refine ⟨?_, ?_, p.prop.pow_minFac (by omega)⟩
  · rw [liouville_apply (pow_ne_zero _ p.prop.ne_zero), cardFactors_apply_prime_pow p.prop]
    ring
  · intro hp
    have hc := cardFactors_eq_one_iff_prime.mpr hp
    rw [cardFactors_apply_prime_pow p.prop] at hc
    omega

/-- No fixed roughness cutoff makes negative Liouville sign imply primality. -/
theorem exists_negativeParity_composite_above_cutoff (z : ℕ) :
    ∃ n : ℕ, z < n.minFac ∧ liouville n = -1 ∧ ¬ n.Prime := by
  obtain ⟨p, hzp, hp⟩ := Nat.exists_infinite_primes (z + 1)
  have hb := prime_cube_parity_boundary ⟨p, hp⟩
  refine ⟨p ^ 3, ?_, hb.1, hb.2.1⟩
  rw [hb.2.2]
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hzp

/-- Positive summands below the cubic threshold, with no smaller prime factor. -/
def cubicRoughPairs (N z : ℕ) : Finset (ℕ × ℕ) :=
  (antidiagonal N).filter fun ab =>
    0 < ab.1 ∧ 0 < ab.2 ∧ ab.1 < z ^ 3 ∧ ab.2 < z ^ 3 ∧
      z ≤ ab.1.minFac ∧ z ≤ ab.2.minFac

/-- Ordered prime pairs on the cubic rough support. -/
def cubicPrimePairCount (N z : ℕ) : ℕ :=
  ((cubicRoughPairs N z).filter fun ab => ab.1.Prime ∧ ab.2.Prime).card

/-- The prime count is the exact negative-negative Liouville projection. -/
theorem four_mul_cubicPrimePairCount (N z : ℕ) :
    4 * (cubicPrimePairCount N z : ℤ) =
      ∑ ab ∈ cubicRoughPairs N z,
        (1 - liouville ab.1 - liouville ab.2 + liouville ab.1 * liouville ab.2) := by
  have term : ∀ ab ∈ cubicRoughPairs N z,
      (1 - liouville ab.1) * (1 - liouville ab.2) =
        if ab.1.Prime ∧ ab.2.Prime then (4 : ℤ) else 0 := by
    intro ab hab
    obtain ⟨_, ha0, hb0, ha, hb, hza, hzb⟩ := mem_filter.mp hab
    have hta := ha.trans_le (Nat.pow_le_pow_left hza 3)
    have htb := hb.trans_le (Nat.pow_le_pow_left hzb 3)
    have hpa : ab.1.Prime ↔ liouville ab.1 = -1 := by
      simpa only [hta, and_true] using
        prime_iff_liouville_eq_neg_one_and_lt_minFac_cube ab.1
    have hpb : ab.2.Prime ↔ liouville ab.2 = -1 := by
      simpa only [htb, and_true] using
        prime_iff_liouville_eq_neg_one_and_lt_minFac_cube ab.2
    have hla : liouville ab.1 = 1 ∨ liouville ab.1 = -1 := by
      rw [liouville_apply (Nat.ne_of_gt ha0)]
      exact neg_one_pow_eq_or ℤ _
    have hlb : liouville ab.2 = 1 ∨ liouville ab.2 = -1 := by
      rw [liouville_apply (Nat.ne_of_gt hb0)]
      exact neg_one_pow_eq_or ℤ _
    rcases hla with hla | hla <;> rcases hlb with hlb | hlb <;>
      norm_num [hpa, hpb, hla, hlb]
  calc
    4 * (cubicPrimePairCount N z : ℤ) =
        ∑ ab ∈ cubicRoughPairs N z, if ab.1.Prime ∧ ab.2.Prime then (4 : ℤ) else 0 := by
      rw [cubicPrimePairCount, ← sum_boole (fun ab : ℕ × ℕ => ab.1.Prime ∧ ab.2.Prime),
        mul_sum]
      apply sum_congr rfl
      intro ab _
      split_ifs <;> ring
    _ = ∑ ab ∈ cubicRoughPairs N z, (1 - liouville ab.1) * (1 - liouville ab.2) :=
      sum_congr rfl fun ab hab => (term ab hab).symm
    _ = _ := sum_congr rfl fun _ _ => by ring

/-- Reflection preserves the cutoff and roughness conditions. -/
theorem swap_mem_cubicRoughPairs (N z : ℕ) (ab : ℕ × ℕ) :
    ab.swap ∈ cubicRoughPairs N z ↔ ab ∈ cubicRoughPairs N z := by
  have hs : ∀ cd : ℕ × ℕ, cd ∈ cubicRoughPairs N z → cd.swap ∈ cubicRoughPairs N z := by
    intro cd hcd
    obtain ⟨hN, ha0, hb0, ha, hb, hza, hzb⟩ := mem_filter.mp hcd
    apply mem_filter.mpr
    refine ⟨?_, hb0, ha0, hb, ha, hzb, hza⟩
    apply mem_antidiagonal.mpr
    change cd.2 + cd.1 = N
    rw [Nat.add_comm]
    exact mem_antidiagonal.mp hN
  exact ⟨fun h => by simpa only [Prod.swap_swap] using hs ab.swap h, hs ab⟩

/-- The two one-point Liouville moments agree by reflection. -/
theorem cubicRoughPairs_sum_liouville_swap (N z : ℕ) :
    (∑ ab ∈ cubicRoughPairs N z, liouville ab.1) =
      ∑ ab ∈ cubicRoughPairs N z, liouville ab.2 := by
  apply sum_bij (fun ab _ => ab.swap)
  · intro ab hab
    exact (swap_mem_cubicRoughPairs N z ab).mpr hab
  · intro a _ b _ hab
    exact Prod.swap_injective hab
  · intro ab hab
    exact ⟨ab.swap, (swap_mem_cubicRoughPairs N z ab).mpr hab, Prod.swap_swap ab⟩
  · intro ab _
    rfl

/-- The exact signed moment combination whose strict positivity is needed. -/
theorem four_mul_cubicPrimePairCount_eq_moments (N z : ℕ) :
    4 * (cubicPrimePairCount N z : ℤ) =
      ((cubicRoughPairs N z).card : ℤ) -
        2 * (∑ ab ∈ cubicRoughPairs N z, liouville ab.1) +
        ∑ ab ∈ cubicRoughPairs N z, liouville ab.1 * liouville ab.2 := by
  rw [four_mul_cubicPrimePairCount, sum_add_distrib, sum_sub_distrib, sum_sub_distrib,
    sum_const, nsmul_eq_mul, mul_one, ← cubicRoughPairs_sum_liouville_swap]
  ring

end GaloisForLFunctions.Goldbach

#print axioms GaloisForLFunctions.Goldbach.minFac_pow_cardFactors_le
#print axioms GaloisForLFunctions.Goldbach.prime_iff_liouville_eq_neg_one_and_lt_minFac_cube
#print axioms GaloisForLFunctions.Goldbach.prime_cube_parity_boundary
#print axioms GaloisForLFunctions.Goldbach.exists_negativeParity_composite_above_cutoff
#print axioms GaloisForLFunctions.Goldbach.cubicRoughPairs
#print axioms GaloisForLFunctions.Goldbach.cubicPrimePairCount
#print axioms GaloisForLFunctions.Goldbach.four_mul_cubicPrimePairCount
#print axioms GaloisForLFunctions.Goldbach.swap_mem_cubicRoughPairs
#print axioms GaloisForLFunctions.Goldbach.cubicRoughPairs_sum_liouville_swap
#print axioms GaloisForLFunctions.Goldbach.four_mul_cubicPrimePairCount_eq_moments
