import GaloisForLFunctions.RHTower.BeurlingDeletionSystemCount
import GaloisForLFunctions.RigidArithmeticOfCuts.AnExactCountForcesTheRationalPrimes

/-!
# A positive-generator model with two extra labels

Delete the rational-prime label two, retain all odd primes, and adjoin labels
of norms three and four. Generalized integers have unique coordinates
(u,a,b), with u positive and odd, and norm u*3^a*4^b. These coordinates
prove local finiteness and identify the actual norm count with a triple count.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount

open RHTower RHTower.BeurlingDeletion
open GaloisForLFunctions.RigidArithmeticOfCuts
/-- Retain odd primes, duplicate the norm-three label, and adjoin a norm-four label. -/
abbrev system : BeurlingSystem where
  Label := KeptPrime ({2} : Set ℕ) ⊕ Bool
  labelNorm := Sum.elim (fun p => (p.1 : ℝ)) (fun b => if b then 4 else 3)
  one_lt_labelNorm := by
    rintro (p | b)
    · change (1 : ℝ) < (p.1 : ℝ)
      exact_mod_cast p.2.1.one_lt
    · cases b <;> norm_num

/-- All generator norms of the model are positive integers. -/
theorem hasIntegerNorms : HasIntegerNorms system := by
  rintro (p | b)
  · exact ⟨p.1, rfl⟩
  · cases b
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩

/-- The two norm-three labels give distinct factorizations of the same integer. -/
theorem norm_not_injective : ¬ Function.Injective system.intNorm := by
  classical
  let p : KeptPrime ({2} : Set ℕ) := ⟨3, by norm_num⟩
  intro hinj
  have he : ({Sum.inl p} : system.Integer) = {Sum.inr false} := hinj (by
    rw [system.intNorm_singleton, system.intNorm_singleton]
    rfl)
  have hc := congrArg (Multiset.count (Sum.inr false)) he
  simp at hc

/-- A factorization is encoded by its odd-prime product and its two extra-label counts. -/
def coordinates (g : system.Integer) : ℕ × ℕ × ℕ :=
  (((split g).1.map (fun p : KeptPrime ({2} : Set ℕ) => p.1)).prod,
    (split g).2.count false, (split g).2.count true)

/-- Unique factorization of the retained odd primes makes the coordinate map injective. -/
theorem coordinates_injective : Function.Injective coordinates := by
  intro g g' he
  have hc := he
  simp only [coordinates, Prod.mk.injEq] at hc
  apply (joinEquiv (α := KeptPrime ({2} : Set ℕ)) (γ := Bool)).symm.injective
  apply Prod.ext
  · exact prod_kept_injective ({2} : Set ℕ) hc.1
  · apply Multiset.ext.mpr
    intro b
    cases b
    · exact hc.2.1
    · exact hc.2.2

/-- A Boolean multiset is determined by the multiplicities of its two labels. -/
private theorem bool_decomposition (v : Multiset Bool) :
    v = Multiset.replicate (v.count false) false + Multiset.replicate (v.count true) true := by
  ext b
  cases b <;> simp only [Multiset.count_add, Multiset.count_replicate] <;> simp

/-- The norm in product coordinates is u times 3^a times 4^b. -/
theorem intNorm_join (u : Multiset (KeptPrime ({2} : Set ℕ)))
    (v : Multiset Bool) :
    system.intNorm (join (u, v)) =
      (((u.map fun p : KeptPrime ({2} : Set ℕ) => p.1).prod : ℕ) : ℝ) *
        (3 : ℝ) ^ v.count false * (4 : ℝ) ^ v.count true := by
  have hv := bool_decomposition v
  rw [show join (u, v) = u.map Sum.inl + v.map Sum.inr from rfl,
    system.intNorm_add]
  have hu : system.intNorm (u.map Sum.inl) =
      (((u.map fun p : KeptPrime ({2} : Set ℕ) => p.1).prod : ℕ) : ℝ) := by
    simp only [BeurlingSystem.intNorm, Multiset.map_map, Nat.cast_multiset_prod]
    rfl
  have hb : system.intNorm (v.map Sum.inr) =
      (3 : ℝ) ^ v.count false * (4 : ℝ) ^ v.count true := by
    conv_lhs => rw [hv]
    rw [Multiset.map_add, system.intNorm_add,
      Multiset.map_replicate, Multiset.map_replicate,
      system.intNorm_replicate, system.intNorm_replicate]
    rfl
  rw [hu, hb, mul_assoc]

/-- The actual generalized-integer norm equals its coordinate product. -/
theorem intNorm_coordinates (g : system.Integer) :
    system.intNorm g = (coordinates g).1 *
      (3 : ℝ) ^ (coordinates g).2.1 * (4 : ℝ) ^ (coordinates g).2.2 := by
  have he := intNorm_join (split g).1 (split g).2
  rw [join_split] at he
  exact he


/-- The first coordinate is positive and has no prime factor two. -/
theorem coordinates_sfree (g : system.Integer) :
    SFree ({2} : Set ℕ) (coordinates g).1 :=
  sFree_prod_kept ({2} : Set ℕ) (split g).1

/-- Every positive odd first coordinate and pair of exponents is represented. -/
theorem exists_coordinates {u : ℕ} (hu : SFree ({2} : Set ℕ) u) (a b : ℕ) :
    ∃ g : system.Integer, coordinates g = (u, a, b) := by
  obtain ⟨v, hv⟩ := exists_kept_of_sFree ({2} : Set ℕ) hu
  refine ⟨join (v, Multiset.replicate a false + Multiset.replicate b true), ?_⟩
  simp only [coordinates, split_join, hv, Multiset.count_add, Multiset.count_replicate]
  simp

/-- The coordinate triples with product at most the real threshold. -/
def tripleSet (X : ℝ) : Set (ℕ × ℕ × ℕ) :=
  {v | SFree ({2} : Set ℕ) v.1 ∧ (v.1 : ℝ) * 3 ^ v.2.1 * 4 ^ v.2.2 ≤ X}

/-- The coordinate triples are exactly the image of the actual norm ball. -/
theorem tripleSet_eq_image (X : ℝ) :
    tripleSet X = coordinates '' {g | system.intNorm g ≤ X} := by
  ext ⟨u, a, b⟩
  simp only [tripleSet, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hu, hX⟩
    obtain ⟨g, hg⟩ := exists_coordinates hu a b
    refine ⟨g, ?_, hg⟩
    rw [intNorm_coordinates, hg]
    exact hX
  · rintro ⟨g, hg, he⟩
    have hs := coordinates_sfree g
    rw [he] at hs
    refine ⟨hs, ?_⟩
    rwa [intNorm_coordinates, he] at hg

/-- The actual Beurling count equals the coordinate-triple cardinality. -/
theorem countBall_eq_ncard_triples (X : ℝ) :
    system.countBall X = (tripleSet X).ncard := by
  rw [tripleSet_eq_image, Set.ncard_image_of_injective _ coordinates_injective]
  rfl


/-- Powers of an integer at least two dominate the exponent plus one. -/
private theorem index_lt_pow {m : ℕ} (hm : 2 ≤ m) (k : ℕ) : k + 1 ≤ m ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    exact (show k + 1 + 1 ≤ (k + 1) * 2 by omega).trans (Nat.mul_le_mul ih hm)

/-- Each coordinate of a bounded-norm triple lies in a finite interval. -/
theorem tripleSet_finite (X : ℝ) : (tripleSet X).Finite := by
  have hfin : ((Finset.Icc 0 ⌊X⌋₊ ×ˢ
      (Finset.Icc 0 ⌊X⌋₊ ×ˢ Finset.Icc 0 ⌊X⌋₊) : Finset (ℕ × ℕ × ℕ)) : Set (ℕ × ℕ × ℕ)).Finite :=
    Finset.finite_toSet _
  apply hfin.subset
  rintro ⟨u, a, b⟩ ⟨hu, hX⟩
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast Nat.pos_of_ne_zero hu.1
  have ha1 : (1 : ℝ) ≤ (3 : ℝ) ^ a := one_le_pow₀ (by norm_num)
  have hb1 : (1 : ℝ) ≤ (4 : ℝ) ^ b := one_le_pow₀ (by norm_num)
  have ha : (a : ℝ) ≤ (3 : ℝ) ^ a := by
    exact_mod_cast (show a ≤ 3 ^ a from (Nat.le_succ a).trans (index_lt_pow (by norm_num) a))
  have hb : (b : ℝ) ≤ (4 : ℝ) ^ b := by
    exact_mod_cast (show b ≤ 4 ^ b from (Nat.le_succ b).trans (index_lt_pow (by norm_num) b))
  have hua : (u : ℝ) ≤ (u : ℝ) * (3 : ℝ) ^ a := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ha1 (Nat.cast_nonneg u)
  have hua1 : (1 : ℝ) ≤ (u : ℝ) * (3 : ℝ) ^ a := hu1.trans hua
  have hlast : (u : ℝ) * (3 : ℝ) ^ a ≤ (u : ℝ) * 3 ^ a * 4 ^ b := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb1 (by positivity : 0 ≤ (u : ℝ) * 3 ^ a)
  have hA : (3 : ℝ) ^ a ≤ (u : ℝ) * 3 ^ a := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hu1 (by positivity : 0 ≤ (3 : ℝ) ^ a)
  have hB : (4 : ℝ) ^ b ≤ (u : ℝ) * 3 ^ a * 4 ^ b := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hua1 (by positivity : 0 ≤ (4 : ℝ) ^ b)
  have huX : (u : ℝ) ≤ X := hua.trans (hlast.trans hX)
  have haX : (a : ℝ) ≤ X := ha.trans (hA.trans (hlast.trans hX))
  have hbX : (b : ℝ) ≤ X := hb.trans (hB.trans hX)
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor huX⟩,
    Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor haX⟩,
      Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor hbX⟩⟩⟩

/-- The positive-generator model has finite norm balls. -/
theorem isDiscrete : system.IsDiscrete := by
  intro X
  have hf := (tripleSet_finite X).preimage coordinates_injective.injOn
  apply hf.subset
  intro g hg
  change system.intNorm g ≤ X at hg
  exact ⟨coordinates_sfree g, by rwa [intNorm_coordinates] at hg⟩



/-- Avoiding the prime two is equivalent to odd residue. -/
theorem sfree_two_iff (n : ℕ) : SFree ({2} : Set ℕ) n ↔ n % 2 = 1 := by
  constructor
  · rintro ⟨hn, hp⟩
    by_contra hm
    have hdiv : 2 ∣ n := Nat.dvd_of_mod_eq_zero (by omega)
    have hf := hp 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hdiv, hn⟩)
    exact hf (Set.mem_singleton 2)
  · intro hn
    refine ⟨by omega, ?_⟩
    intro p hp hmem
    have hp2 : p = 2 := Set.mem_singleton_iff.mp hmem
    rw [hp2] at hp
    have hmod := Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mem_primeFactors hp)
    omega

/-- The finite set of positive odd integers up to a real threshold. -/
def oddIntegers (X : ℝ) : Finset ℕ :=
  (Finset.range ⌊(X + 1) / 2⌋₊).image fun j => 2 * j + 1

/-- The positive odd-integer count is the floor of (X+1)/2. -/
theorem card_oddIntegers (X : ℝ) : (oddIntegers X).card = ⌊(X + 1) / 2⌋₊ := by
  rw [oddIntegers, Finset.card_image_of_injective _ (by
    intro a b hab
    change 2 * a + 1 = 2 * b + 1 at hab
    omega), Finset.card_range]

/-- The explicit odd-integer enumeration has exactly the required cutoff. -/
theorem mem_oddIntegers {X : ℝ} (hX : 0 ≤ X) (n : ℕ) :
    n ∈ oddIntegers X ↔ SFree ({2} : Set ℕ) n ∧ (n : ℝ) ≤ X := by
  rw [sfree_two_iff]
  simp only [oddIntegers, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨by omega, ?_⟩
    have hj' : ((j + 1 : ℕ) : ℝ) ≤ (⌊(X + 1) / 2⌋₊ : ℝ) := by exact_mod_cast hj
    have hf := Nat.floor_le (show 0 ≤ (X + 1) / 2 by linarith only [hX])
    push_cast at hj' ⊢
    linarith only [hj', hf]
  · rintro ⟨hn, hnX⟩
    have he : 2 * (n / 2) + 1 = n := by omega
    refine ⟨n / 2, ?_, he⟩
    have hfloor : n / 2 + 1 ≤ ⌊(X + 1) / 2⌋₊ := by
      apply Nat.le_floor
      have heR : (2 : ℝ) * (n / 2 : ℕ) + 1 = n := by exact_mod_cast he
      push_cast
      linarith only [hnX, heR]
    omega

/-- The odd-integer count differs from half its endpoint by at most one half. -/
theorem odd_count_error {X : ℝ} (hX : 0 ≤ X) :
    |((oddIntegers X).card : ℝ) - X / 2| ≤ 1 / 2 := by
  rw [card_oddIntegers]
  have hlow := Nat.lt_floor_add_one ((X + 1) / 2)
  have hhigh := Nat.floor_le (show 0 ≤ (X + 1) / 2 by linarith only [hX])
  apply abs_le.mpr
  constructor <;> linarith only [hlow, hhigh]

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount
