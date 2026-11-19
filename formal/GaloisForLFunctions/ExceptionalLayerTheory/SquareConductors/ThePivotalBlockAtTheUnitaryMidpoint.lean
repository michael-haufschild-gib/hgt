import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheParityOfTheSmallUnitaryDivisors
import Mathlib.Combinatorics.SetFamily.LYM

/-!
# A pivotal prime-power block at the unitary midpoint

Pairing each subset with the subset obtained by inserting one block cancels
all signs except those just below the square root. At a smallest block,
these survivors form an antichain. Sperner's theorem bounds the weight
by the central binomial coefficient on the remaining blocks.
-/

open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

noncomputable section

/-- Subsets which cross the square-root cut when the block at `p` is inserted. -/
def unitaryPivots (k p : ℕ) : Finset (Finset ℕ) :=
  (k.primeFactors.erase p).powerset.filter fun S =>
    (primePowerSubset k S)^2 ≤ k ∧ k < (p^k.factorization p * primePowerSubset k S)^2

/-- Comparison with the complementary product is the exact squared-divisor test. -/
theorem unitarySubset_small_iff_square {k : ℕ} (hk : 0 < k) {S : Finset ℕ} (hS : S ⊆ k.primeFactors) :
    primePowerSubset k S ≤ primePowerSubset k (k.primeFactors \ S) ↔ (primePowerSubset k S)^2 ≤ k := by
  have hpos : 0 < primePowerSubset k S :=
    prod_pos fun _ hi => pow_pos (Nat.prime_of_mem_primeFactors (hS hi)).pos _
  have hprod : primePowerSubset k S * primePowerSubset k (k.primeFactors \ S) = k := by
    rw [primePowerSubset, primePowerSubset, mul_comm, prod_sdiff hS]
    exact (Nat.prod_primeFactors_pow_factorization hk.ne').symm
  calc
    _ ↔ primePowerSubset k S * primePowerSubset k S ≤
        primePowerSubset k S * primePowerSubset k (k.primeFactors \ S) :=
      ⟨Nat.mul_le_mul_left _, fun h => Nat.le_of_mul_le_mul_left h hpos⟩
    _ ↔ _ := by rw [hprod, pow_two]

private theorem sum_over_pivots {k p : ℕ} (hp : p ∈ k.primeFactors) :
    unitaryHalfWeight k = ∑ S ∈ unitaryPivots k p, (-1 : ℤ)^S.card := by
  let P := k.primeFactors.erase p
  let f (S : Finset ℕ) := if (primePowerSubset k S)^2 ≤ k then (-1 : ℤ)^S.card else 0
  have hk : 0 < k := Nat.pos_of_ne_zero (Nat.mem_primeFactors.mp hp).2.2
  have h : unitaryHalfWeight k = ∑ S ∈ k.primeFactors.powerset, f S := by
    unfold unitaryHalfWeight smallUnitarySubsets
    rw [sum_filter]
    refine sum_congr rfl fun S hS => ?_
    simp only [f, unitarySubset_small_iff_square hk (mem_powerset.mp hS)]
  have hpP : p ∉ P := notMem_erase _ _
  have he : insert p P = k.primeFactors := insert_erase hp
  rw [h, ← he, sum_powerset_insert hpP, ← sum_add_distrib, unitaryPivots, sum_filter]
  apply sum_congr rfl
  intro S hS
  have hpS : p ∉ S := fun hpS => hpP (mem_powerset.mp hS hpS)
  have hblock : 0 < p^k.factorization p := pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  have hle : primePowerSubset k S ≤ p^k.factorization p * primePowerSubset k S :=
    Nat.le_mul_of_pos_left _ hblock
  have hs : primePowerSubset k (insert p S) = p^k.factorization p * primePowerSubset k S :=
    prod_insert hpS
  have hsquare := Nat.pow_le_pow_left hle 2
  simp only [f, hs, card_insert_of_notMem hpS, pow_succ (-1 : ℤ), mul_neg_one]
  split_ifs <;> first | omega | ring

private theorem pivotal_antichain {k p : ℕ} (hp : p ∈ k.primeFactors)
    (hmin : ∀ q ∈ k.primeFactors, p^k.factorization p ≤ q^k.factorization q) :
    IsAntichain (· ⊆ ·) (unitaryPivots k p : Set (Finset ℕ)) := by
  intro S hS T hT hne hsub
  obtain ⟨hSq, hSw⟩ := mem_filter.mp hS
  obtain ⟨hTq, hTw⟩ := mem_filter.mp hT
  have hP : T ⊆ k.primeFactors := (mem_powerset.mp hTq).trans (erase_subset _ _)
  obtain ⟨q, hq, hqS⟩ := Set.not_subset.mp (show ¬(T : Set ℕ) ⊆ S from
    fun h => hne (Subset.antisymm hsub h))
  have hbulk : primePowerSubset k (insert q S) ≤ primePowerSubset k T :=
    Finset.prod_le_prod_of_subset_of_one_le (insert_subset hq hsub) (fun _ _ => Nat.zero_le _)
      (fun i hi _ => Nat.succ_le_of_lt (pow_pos (Nat.prime_of_mem_primeFactors (hP hi)).pos _))
  have hqprod : primePowerSubset k (insert q S) = q^k.factorization q * primePowerSubset k S :=
    prod_insert hqS
  rw [hqprod] at hbulk
  exact hSw.2.not_ge ((Nat.pow_le_pow_left
    ((Nat.mul_le_mul_right _ (hmin q (hP hq))).trans hbulk) 2).trans hTw.1)

/-- Sperner's bound on a ground finset in an infinite ambient type. -/
private theorem ground_sperner (P : Finset ℕ) (F : Finset (Finset ℕ))
    (hground : ∀ S ∈ F, S ⊆ P) (hanti : IsAntichain (· ⊆ ·) (F : Set (Finset ℕ))) :
    F.card ≤ P.card.choose (P.card/2) := by
  let restrict (S : Finset ℕ) := S.subtype (· ∈ P)
  have back (S : Finset ℕ) (hS : S ∈ F) :
      (restrict S).map (Function.Embedding.subtype (· ∈ P)) = S :=
    subtype_map_of_mem (fun _ hi => hground S hS hi)
  have hinj : Set.InjOn restrict (F : Set (Finset ℕ)) := by
    intro S hS T hT h
    rw [← back S hS, h, back T hT]
  have hf : IsAntichain (· ⊆ ·) (F.image restrict : Set (Finset {p // p ∈ P})) := by
    intro U hU V hV hUV hsub
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hU
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hV
    apply hanti hS hT (fun he => hUV (congrArg restrict he))
    rw [← back S hS, ← back T hT]
    exact map_subset_map.mpr hsub
  simpa only [card_image_of_injOn hinj, Fintype.card_coe] using hf.sperner

/-- A minimum block gives an exact signed price supported on an antichain. -/
theorem unitaryHalfWeight_has_pivotal_antichain (k : ℕ) :
    k.primeFactors = ∅ ∨ ∃ p ∈ k.primeFactors,
      IsAntichain (· ⊆ ·) (unitaryPivots k p : Set (Finset ℕ)) ∧
      unitaryHalfWeight k = ∑ S ∈ unitaryPivots k p, (-1 : ℤ)^S.card := by
  rcases k.primeFactors.eq_empty_or_nonempty with he | hn
  · exact Or.inl he
  obtain ⟨p,hp,hm⟩ := k.primeFactors.exists_min_image (fun p => p^k.factorization p) hn
  exact Or.inr ⟨p, hp, pivotal_antichain hp hm, sum_over_pivots hp⟩

/-- The central binomial bound holds for every integer and arbitrary block multiplicities. -/
theorem unitaryHalfWeight_central_bound (k : ℕ) :
    |unitaryHalfWeight k| ≤ ((k.primeFactors.card-1).choose ((k.primeFactors.card-1)/2) : ℤ) := by
  rcases unitaryHalfWeight_has_pivotal_antichain k with he | ⟨p,hp,ha,hw⟩
  · simp [unitaryHalfWeight, smallUnitarySubsets, he, primePowerSubset]
  have hc := ground_sperner (k.primeFactors.erase p) (unitaryPivots k p)
    (fun S hS => mem_powerset.mp (mem_filter.mp hS).1) ha
  rw [card_erase_of_mem hp] at hc
  rw [hw]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simpa using (show ((unitaryPivots k p).card : ℤ) ≤ _ by exact_mod_cast hc)

#print axioms unitaryHalfWeight_has_pivotal_antichain
#print axioms unitaryHalfWeight_central_bound

end

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
