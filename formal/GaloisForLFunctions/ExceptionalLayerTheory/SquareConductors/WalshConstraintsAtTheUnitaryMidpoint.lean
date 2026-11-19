import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheVirialSymbolOnPrimePowerBlocks

/-!
# Boundary constraints on the Walsh spectrum of small unitary divisors

A balanced integer stays below the square root at the empty set and after
every single birth. Inversion at precisely these vertices forces an exact
signed sum of higher interactions. In particular the midpoint spectrum cannot
lie in the null space of the critical virial multiplier.
-/

open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
noncomputable section

/-- Orthogonality in the coordinate indexing the Walsh characters. -/
theorem blockCharacter_column_orthogonality {P A B : Finset ℕ} (ha : A ⊆ P) (hb : B ⊆ P) :
    ∑ T ∈ P.powerset, blockCharacter T A * blockCharacter T B =
      if A = B then (2:ℤ)^P.card else 0 := by
  simp_rw [blockCharacter, ← prod_mul_distrib]
  rw [← prod_one_add]
  by_cases h : A = B
  · subst B
    rw [if_pos rfl, ← prod_const]
    exact prod_congr rfl fun p _ => by split_ifs <;> norm_num
  · rw [if_neg h]
    obtain ⟨p,hp⟩ : ∃ p, ¬(p ∈ A ↔ p ∈ B) := by
      by_contra! hall
      exact h (Finset.ext hall)
    by_cases hA : p ∈ A
    · exact prod_eq_zero (ha hA) (by simp [hA, show p ∉ B by tauto])
    · have hB : p ∈ B := by tauto
      exact prod_eq_zero (hb hB) (by simp [hA,hB])

/-- Inversion recovers the signed square-root cut at every vertex of the
actual prime-power cube, including possible ties. -/
theorem unitaryWalshContrast_inversion (k : ℕ) {A : Finset ℕ} (hA : A ⊆ k.primeFactors) :
    ∑ T ∈ k.primeFactors.powerset, unitaryWalshContrast k T * blockCharacter T A =
      (2:ℤ)^k.primeFactors.card * ((if A ∈ smallUnitarySubsets k then 1 else 0) -
        (if k.primeFactors \ A ∈ smallUnitarySubsets k then 1 else 0)) := by
  simp only [unitaryWalshContrast, sum_mul, sub_mul]
  rw [sum_comm]
  have inner (S : Finset ℕ) (hS : S ∈ smallUnitarySubsets k) :
      ∑ T ∈ k.primeFactors.powerset,
        (blockCharacter T S * blockCharacter T A -
          blockCharacter T (k.primeFactors \ S) * blockCharacter T A) =
        (if S=A then (2:ℤ)^k.primeFactors.card else 0) -
        (if S=k.primeFactors \ A then (2:ℤ)^k.primeFactors.card else 0) := by
    have hs := mem_powerset.mp (mem_filter.mp hS).1
    have iffC : k.primeFactors \ S = A ↔ S = k.primeFactors \ A := by
      constructor
      · rintro rfl; rw [Finset.sdiff_sdiff_eq_self hs]
      · rintro rfl; rw [Finset.sdiff_sdiff_eq_self hA]
    rw [sum_sub_distrib, blockCharacter_column_orthogonality hs hA, blockCharacter_column_orthogonality sdiff_subset hA]
    simp only [iffC]
  rw [sum_congr rfl inner, sum_sub_distrib, sum_ite_eq', sum_ite_eq']
  split_ifs <;> ring

private theorem empty_reading {k : ℕ} (hk : 1 < k) :
    ∅ ∈ smallUnitarySubsets k ∧ k.primeFactors ∉ smallUnitarySubsets k := by
  refine ⟨mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _), ?_⟩, ?_⟩
  · rw [unitarySubset_small_iff_square (by omega) (empty_subset _)]
    simpa only [primePowerSubset, prod_empty, one_pow] using hk.le
  · intro h
    exact lt_irrefl _ (small_unitary_subset_card hk h).1

/-- Total signed Walsh mass is independent of the prime sizes. -/
theorem unitaryWalshContrast_sum {k : ℕ} (hk : 1 < k) :
    ∑ T ∈ k.primeFactors.powerset, unitaryWalshContrast k T = (2:ℤ)^k.primeFactors.card := by
  have he := unitaryWalshContrast_inversion k (empty_subset _)
  obtain ⟨h₀,h₁⟩ := empty_reading hk
  simpa [blockCharacter,h₀,h₁] using he

private theorem singleton_reading {k p : ℕ} (hp : p ∈ k.primeFactors)
    (hbal : (p^k.factorization p)^2 < k) :
    {p} ∈ smallUnitarySubsets k ∧ k.primeFactors \ {p} ∉ smallUnitarySubsets k := by
  have hs := singleton_subset_iff.mpr hp
  have hk := Nat.pos_of_ne_zero (Nat.mem_primeFactors.mp hp).2.2
  have he : primePowerSubset k {p} = p^k.factorization p := prod_singleton _ _
  have prod : primePowerSubset k {p} * primePowerSubset k (k.primeFactors \ {p}) = k := by
    rw [primePowerSubset, primePowerSubset, mul_comm, prod_sdiff hs]
    exact (Nat.prod_primeFactors_pow_factorization hk.ne').symm
  refine ⟨mem_filter.mpr ⟨mem_powerset.mpr hs, (unitarySubset_small_iff_square hk hs).mpr ?_⟩, ?_⟩
  · simpa only [he] using hbal.le
  · intro h
    have hle := (mem_filter.mp h).2
    rw [Finset.sdiff_sdiff_eq_self hs] at hle
    have h := Nat.mul_le_mul_left (primePowerSubset k {p}) hle
    rw [prod, he, ← pow_two] at h
    exact hbal.not_ge h

/-- A prime block below the square root has zero net Walsh mass among
all the interactions involving that particular prime. -/
theorem unitaryWalshContrast_through_prime {k p : ℕ} (hp : p ∈ k.primeFactors)
    (hbal : (p^k.factorization p)^2 < k) :
    ∑ T ∈ k.primeFactors.powerset.filter (fun T => p ∈ T), unitaryWalshContrast k T = 0 := by
  have hk : 1 < k := Nat.nonempty_primeFactors.mp ⟨p,hp⟩
  obtain ⟨h₀,h₁⟩ := singleton_reading hp hbal
  have he := unitaryWalshContrast_inversion k (singleton_subset_iff.mpr hp)
  have ch (T : Finset ℕ) : blockCharacter T {p} = if p ∈ T then -1 else 1 := by
    simp [blockCharacter, prod_ite_eq']
  simp only [ch, h₀, h₁, if_true, if_false, sub_zero, mul_one] at he
  let f := unitaryWalshContrast k
  have point (T : Finset ℕ) : f T * (if p ∈ T then -1 else 1) =
      f T - 2*(if p ∈ T then f T else 0) := by split_ifs <;> ring
  change (∑ T ∈ k.primeFactors.powerset, f T * (if p ∈ T then -1 else 1)) = _ at he
  simp_rw [point] at he
  rw [sum_sub_distrib, ← mul_sum, ← sum_filter, unitaryWalshContrast_sum hk] at he
  dsimp only [f] at he
  linarith only [he]

/-- At a balanced integer the constant Walsh mass must be supplied, with
opposite sign, by the excess of the interaction rank over one. -/
theorem unitaryWalshContrast_rank_excess {k : ℕ} (hk : 1 < k)
    (hbal : ∀ p ∈ k.primeFactors, (p^k.factorization p)^2 < k) :
    ∑ T ∈ k.primeFactors.powerset, ((T.card:ℤ)-1)*unitaryWalshContrast k T =
      -(2:ℤ)^k.primeFactors.card := by
  have hzero : ∑ p ∈ k.primeFactors, ∑ T ∈ k.primeFactors.powerset,
      (if p ∈ T then unitaryWalshContrast k T else 0) = 0 := by
    apply sum_eq_zero
    intro p hp
    rw [← sum_filter]
    exact unitaryWalshContrast_through_prime hp (hbal p hp)
  rw [sum_comm] at hzero
  have hf (T : Finset ℕ) (hT : T ∈ k.primeFactors.powerset) :
      ∑ p ∈ k.primeFactors, (if p ∈ T then unitaryWalshContrast k T else 0) =
        (T.card:ℤ)*unitaryWalshContrast k T := by
    rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr (mem_powerset.mp hT), sum_const,
      nsmul_eq_mul]
  rw [sum_congr rfl hf] at hzero
  simp only [sub_mul, one_mul, sum_sub_distrib, hzero, unitaryWalshContrast_sum hk, zero_sub]

#print axioms unitaryWalshContrast_inversion
#print axioms unitaryWalshContrast_sum
#print axioms unitaryWalshContrast_through_prime
#print axioms unitaryWalshContrast_rank_excess

/-- Nonlinear odd Walsh interactions available to the midpoint cut. -/
def nonlinearUnitaryRanks (k : ℕ) : Finset (Finset ℕ) :=
  k.primeFactors.powerset.filter (fun T => Odd T.card ∧ 3 ≤ T.card)

/-- Every balanced integer has positive critical virial energy. More precisely,
its energy times the number of available nonlinear modes pays at least
seven tenths of the square of the entire cube size. -/
theorem balanced_unitary_virial_floor {k : ℕ} (hk : 1 < k)
    (hbal : ∀ p ∈ k.primeFactors, (p^k.factorization p)^2 < k) :
    7/10*((2:ℝ)^k.primeFactors.card)^2 ≤
      ((nonlinearUnitaryRanks k).card : ℝ) * unitaryVirialEnergy (1/10) k := by
  let F := nonlinearUnitaryRanks k
  let C (T : Finset ℕ) : ℝ := unitaryWalshContrast k T
  let a (T : Finset ℕ) := ((T.card:ℝ)-1)*C T
  let e (T : Finset ℕ) := blockVirialSymbol (1/10) (2*T.card)*(C T)^2
  have off {T : Finset ℕ} (hT : T ∈ k.primeFactors.powerset) (hf : T ∉ F) :
      a T = 0 ∧ e T = 0 := by
    rcases Nat.even_or_odd T.card with he | ho
    · simp [a,e,C,unitaryWalshContrast_even (mem_powerset.mp hT) he]
    · have hlt : ¬3 ≤ T.card := fun h => hf (mem_filter.mpr ⟨hT,ho,h⟩)
      obtain ⟨j,hj⟩ := ho
      have h1 : T.card = 1 := by omega
      norm_num [a,e,h1,blockVirialSymbol]
  have ha : ∑ T ∈ F, a T = -(2:ℝ)^k.primeFactors.card := by
    rw [sum_subset (show F ⊆ k.primeFactors.powerset from filter_subset ..)
      (fun T hT hf => (off hT hf).1)]
    dsimp only [a,C]
    exact_mod_cast unitaryWalshContrast_rank_excess hk hbal
  have he : ∑ T ∈ F, e T = unitaryVirialEnergy (1/10) k :=
    sum_subset (filter_subset ..) (fun T hT hf => (off hT hf).2)
  have hp : (7/10:ℝ) * ∑ T ∈ F, (a T)^2 ≤ ∑ T ∈ F, e T := by
    rw [mul_sum]
    refine sum_le_sum fun T hT => ?_
    have h := mul_le_mul_of_nonneg_right (blockVirial_rank_excess (mem_filter.mp hT).2.2)
      (sq_nonneg (C T))
    simpa only [a,e,mul_pow,mul_assoc] using h
  have cs := sum_mul_sq_le_sq_mul_sq F (fun _ => (1:ℝ)) a
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, ha, neg_sq] at cs
  rw [← he]
  calc _ ≤ 7/10 * (F.card * ∑ T ∈ F, (a T)^2) := mul_le_mul_of_nonneg_left cs (by norm_num)
       _ = (F.card:ℝ) * (7/10 * ∑ T ∈ F, (a T)^2) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)

#print axioms balanced_unitary_virial_floor

/-- The subset character depends symmetrically on its two arguments. -/
theorem blockCharacter_comm (T S : Finset ℕ) : blockCharacter T S = blockCharacter S T := by
  simp only [blockCharacter, prod_ite, filter_mem_eq_inter, prod_const, one_pow, mul_one, inter_comm T S]

/-- Applying the unnormalized Walsh transform twice multiplies by the cube size. -/
theorem blockCharacter_double_transform {P T : Finset ℕ} (ht : T ⊆ P) (c : Finset ℕ → ℤ) :
    ∑ A ∈ P.powerset, ((∑ U ∈ P.powerset, c U*blockCharacter U A)*blockCharacter T A) =
      c T*(2:ℤ)^P.card := by
  simp_rw [sum_mul, mul_assoc]
  rw [sum_comm]
  have one (U : Finset ℕ) (hU : U ∈ P.powerset) :
      ∑ A ∈ P.powerset, c U*(blockCharacter U A * blockCharacter T A) =
        if U=T then c U*2^P.card else 0 := by
    rw [← mul_sum]
    simp_rw [blockCharacter_comm U, blockCharacter_comm T]
    rw [blockCharacter_column_orthogonality (mem_powerset.mp hU) ht, mul_ite, mul_zero]
  rw [sum_congr rfl one, sum_ite_eq', if_pos (mem_powerset.mpr ht)]

/-- A dominant prime-power block puts the entire contrast in that one
Walsh coordinate, at amplitude equal to the size of the cube. -/
theorem dominant_unitary_single_mode {k p : ℕ} (hk : 1 < k) (hp : p ∈ k.primeFactors)
    (hbig : k < (p^k.factorization p)^2) {T : Finset ℕ} (ht : T ⊆ k.primeFactors) :
    unitaryWalshContrast k T = if T={p} then (2:ℤ)^k.primeFactors.card else 0 := by
  let P := k.primeFactors
  have below {A : Finset ℕ} (ha : A ⊆ P) :
      A ∈ smallUnitarySubsets k ↔ p ∉ A := by
    rw [small_unitary_subsets_of_dominant hk hp hbig, mem_powerset]
    exact ⟨fun h hpA => (mem_erase.mp (h hpA)).1 rfl,
      fun h q hq => mem_erase.mpr ⟨fun he => h (he ▸ hq),ha hq⟩⟩
  have vertex (A : Finset ℕ) (ha : A ∈ P.powerset) :
      ∑ U ∈ P.powerset, unitaryWalshContrast k U*blockCharacter U A =
        (2:ℤ)^P.card * blockCharacter {p} A := by
    rw [unitaryWalshContrast_inversion k (mem_powerset.mp ha)]
    by_cases h : p ∈ A <;>
      simp [below (mem_powerset.mp ha), below (A:=P \ A) sdiff_subset, blockCharacter, P, hp, h]
  have hrec := blockCharacter_double_transform ht (unitaryWalshContrast k)
  change (∑ A ∈ P.powerset, _) = _ at hrec
  rw [sum_congr rfl (fun A ha => congrArg (· * blockCharacter T A) (vertex A ha))] at hrec
  simp_rw [mul_assoc, blockCharacter_comm {p}, blockCharacter_comm T] at hrec
  rw [← mul_sum, blockCharacter_column_orthogonality (singleton_subset_iff.mpr hp) ht] at hrec
  apply mul_right_cancel₀ (pow_ne_zero P.card (by norm_num : (2:ℤ) ≠ 0))
  simpa only [mul_comm ((2:ℤ)^P.card), eq_comm (a:={p}) (b:=T)] using hrec.symm

/-- Critical energy is zero exactly for the degenerate cubes and the integers
with a block larger than the product of all other blocks. -/
theorem unitaryVirialEnergy_zero_iff (k : ℕ) :
    unitaryVirialEnergy (1/10) k = 0 ↔
      k ≤ 1 ∨ ∃ p ∈ k.primeFactors, k < (p^k.factorization p)^2 := by
  by_cases hk : k ≤ 1
  · obtain rfl | rfl : k=0 ∨ k=1 := by omega
    all_goals simp [unitaryVirialEnergy, unitaryWalshContrast, blockCharacter]
  have hk1 : 1 < k := by omega
  constructor
  · intro hz
    right
    by_contra! hn
    have hbal (p : ℕ) (hp : p ∈ k.primeFactors) : (p^k.factorization p)^2 < k := by
      apply (hn p hp).lt_of_ne
      intro he
      have ha := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd
        (Nat.mem_primeFactors.mp hp).2.2 (Nat.mem_primeFactors.mp hp).2.1
      have he' := congrArg (fun n : ℕ => n.factorization p) he
      rw [← pow_mul, Nat.factorization_pow_self (Nat.prime_of_mem_primeFactors hp)] at he'
      omega
    have h := balanced_unitary_virial_floor hk1 hbal
    rw [hz, mul_zero] at h
    exact (by positivity : (0:ℝ) < 7/10*((2:ℝ)^k.primeFactors.card)^2).not_ge h
  · rintro (hh | ⟨p,hp,hbig⟩)
    · exact (hk hh).elim
    apply sum_eq_zero
    intro T hT
    rw [dominant_unitary_single_mode hk1 hp hbig (mem_powerset.mp hT)]
    split_ifs with he
    · subst T
      norm_num [blockVirialSymbol]
    · simp

#print axioms dominant_unitary_single_mode
#print axioms unitaryVirialEnergy_zero_iff
end
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
