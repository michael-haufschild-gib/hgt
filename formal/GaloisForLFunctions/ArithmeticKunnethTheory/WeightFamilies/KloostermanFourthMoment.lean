import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanMomentCounts
import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.HyperplaneTateTrace
import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanLocalStatistics

/-!
# The exact fourth Kloosterman moment

The normalized reciprocal locus for four coordinates is the union of three
lines. Each pair meets once; their intersection points merge in characteristic
two. The resulting point count gives the exact fourth moment and a uniform
bound of two after square-root normalization and parameter averaging.
-/

open Finset

namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The normalized fourth-moment locus is the union of three coordinate lines. -/
theorem mem_normalizedDoubleZeroTorus_three (x : MomentTorus F 3) :
    x ∈ normalizedDoubleZeroTorus 3 ↔
      (1 + ∑ i, (x i : F) = 0) ∧
        ((x 0 : F) = -1 ∨ (x 1 : F) = -1 ∨ (x 2 : F) = -1) := by
  have h0 := (x 0).property
  have h1 := (x 1).property
  have h2 := (x 2).property
  have hclear : (1 + (x 0 : F)⁻¹ + (x 1 : F)⁻¹ + (x 2 : F)⁻¹ = 0) ↔
      ((x 0 : F) * x 1 * x 2 + (x 0 : F) * x 1 +
        (x 0 : F) * x 2 + (x 1 : F) * x 2 = 0) := by
    constructor
    · intro h
      field_simp [h0, h1, h2] at h
      linear_combination h
    · intro h
      field_simp [h0, h1, h2]
      linear_combination h
  simp only [normalizedDoubleZeroTorus, normalizedCoordinateZeroTorus,
    mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hs, hr⟩
    refine ⟨hs, ?_⟩
    have hs' : 1 + (x 0 : F) + (x 1 : F) + (x 2 : F) = 0 := by
      simpa [Fin.sum_univ_succ, add_assoc] using hs
    have hr' : 1 + (x 0 : F)⁻¹ + (x 1 : F)⁻¹ + (x 2 : F)⁻¹ = 0 := by
      simpa [Fin.sum_univ_succ, add_assoc] using hr
    have hp : ((x 0 : F) + 1) * ((x 1 : F) + 1) * ((x 2 : F) + 1) = 0 := by
      linear_combination hclear.mp hr' + hs'
    simpa only [mul_eq_zero, add_eq_zero_iff_eq_neg, or_assoc] using hp
  · rintro ⟨hs, hz⟩
    refine ⟨hs, ?_⟩
    have hs' : 1 + (x 0 : F) + (x 1 : F) + (x 2 : F) = 0 := by
      simpa [Fin.sum_univ_succ, add_assoc] using hs
    have hp : ((x 0 : F) + 1) * ((x 1 : F) + 1) * ((x 2 : F) + 1) = 0 := by
      simpa only [mul_eq_zero, add_eq_zero_iff_eq_neg, or_assoc] using hz
    have hr' : 1 + (x 0 : F)⁻¹ + (x 1 : F)⁻¹ + (x 2 : F)⁻¹ = 0 := by
      apply hclear.mpr
      linear_combination hp - hs'
    simpa [Fin.sum_univ_succ, add_assoc] using hr'

private def fourthOne : {a : F // a ≠ 0} := ⟨1, one_ne_zero⟩
private def fourthNegOne : {a : F // a ≠ 0} := ⟨-1, neg_ne_zero.mpr one_ne_zero⟩
private def fourthNeg (u : {a : F // a ≠ 0}) : {a : F // a ≠ 0} :=
  ⟨-u.val, neg_ne_zero.mpr u.property⟩

private def fourthLine0 (u : {a : F // a ≠ 0}) : MomentTorus F 3 :=
  ![fourthNegOne, u, fourthNeg u]
private def fourthLine1 (u : {a : F // a ≠ 0}) : MomentTorus F 3 :=
  ![u, fourthNegOne, fourthNeg u]
private def fourthLine2 (u : {a : F // a ≠ 0}) : MomentTorus F 3 :=
  ![u, fourthNeg u, fourthNegOne]

private def fourthLines (i : Fin 3) : Finset (MomentTorus F 3) :=
  if i = 0 then univ.image fourthLine0
  else if i = 1 then univ.image fourthLine1
  else univ.image fourthLine2

private theorem normalizedDoubleZeroTorus_three_eq_lines :
    normalizedDoubleZeroTorus (F := F) 3 =
      (fourthLines 0 ∪ fourthLines 1) ∪ fourthLines 2 := by
  ext x
  simp only [fourthLines, Fin.isValue, ↓reduceIte, mem_union]
  constructor
  · intro hx
    obtain ⟨hs, hz⟩ := (mem_normalizedDoubleZeroTorus_three x).mp hx
    have hs' : 1 + (x 0 : F) + (x 1 : F) + (x 2 : F) = 0 := by
      simpa [Fin.sum_univ_succ, add_assoc] using hs
    rcases hz with h0 | h1 | h2
    · left; left
      refine mem_image.mpr ⟨x 1, mem_univ _, ?_⟩
      funext i
      apply Subtype.ext
      fin_cases i
      · exact h0.symm
      · rfl
      · change -(x 1 : F) = (x 2 : F)
        linear_combination h0 - hs'
    · left; right
      refine mem_image.mpr ⟨x 0, mem_univ _, ?_⟩
      funext i
      apply Subtype.ext
      fin_cases i
      · rfl
      · exact h1.symm
      · change -(x 0 : F) = (x 2 : F)
        linear_combination h1 - hs'
    · right
      refine mem_image.mpr ⟨x 0, mem_univ _, ?_⟩
      funext i
      apply Subtype.ext
      fin_cases i
      · rfl
      · change -(x 0 : F) = (x 1 : F)
        linear_combination h2 - hs'
      · exact h2.symm
  · rintro ((hx | hx) | hx)
    all_goals obtain ⟨u, _, rfl⟩ := mem_image.mp hx
    all_goals simp [normalizedDoubleZeroTorus, normalizedCoordinateZeroTorus,
      fourthLine0, fourthLine1, fourthLine2, fourthNegOne, fourthNeg,
      Fin.sum_univ_succ, inv_neg, add_assoc]

private theorem fourthLines_card (i : Fin 3) :
    (fourthLines (F := F) i).card = Fintype.card F - 1 := by
  have hc : Fintype.card {a : F // a ≠ 0} = Fintype.card F - 1 := by
    rw [Fintype.card_subtype]
    exact SignedSuccessorArithmetic.card_units_filter
  have hi0 : Function.Injective (fourthLine0 (F := F)) :=
    fun u v h => congrFun h 1
  have hi1 : Function.Injective (fourthLine1 (F := F)) :=
    fun u v h => congrFun h 0
  have hi2 : Function.Injective (fourthLine2 (F := F)) :=
    fun u v h => congrFun h 0
  fin_cases i
  · change (univ.image (fourthLine0 (F := F))).card = _
    rw [card_image_of_injective _ hi0, card_univ, hc]
  · change (univ.image (fourthLine1 (F := F))).card = _
    rw [card_image_of_injective _ hi1, card_univ, hc]
  · change (univ.image (fourthLine2 (F := F))).card = _
    rw [card_image_of_injective _ hi2, card_univ, hc]

private theorem fourthLines_inter_zero_one :
    fourthLines (F := F) 0 ∩ fourthLines 1 = {fourthLine0 fourthNegOne} := by
  ext x
  simp only [fourthLines, Fin.isValue, ↓reduceIte, mem_inter, mem_singleton]
  constructor
  · rintro ⟨ha, hb⟩
    obtain ⟨u, _, hu⟩ := mem_image.mp ha
    obtain ⟨v, _, hv⟩ := mem_image.mp hb
    have he := congrFun (hu.trans hv.symm) 1
    have hu0 : u = fourthNegOne := he
    subst u
    exact hu.symm
  · intro hx
    subst x
    exact ⟨mem_image.mpr ⟨fourthNegOne, mem_univ _, rfl⟩,
      mem_image.mpr ⟨fourthNegOne, mem_univ _, rfl⟩⟩

private theorem fourthLines_inter_zero_two :
    fourthLines (F := F) 0 ∩ fourthLines 2 = {fourthLine0 fourthOne} := by
  ext x
  simp only [fourthLines, Fin.isValue, ↓reduceIte, mem_inter, mem_singleton]
  constructor
  · rintro ⟨ha, hb⟩
    obtain ⟨u, _, hu⟩ := mem_image.mp ha
    obtain ⟨v, _, hv⟩ := mem_image.mp hb
    have he : -(u : F) = -1 := congrArg Subtype.val (congrFun (hu.trans hv.symm) 2)
    have hu0 : u = fourthOne := by
      apply Subtype.ext
      change (u : F) = 1
      linear_combination -he
    subst u
    exact hu.symm
  · intro hx
    subst x
    refine ⟨mem_image.mpr ⟨fourthOne, mem_univ _, rfl⟩,
      mem_image.mpr ⟨fourthNegOne, mem_univ _, ?_⟩⟩
    funext i
    apply Subtype.ext
    fin_cases i <;> simp [fourthLine0, fourthLine2, fourthNegOne, fourthOne, fourthNeg]

private theorem fourthLines_inter_one_two :
    fourthLines (F := F) 1 ∩ fourthLines 2 = {fourthLine1 fourthOne} := by
  ext x
  simp only [fourthLines, Fin.isValue, ↓reduceIte, mem_inter, mem_singleton]
  constructor
  · rintro ⟨ha, hb⟩
    obtain ⟨u, _, hu⟩ := mem_image.mp ha
    obtain ⟨v, _, hv⟩ := mem_image.mp hb
    have he : -(u : F) = -1 := congrArg Subtype.val (congrFun (hu.trans hv.symm) 2)
    have hu0 : u = fourthOne := by
      apply Subtype.ext
      change (u : F) = 1
      linear_combination -he
    subst u
    exact hu.symm
  · intro hx
    subst x
    exact ⟨mem_image.mpr ⟨fourthOne, mem_univ _, rfl⟩,
      mem_image.mpr ⟨fourthOne, mem_univ _, rfl⟩⟩

/-- The three lines have three pair intersections; they merge only in characteristic two. -/
theorem normalizedDoubleZeroTorus_three_card :
    (normalizedDoubleZeroTorus (F := F) 3).card + 6 =
      3 * Fintype.card F + if (1 : F) = -1 then 1 else 0 := by
  have hAB := card_union_add_card_inter (fourthLines (F := F) 0) (fourthLines 1)
  have hABC := card_union_add_card_inter
    (fourthLines (F := F) 0 ∪ fourthLines 1) (fourthLines 2)
  have hinter : (fourthLines (F := F) 0 ∪ fourthLines 1) ∩ fourthLines 2 =
      {fourthLine0 fourthOne, fourthLine1 fourthOne} := by
    calc
      _ = (fourthLines 0 ∩ fourthLines 2) ∪ (fourthLines 1 ∩ fourthLines 2) := by
        ext x
        simp only [mem_inter, mem_union]
        tauto
      _ = _ := by rw [fourthLines_inter_zero_two, fourthLines_inter_one_two]; rfl
  have he : fourthLine0 (F := F) fourthOne = fourthLine1 fourthOne ↔ (1 : F) = -1 := by
    constructor
    · intro h
      exact congrArg Subtype.val (congrFun h 1)
    · intro h
      funext i
      apply Subtype.ext
      fin_cases i
      · exact h.symm
      · exact h
      · rfl
  rw [fourthLines_inter_zero_one, card_singleton, fourthLines_card, fourthLines_card] at hAB
  rw [hinter, fourthLines_card] at hABC
  rw [normalizedDoubleZeroTorus_three_eq_lines]
  have hq := Fintype.one_lt_card (α := F)
  by_cases hc : (1 : F) = -1
  · have hpts := he.mpr hc
    simp [hpts] at hABC
    rw [if_pos hc]
    omega
  · rw [card_pair (fun h => hc (he.mp h))] at hABC
    rw [if_neg hc]
    omega

#print axioms mem_normalizedDoubleZeroTorus_three
#print axioms normalizedDoubleZeroTorus_three_card

private instance primeFieldFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

/-- The exact fourth moment has one additional square-field-size term in characteristic two. -/
theorem sum_primeKloostermanTrace_four (p : Nat.Primes) :
    ∑ a : ZMod p.val, primeKloostermanTrace p a ^ 4 =
      2 * (p.val : ℝ) ^ 3 - 3 * (p.val : ℝ) ^ 2 - 3 * p.val +
        if (1 : ZMod p.val) = -1 then (p.val : ℝ) ^ 2 else 0 := by
  have hreal (a : ZMod p.val) :
      SignedSuccessorArithmetic.kloosterman ZMod.stdAddChar a 1 =
        (primeKloostermanTrace p a : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using primeKloostermanTrace_im p a
  have hm := kloosterman_moment_double_count (ZMod.isPrimitive_stdAddChar p.val)
    (b := (1 : ZMod p.val)) one_ne_zero 3
  simp only [hreal, ZMod.card] at hm
  have hmR : (∑ a : ZMod p.val, primeKloostermanTrace p a ^ 4) =
      (p.val : ℝ) ^ 2 * (normalizedDoubleZeroTorus (F := ZMod p.val) 3).card -
        ((p.val : ℝ) - 1) ^ 3 - 1 := by
    apply Complex.ofReal_injective
    push_cast
    convert hm using 1 <;> ring
  rw [hmR]
  have hc := normalizedDoubleZeroTorus_three_card (F := ZMod p.val)
  simp only [ZMod.card] at hc
  by_cases htwo : (1 : ZMod p.val) = -1
  · rw [if_pos htwo] at hc ⊢
    have hcR : ((normalizedDoubleZeroTorus (F := ZMod p.val) 3).card : ℝ) + 6 =
        3 * (p.val : ℝ) + 1 := by exact_mod_cast hc
    linear_combination (p.val : ℝ) ^ 2 * hcR
  · rw [if_neg htwo] at hc ⊢
    have hcR : ((normalizedDoubleZeroTorus (F := ZMod p.val) 3).card : ℝ) + 6 =
        3 * (p.val : ℝ) + 0 := by exact_mod_cast hc
    linear_combination (p.val : ℝ) ^ 2 * hcR

/-- Complete prime-field traces have uniformly bounded normalized fourth moment. -/
theorem primeKloostermanTrace_normalized_fourth_le_two (p : Nat.Primes) :
    (∑ a : ZMod p.val, primeKloostermanTrace p a ^ 4) / (p.val : ℝ) ^ 3 ≤ 2 := by
  have hp : (0 : ℝ) < p.val := by exact_mod_cast p.property.pos
  apply (div_le_iff₀ (pow_pos hp 3)).mpr
  rw [sum_primeKloostermanTrace_four]
  split_ifs <;> nlinarith only [sq_nonneg (p.val : ℝ), hp]

#print axioms sum_primeKloostermanTrace_four
#print axioms primeKloostermanTrace_normalized_fourth_le_two

private theorem primeField_one_eq_neg_one_iff (p : Nat.Primes) :
    (1 : ZMod p.val) = -1 ↔ p.val = 2 := by
  constructor
  · intro h
    have hz : (2 : ZMod p.val) = 0 := by linear_combination h
    exact (Nat.prime_dvd_prime_iff_eq p.property Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p.val).mp hz)
  · intro h
    have hz : (2 : ZMod p.val) = 0 :=
      (ZMod.natCast_eq_zero_iff 2 p.val).mpr (by rw [h])
    linear_combination hz

/-- The sole exceptional prime contributes four to the fourth-moment polynomial. -/
theorem sum_primeKloostermanTrace_four_explicit (p : Nat.Primes) :
    ∑ a : ZMod p.val, primeKloostermanTrace p a ^ 4 =
      2 * (p.val : ℝ) ^ 3 - 3 * (p.val : ℝ) ^ 2 - 3 * p.val +
        if p.val = 2 then 4 else 0 := by
  rw [sum_primeKloostermanTrace_four, primeField_one_eq_neg_one_iff]
  by_cases h : p.val = 2
  · norm_num [h]
  · rw [if_neg h]

#print axioms sum_primeKloostermanTrace_four_explicit

end
end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
