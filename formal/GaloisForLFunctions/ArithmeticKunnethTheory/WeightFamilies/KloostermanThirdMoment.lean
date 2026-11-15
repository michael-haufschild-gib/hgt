import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.HyperplaneTateTrace
import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanLocalStatistics

/-!
# The cubic Kloosterman moment and the third cyclotomic locus

The normalized three-coordinate reciprocal locus is exactly `t² + t + 1 = 0`.
Its point count determines the cubic moment over every finite field, including
characteristic three. For prime fields this gives the signed cubic statistic of
the complete and punctured families, with no equidistribution input.
-/

open Finset

namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The third cyclotomic equation, retaining its characteristic-three root. -/
def cubicCyclotomicRoots : Finset F := univ.filter (fun t => t ^ 2 + t + 1 = 0)

/-- A root factors the quadratic, including inseparable characteristic three. -/
theorem cubicCyclotomicRoots_eq_pair {r : F} (hr : r ^ 2 + r + 1 = 0) :
    cubicCyclotomicRoots (F := F) = {r, -1 - r} := by
  ext t
  simp only [cubicCyclotomicRoots, mem_filter, mem_univ, true_and,
    mem_insert, mem_singleton]
  have hf : t ^ 2 + t + 1 = (t - r) * (t - (-1 - r)) := by
    linear_combination hr
  rw [hf, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- The two roots merge exactly in characteristic three. -/
theorem cubicCyclotomicRoots_card :
    (cubicCyclotomicRoots (F := F)).card =
      if (3 : F) = 0 then 1 else if ∃ r : F, r ^ 2 + r + 1 = 0 then 2 else 0 := by
  by_cases h3 : (3 : F) = 0
  · rw [if_pos h3]
    have hr : (1 : F) ^ 2 + 1 + 1 = 0 := by linear_combination h3
    rw [cubicCyclotomicRoots_eq_pair hr]
    have he : (-1 - 1 : F) = 1 := by linear_combination -h3
    simp only [he, insert_eq_of_mem, mem_singleton, card_singleton]
  · rw [if_neg h3]
    split_ifs with hex
    · obtain ⟨r, hr⟩ := hex
      rw [cubicCyclotomicRoots_eq_pair hr]
      apply card_pair
      intro he
      have hlin : 2 * r + 1 = 0 := by linear_combination he
      apply h3
      linear_combination 4 * hr - (2 * r + 1) * hlin
    · have he : cubicCyclotomicRoots (F := F) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro r hr
        exact hex ⟨r, (mem_filter.mp hr).2⟩
      rw [he, card_empty]

/-- Eliminating the second coordinate identifies the reciprocal locus with a quadratic. -/
theorem mem_normalizedDoubleZeroTorus_two (x : MomentTorus F 2) :
    x ∈ normalizedDoubleZeroTorus 2 ↔
      (x 1 : F) = -1 - x 0 ∧ (x 0 : F) ^ 2 + x 0 + 1 = 0 := by
  have h0 := (x 0).property
  have h1 := (x 1).property
  simp only [normalizedDoubleZeroTorus, normalizedCoordinateZeroTorus,
    mem_filter, mem_univ, true_and, Fin.sum_univ_two]
  constructor
  · rintro ⟨hs, hr⟩
    have he : (x 1 : F) = -1 - x 0 := by linear_combination hs
    refine ⟨he, ?_⟩
    field_simp [h0, h1] at hr
    rw [he] at hr
    linear_combination -hr
  · rintro ⟨he, hp⟩
    constructor
    · rw [he]; ring
    · field_simp [h0, h1]
      rw [he]
      linear_combination -hp

/-- Each cyclotomic root supplies one normalized torus point, and every point arises so. -/
theorem normalizedDoubleZeroTorus_two_card :
    (normalizedDoubleZeroTorus (F := F) 2).card = (cubicCyclotomicRoots (F := F)).card := by
  apply card_bij (fun (x : MomentTorus F 2) _ => (x 0 : F))
  · intro x hx
    exact mem_filter.mpr ⟨mem_univ _, (mem_normalizedDoubleZeroTorus_two x).mp hx |>.2⟩
  · intro x hx y hy hxy
    have hx' := (mem_normalizedDoubleZeroTorus_two x).mp hx
    have hy' := (mem_normalizedDoubleZeroTorus_two y).mp hy
    funext i
    apply Subtype.ext
    fin_cases i
    · exact hxy
    · change (x 1 : F) = (y 1 : F)
      rw [hx'.1, hy'.1, hxy]
  · intro t ht
    have ht' : t ^ 2 + t + 1 = 0 := (mem_filter.mp ht).2
    have ht0 : t ≠ 0 := by intro h; simp [h] at ht'
    have ht1 : -1 - t ≠ 0 := by
      intro h
      have he : t = -1 := by linear_combination -h
      simp [he] at ht'
    let x : MomentTorus F 2 := ![⟨t, ht0⟩, ⟨-1 - t, ht1⟩]
    refine ⟨x, (mem_normalizedDoubleZeroTorus_two x).mpr ?_, rfl⟩
    exact ⟨rfl, ht'⟩

/-- The complete cubic moment is a quadratic point count with its hyperplane term removed. -/
theorem kloosterman_third_moment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {b : F} (hb : b ≠ 0) :
    ∑ a : F, SignedSuccessorArithmetic.kloosterman ψ a b ^ 3 =
      ((cubicCyclotomicRoots (F := F)).card - 1 : ℂ) * (Fintype.card F : ℂ) ^ 2 +
        2 * (Fintype.card F : ℂ) := by
  have h := kloosterman_moment_double_count hψ hb 2
  rw [normalizedDoubleZeroTorus_two_card] at h
  calc
    _ = _ := h
    _ = _ := by ring

private instance primeFieldFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

/-- The exact signed cubic moment of the complete prime-field family. -/
theorem sum_primeKloostermanTrace_cube (p : Nat.Primes) :
    ∑ a : ZMod p.val, primeKloostermanTrace p a ^ 3 =
      ((cubicCyclotomicRoots (F := ZMod p.val)).card - 1 : ℝ) * (p.val : ℝ) ^ 2 +
        2 * (p.val : ℝ) := by
  have hreal (a : ZMod p.val) :
      SignedSuccessorArithmetic.kloosterman ZMod.stdAddChar a 1 =
        (primeKloostermanTrace p a : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using primeKloostermanTrace_im p a
  have h := kloosterman_third_moment (ZMod.isPrimitive_stdAddChar p.val)
    (b := (1 : ZMod p.val)) one_ne_zero
  simp only [hreal, ZMod.card] at h
  exact_mod_cast h

/-- Deleting the singular parameter adds one to the cubic moment. -/
theorem sum_primeKloostermanTrace_cube_ne_zero (p : Nat.Primes) :
    ∑ a ∈ (univ : Finset (ZMod p.val)).erase 0, primeKloostermanTrace p a ^ 3 =
      ((cubicCyclotomicRoots (F := ZMod p.val)).card - 1 : ℝ) * (p.val : ℝ) ^ 2 +
        2 * (p.val : ℝ) + 1 := by
  rw [sum_erase_eq_sub (mem_univ 0), sum_primeKloostermanTrace_cube,
    primeKloostermanTrace_zero]
  ring

#print axioms normalizedDoubleZeroTorus_two_card
#print axioms cubicCyclotomicRoots_card
#print axioms kloosterman_third_moment
#print axioms sum_primeKloostermanTrace_cube
#print axioms sum_primeKloostermanTrace_cube_ne_zero

end
end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
