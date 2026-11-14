import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.GreedyProductContainers
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.BernoulliCharacterDecay

/-!
# The Bernoulli measure on indexed subproducts

Choose each indexed factor independently with probability one half, retaining collisions
between different selections as multiplicity. The resulting mass is positive exactly on
the subproduct set, has total mass one, and has the Bernoulli character product as its
exact Fourier transform.
-/

open Finset
open scoped Pointwise

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

noncomputable section

variable {G ι : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [DecidableEq ι]

omit [Fintype G] in
/-- The pointwise product set is the image of all indexed selections. -/
theorem subproducts_eq_image_powerset (q : ι → G) (I : Finset ι) :
    subproducts q I = I.powerset.image (fun J => ∏ i ∈ J, q i) := by
  induction I using Finset.induction_on with
  | empty => simp [subproducts]; rfl
  | @insert i I hi ih =>
    rw [subproducts_insert q I i hi, ih, powerset_insert, image_union, image_image]
    congr 1
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := mem_smul_finset.mp hx
      obtain ⟨J, hJ, rfl⟩ := mem_image.mp hy
      have hiJ : i ∉ J := fun h => hi ((mem_powerset.mp hJ) h)
      exact mem_image.mpr ⟨J, hJ, by simp only [Function.comp_apply, prod_insert hiJ, smul_eq_mul]⟩
    · intro hx
      obtain ⟨J, hJ, rfl⟩ := mem_image.mp hx
      have hiJ : i ∉ J := fun h => hi ((mem_powerset.mp hJ) h)
      exact mem_smul_finset.mpr ⟨∏ j ∈ J, q j, mem_image.mpr ⟨J, hJ, rfl⟩,
        by simp only [Function.comp_apply, prod_insert hiJ, smul_eq_mul]⟩

/-- Probability mass of a group element under independent selection of the indexed factors. -/
def subproductMass (q : ι → G) (I : Finset ι) (g : G) : ℝ :=
  ((I.powerset.filter fun J => (∏ i ∈ J, q i) = g).card : ℝ) / 2 ^ I.card

omit [Fintype G] [DecidableEq ι] in
/-- Every subproduct mass is nonnegative. -/
theorem subproductMass_nonneg (q : ι → G) (I : Finset ι) (g : G) :
    0 ≤ subproductMass q I g := by
  unfold subproductMass
  positivity

omit [Fintype G] in
/-- Colliding selections retain positive mass, so the support is exactly the subproduct set. -/
theorem subproductMass_pos_iff (q : ι → G) (I : Finset ι) (g : G) :
    0 < subproductMass q I g ↔ g ∈ subproducts q I := by
  rw [subproducts_eq_image_powerset, mem_image]
  have hden : (0 : ℝ) < 2 ^ I.card := by positivity
  constructor
  · intro h
    have hc : 0 < (I.powerset.filter fun J => (∏ i ∈ J, q i) = g).card := by
      by_contra hn
      have hz : (I.powerset.filter fun J => (∏ i ∈ J, q i) = g).card = 0 := by omega
      simp only [subproductMass, hz, Nat.cast_zero, zero_div, lt_self_iff_false] at h
    obtain ⟨J, hJ⟩ := card_pos.mp hc
    exact ⟨J, (mem_filter.mp hJ).1, (mem_filter.mp hJ).2⟩
  · rintro ⟨J, hJ, hprod⟩
    exact div_pos (Nat.cast_pos.mpr (card_pos.mpr ⟨J, mem_filter.mpr ⟨hJ, hprod⟩⟩)) hden

private theorem sum_weighted_fiber_card {α β R : Type*} [Fintype β] [DecidableEq β]
    [CommSemiring R] (s : Finset α) (f : α → β) (F : β → R) :
    ∑ b, ((s.filter fun a => f a = b).card : R) * F b = ∑ a ∈ s, F (f a) := by
  calc
    _ = ∑ b, ∑ a ∈ s.filter (fun a => f a = b), F (f a) := by
      apply sum_congr rfl
      intro b _
      calc
        _ = ∑ _a ∈ s.filter (fun a => f a = b), F b := by
          rw [sum_const, nsmul_eq_mul]
        _ = _ := sum_congr rfl (fun a ha => by rw [(mem_filter.mp ha).2])
    _ = _ := sum_fiberwise s f (fun a => F (f a))

omit [DecidableEq ι] in
/-- The independent-selection mass sums to one, including the empty factor family. -/
theorem sum_subproductMass (q : ι → G) (I : Finset ι) :
    ∑ g, subproductMass q I g = 1 := by
  have h := sum_weighted_fiber_card I.powerset (fun J => ∏ i ∈ J, q i) (fun _ => (1 : ℝ))
  simp only [mul_one, sum_const, nsmul_eq_mul, mul_one, card_powerset,
    Nat.cast_pow, Nat.cast_ofNat] at h
  simp only [subproductMass, div_eq_mul_inv]
  rw [← sum_mul, h]
  exact mul_inv_cancel₀ (by positivity)

omit [DecidableEq ι] in
/-- The exact finite Fourier transform of the selection mass is the product of local multipliers. -/
theorem sum_subproductMass_character (q : ι → G) (I : Finset ι) (χ : G →* Circle) :
    ∑ g, (subproductMass q I g : ℂ) * (χ g : ℂ) = bernoulliCharacterProduct χ q I := by
  simp only [subproductMass, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  simp only [div_eq_mul_inv]
  calc
    _ = (∑ g, ((I.powerset.filter fun J => (∏ i ∈ J, q i) = g).card : ℂ) *
        (Circle.coeHom.comp χ) g) * ((2 : ℂ) ^ I.card)⁻¹ := by
      rw [sum_mul]
      apply sum_congr rfl
      intro g _
      change _ = _ * (χ g : ℂ) * _
      ring
    _ = (∑ J ∈ I.powerset, (Circle.coeHom.comp χ) (∏ i ∈ J, q i)) *
        ((2 : ℂ) ^ I.card)⁻¹ := by rw [sum_weighted_fiber_card]
    _ = bernoulliCharacterProduct χ q I := by
      simp only [map_prod]
      rw [← prod_one_add]
      change (∏ i ∈ I, (1 + (χ (q i) : ℂ))) * ((2 : ℂ) ^ I.card)⁻¹ =
        ∏ i ∈ I, (1 + (χ (q i) : ℂ)) / 2
      rw [prod_div_distrib, prod_const, div_eq_mul_inv]

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.subproducts_eq_image_powerset
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.subproductMass_nonneg
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.subproductMass_pos_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.sum_subproductMass
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.sum_subproductMass_character
