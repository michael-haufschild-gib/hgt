import GaloisForLFunctions.goldbach.OddCharacterProjection
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.BernoulliDifferenceMeasure
import GaloisForLFunctions.RHTower.OffLineAnnihilatingWeightsCountCriticalZeros

/-!
# Bernoulli subproducts in reduced residue groups

The reduced-residue Parseval identity turns fourth-power Bernoulli character decay
into a lower bound for the quotient set of indexed subproducts. Its odd-character
projection gives an exact obstruction to avoiding the residue `-1`: the odd spectral
mass must pay for the diagonal energy of the selection measure.
-/

open Finset
open scoped Classical Pointwise

namespace GaloisForLFunctions.Goldbach

open ArithmeticHarmonicAnalysis.FiniteGroup

noncomputable section

/-- Restriction of a Dirichlet character to units, with its unit modulus recorded. -/
def unitCircleCharacter (N : ℕ) (χ : DirichletCharacter ℂ (N + 1)) :
    (ZMod (N + 1))ˣ →* Circle where
  toFun a := ⟨χ a, mem_sphere_zero_iff_norm.mpr
    (Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity a))⟩
  map_one' := by apply Subtype.ext; exact map_one χ
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul χ (a : ZMod (N + 1)) (b : ZMod (N + 1))

/-- Parseval and support Cauchy–Schwarz give a spectral container on reduced residues. -/
theorem unit_spectral_container (N : ℕ) (w : (ZMod (N + 1))ˣ → ℂ) :
    ((N + 1).totient : ℝ) * ‖∑ a, w a‖ ^ 2 ≤
      ((univ.filter fun a => w a ≠ 0).card : ℝ) *
        ∑ χ : DirichletCharacter ℂ (N + 1), ‖unitCharacterSum N w χ‖ ^ 2 := by
  have h := _root_.RHTower.ZeroValueConfig.norm_sum_sq_le_card_support_mul univ w
  rw [sum_norm_sq_unitCharacterSum]
  have hm := mul_le_mul_of_nonneg_left h
    (Nat.cast_nonneg (N + 1).totient : (0 : ℝ) ≤ (N + 1).totient)
  simpa only [mul_left_comm] using hm

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- The Dirichlet transform of the selection measure is its Bernoulli product. -/
theorem unitCharacterSum_subproductMass (N : ℕ) (q : ι → (ZMod (N + 1))ˣ)
    (I : Finset ι) (χ : DirichletCharacter ℂ (N + 1)) :
    unitCharacterSum N (fun a => (subproductMass q I a : ℂ)) χ =
      bernoulliCharacterProduct (unitCircleCharacter N χ) q I :=
  sum_subproductMass_character q I (unitCircleCharacter N χ)

omit [DecidableEq ι] in
/-- Quotients of independent selections have a nonnegative Dirichlet transform. -/
theorem unitCharacterSum_subproductDifferenceMass (N : ℕ)
    (q : ι → (ZMod (N + 1))ˣ) (I : Finset ι)
    (χ : DirichletCharacter ℂ (N + 1)) :
    unitCharacterSum N (fun a => (subproductDifferenceMass q I a : ℂ)) χ =
      (Complex.normSq (bernoulliCharacterProduct (unitCircleCharacter N χ) q I) : ℂ) :=
  sum_subproductDifferenceMass_character q I (unitCircleCharacter N χ)

/-- Fourth-power character decay bounds the size of the actual quotient set of subproducts. -/
theorem subproduct_difference_spectral_container (N : ℕ)
    (q : ι → (ZMod (N + 1))ˣ) (I : Finset ι) :
    ((N + 1).totient : ℝ) ≤
      ((subproducts q I * (subproducts q I)⁻¹).card : ℝ) *
        ∑ χ : DirichletCharacter ℂ (N + 1),
          (9 / 16 : ℝ) ^ (I.filter fun i => (χ (q i)).re ≤ 1 / 2).card := by
  have hs : (univ.filter fun a => (subproductDifferenceMass q I a : ℂ) ≠ 0) =
      subproducts q I * (subproducts q I)⁻¹ := by
    ext a
    simp only [mem_filter, mem_univ, true_and, ne_eq, Complex.ofReal_eq_zero]
    rw [← subproductDifferenceMass_pos_iff]
    constructor
    · intro ha
      exact lt_of_le_of_ne (subproductDifferenceMass_nonneg q I a) (Ne.symm ha)
    · exact ne_of_gt
  have h := unit_spectral_container N (fun a => (subproductDifferenceMass q I a : ℂ))
  rw [hs, ← Complex.ofReal_sum, sum_subproductDifferenceMass] at h
  simp only [Complex.ofReal_one, norm_one, one_pow, mul_one] at h
  refine h.trans (mul_le_mul_of_nonneg_left (sum_le_sum fun χ _ => ?_) (by positivity))
  rw [← Complex.normSq_eq_norm_sq]
  exact subproductDifferenceMass_fourth_decay q I (unitCircleCharacter N χ)

omit [DecidableEq ι] in
/-- Odd spectral mass equals diagonal selection energy minus mass at the negative unit. -/
theorem subproduct_odd_moment (N : ℕ) (q : ι → (ZMod (N + 1))ˣ) (I : Finset ι) :
    2 * (∑ χ : DirichletCharacter ℂ (N + 1) with χ.Odd,
      Complex.normSq (bernoulliCharacterProduct (unitCircleCharacter N χ) q I)) =
        ((N + 1).totient : ℝ) *
          ((∑ a, subproductMass q I a ^ 2) - subproductDifferenceMass q I (-1)) := by
  have h := twice_sum_odd_norm_sq_unitCharacterSum N (subproductMass q I)
  simp only [unitCharacterSum_subproductMass, ← Complex.normSq_eq_norm_sq] at h
  have hr : (∑ a, subproductMass q I (-a) * subproductMass q I a) =
      subproductDifferenceMass q I (-1) := by
    unfold subproductDifferenceMass finiteAutocorrelation
    apply sum_congr rfl
    intro a _
    simp only [inv_neg, inv_one, neg_one_mul]
    exact mul_comm _ _
  rw [hr] at h
  exact h

private theorem subproduct_energy_bound (N : ℕ) (q : ι → (ZMod (N + 1))ˣ)
    (I : Finset ι) : 1 ≤ (2 : ℝ) ^ I.card * ∑ a, subproductMass q I a ^ 2 := by
  have hs : (univ.filter fun a => (subproductMass q I a : ℂ) ≠ 0) =
      subproducts q I := by
    ext a
    simp only [mem_filter, mem_univ, true_and, ne_eq, Complex.ofReal_eq_zero]
    rw [← subproductMass_pos_iff]
    constructor
    · intro ha
      exact lt_of_le_of_ne (subproductMass_nonneg q I a) (Ne.symm ha)
    · exact ne_of_gt
  have h := _root_.RHTower.ZeroValueConfig.norm_sum_sq_le_card_support_mul
    univ (fun a => (subproductMass q I a : ℂ))
  rw [hs, ← Complex.ofReal_sum, sum_subproductMass] at h
  simp only [Complex.ofReal_one, norm_one, one_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs] at h
  have hc : (subproducts q I).card ≤ 2 ^ I.card := by
    rw [subproducts_eq_image_powerset]
    exact (card_image_le).trans_eq (card_powerset I)
  have hc' : ((subproducts q I).card : ℝ) ≤ 2 ^ I.card := by exact_mod_cast hc
  exact h.trans (mul_le_mul_of_nonneg_right hc' (sum_nonneg fun a _ => sq_nonneg _))

/-- Avoiding `-1` forces an explicit lower bound on the odd-character moment. -/
theorem subproduct_negative_unit_or_odd_barrier (N : ℕ)
    (q : ι → (ZMod (N + 1))ˣ) (I : Finset ι) :
    (-1 : (ZMod (N + 1))ˣ) ∈ subproducts q I * (subproducts q I)⁻¹ ∨
      ((N + 1).totient : ℝ) ≤ (2 : ℝ) ^ (I.card + 1) *
        ∑ χ : DirichletCharacter ℂ (N + 1) with χ.Odd,
          Complex.normSq (bernoulliCharacterProduct (unitCircleCharacter N χ) q I) := by
  by_cases hmem : (-1 : (ZMod (N + 1))ˣ) ∈ subproducts q I * (subproducts q I)⁻¹
  · exact Or.inl hmem
  right
  have hz : subproductDifferenceMass q I (-1) = 0 := by
    have hn : ¬ 0 < subproductDifferenceMass q I (-1) :=
      fun h => hmem ((subproductDifferenceMass_pos_iff q I (-1)).mp h)
    exact le_antisymm (le_of_not_gt hn) (subproductDifferenceMass_nonneg q I (-1))
  have ho := subproduct_odd_moment N q I
  rw [hz, sub_zero] at ho
  have he := mul_le_mul_of_nonneg_left (subproduct_energy_bound N q I)
    (Nat.cast_nonneg (N + 1).totient : (0 : ℝ) ≤ (N + 1).totient)
  rw [mul_one] at he
  calc
    _ ≤ ((N + 1).totient : ℝ) * ((2 : ℝ) ^ I.card * ∑ a, subproductMass q I a ^ 2) := he
    _ = (2 : ℝ) ^ I.card * (2 * ∑ χ : DirichletCharacter ℂ (N + 1) with χ.Odd,
          Complex.normSq (bernoulliCharacterProduct (unitCircleCharacter N χ) q I)) := by
      rw [ho]; ring
    _ = _ := by rw [pow_succ]; ring

/-- Local half-plane contraction gives a completely explicit parity barrier. -/
theorem subproduct_negative_unit_or_character_count (N : ℕ)
    (q : ι → (ZMod (N + 1))ˣ) (I : Finset ι) :
    (-1 : (ZMod (N + 1))ˣ) ∈ subproducts q I * (subproducts q I)⁻¹ ∨
      ((N + 1).totient : ℝ) ≤ (2 : ℝ) ^ (I.card + 1) *
        ∑ χ : DirichletCharacter ℂ (N + 1) with χ.Odd,
          (3 / 4 : ℝ) ^ (I.filter fun i => (χ (q i)).re ≤ 1 / 2).card := by
  rcases subproduct_negative_unit_or_odd_barrier N q I with h | h
  · exact Or.inl h
  · right
    exact h.trans (mul_le_mul_of_nonneg_left
      (sum_le_sum fun χ _ => bernoulliCharacterProduct_decay (unitCircleCharacter N χ) q I)
      (by positivity))

end
end GaloisForLFunctions.Goldbach

#print axioms GaloisForLFunctions.Goldbach.unit_spectral_container
#print axioms GaloisForLFunctions.Goldbach.unitCharacterSum_subproductMass
#print axioms GaloisForLFunctions.Goldbach.unitCharacterSum_subproductDifferenceMass
#print axioms GaloisForLFunctions.Goldbach.subproduct_difference_spectral_container
#print axioms GaloisForLFunctions.Goldbach.subproduct_odd_moment
#print axioms GaloisForLFunctions.Goldbach.subproduct_negative_unit_or_odd_barrier
#print axioms GaloisForLFunctions.Goldbach.subproduct_negative_unit_or_character_count
