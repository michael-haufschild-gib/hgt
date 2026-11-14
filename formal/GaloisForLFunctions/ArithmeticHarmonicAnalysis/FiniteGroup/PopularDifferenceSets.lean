import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.PopularSymmetry
import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.DysonTransform

/-!
# Popular translations in difference sets and Dyson transforms

Half-popular translations are high-multiplicity quotients of points of a set. Their complement
forces geometric growth of the large Dyson component. A missing quotient forces the original
set to occupy at most half the group, while a set larger than half has every possible quotient.
-/

open Finset
open scoped Pointwise Classical

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

open HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- Half-popularity is precisely a threshold on the existing difference representation count. -/
theorem popular_eq_rep_filter (A : Finset G) :
    popularTranslations A = univ.filter (fun g => A.card < 2 * rep A A⁻¹ g) := by
  ext g
  simp only [popularTranslations, mem_filter, rep_eq_card_inter, inv_inv]

/-- The popular part of the difference representation spectrum has a strict cardinality bound. -/
theorem difference_popular_card (A : Finset G) :
    (univ.filter fun g => A.card < 2 * rep A A⁻¹ g).card < 2 * A.card ↔ A.Nonempty := by
  rw [← popular_eq_rep_filter]
  exact popular_card_lt_iff A

/-- The large Dyson component grows geometrically away from popular differences. -/
theorem difference_popular_or_dyson_growth (A : Finset G) (g : G) :
    A.card < 2 * rep A A⁻¹ g ∨ 3 * A.card ≤ 2 * (dysonLarge A A g).card := by
  have h := popular_or_growth A g
  simpa only [popular_eq_rep_filter, mem_filter, mem_univ, true_and, dysonLarge,
    union_comm] using h

omit [Fintype G] in
/-- A missing difference makes a set disjoint from its translate. -/
theorem difference_missing_iff_disjoint (A : Finset G) (g : G) :
    g ∉ A * A⁻¹ ↔ Disjoint A (g • A) := by
  rw [← rep_pos_iff_mem_mul, rep_eq_card_inter, inv_inv, not_lt, Nat.le_zero,
    card_eq_zero, disjoint_iff_inter_eq_empty]

/-- A quotient is either represented, or the original set occupies at most half the group. -/
theorem difference_hit_or_half (A : Finset G) (g : G) :
    g ∈ A * A⁻¹ ∨ 2 * A.card ≤ Fintype.card G := by
  by_cases hg : g ∈ A * A⁻¹
  · exact Or.inl hg
  have hd := (difference_missing_iff_disjoint A g).mp hg
  have hu := card_le_univ (s := A ∪ g • A)
  rw [card_union_of_disjoint hd, card_smul_finset] at hu
  exact Or.inr (by omega)

/-- Above half-density, the difference set is the entire group. -/
theorem difference_full_or_half (A : Finset G) :
    A * A⁻¹ = univ ∨ 2 * A.card ≤ Fintype.card G := by
  by_cases hh : 2 * A.card ≤ Fintype.card G
  · exact Or.inr hh
  exact Or.inl (eq_univ_of_forall fun g => (difference_hit_or_half A g).resolve_right hh)

/-- Every period of a nonempty set is popular. -/
theorem period_popular_or_empty (A : Finset G) (g : stabSubgroup A) :
    (g : G) ∈ popularTranslations A ∨ A = ∅ := by
  by_cases hA : A = ∅
  · exact Or.inr hA
  have hcard : 0 < A.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hA)
  have hfix : (g : G) • A = A := g.property
  simp only [popularTranslations, mem_filter, mem_univ, true_and, hfix, inter_self]
  exact Or.inl (by omega)

/-- Popular translations of a subgroup coincide exactly with that subgroup. -/
theorem popular_subgroup (H : Subgroup G) :
    popularTranslations (univ.filter fun g => g ∈ H) = univ.filter fun g => g ∈ H := by
  let A : Finset G := univ.filter fun g => g ∈ H
  have hA : IsSubgroupFinset A := {
    one_mem := by simp [A]
    mul_mem := by simpa only [A, mem_filter, mem_univ, true_and] using H.mul_mem
    inv_mem := by simpa only [A, mem_filter, mem_univ, true_and] using H.inv_mem }
  change popularTranslations A = A
  ext g
  constructor
  · intro hg
    have hc : 0 < (A ∩ g • A).card := by
      have hh := (mem_filter.mp hg).2
      omega
    obtain ⟨x, hx0⟩ := card_pos.mp hc
    obtain ⟨hx, hxg⟩ := mem_inter.mp hx0
    obtain ⟨y, hy, hxy⟩ := mem_smul_finset.mp hxg
    have hprod := hA.mul_mem hx (hA.inv_mem hy)
    simpa only [← hxy, smul_eq_mul, mul_inv_cancel_right] using hprod
  · intro hg
    have hfix := hA.smul_eq hg
    have hc := hA.card_pos'
    simp only [popularTranslations, mem_filter, mem_univ, true_and, hfix, inter_self]
    omega

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.difference_popular_card
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.difference_popular_or_dyson_growth
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.difference_full_or_half
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.period_popular_or_empty
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.popular_subgroup
