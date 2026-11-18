import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Prod
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic

/-!
# Cross families at full Hamming distance

The affine-chart argument of Choi and Jang, Lemma 2.1 (arXiv:2610.07631),
uses disjoint coordinate projections in two ternary word families. For
arbitrary finite alphabets the sharp bound on the product of family sizes
is the product of the balanced bipartition sizes of the individual alphabets.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
open Finset
open scoped Classical
noncomputable section

variable {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, Fintype (A i)]

/-- Largest family at full Hamming distance from every member of the given family. -/
def oppositeBox (S : Finset (∀ i, A i)) : Finset (∀ i, A i) :=
  Fintype.piFinset fun i => (S.image fun x => x i)ᶜ

theorem mem_oppositeBox (S : Finset (∀ i, A i)) (y : ∀ i, A i) :
    y ∈ oppositeBox S ↔ ∀ x ∈ S, ∀ i, x i ≠ y i := by
  simp only [oppositeBox, Fintype.mem_piFinset, mem_compl, mem_image, not_exists, not_and]
  exact ⟨fun h x hx i => h i x hx, fun h i x hx => h x hx i⟩

/-- The maximal opposite family has a product formula even for nonrectangular input. -/
theorem card_oppositeBox (S : Finset (∀ i, A i)) :
    (oppositeBox S).card = ∏ i, (Fintype.card (A i) - (S.image fun x => x i).card) := by
  simp [oppositeBox, Fintype.card_piFinset, card_compl]

/-- Taking the opposite reverses inclusion and forms a symmetric Galois connection. -/
theorem subset_oppositeBox_iff (S T : Finset (∀ i, A i)) :
    S ⊆ oppositeBox T ↔ T ⊆ oppositeBox S := by
  have flip (U V : Finset (∀ i, A i)) (h : U ⊆ oppositeBox V) : V ⊆ oppositeBox U :=
    fun v hv => (mem_oppositeBox U v).mpr fun u hu i =>
      ((mem_oppositeBox V u).mp (h hu) v hv i).symm
  exact ⟨flip S T, flip T S⟩

/-- Every family embeds in its double opposite. -/
theorem subset_double_oppositeBox (S : Finset (∀ i, A i)) :
    S ⊆ oppositeBox (oppositeBox S) := (subset_oppositeBox_iff _ _).mpr Subset.rfl

theorem oppositeBox_antitone : Antitone (oppositeBox (A := A)) := by
  intro S T h y hy
  exact (mem_oppositeBox S y).mpr fun x hx => (mem_oppositeBox T y).mp hy x (h hx)

/-- Maximal opposite families are exactly the fixed points of double opposition. -/
theorem oppositeBox_triple (S : Finset (∀ i, A i)) :
    oppositeBox (oppositeBox (oppositeBox S)) = oppositeBox S :=
  Subset.antisymm (oppositeBox_antitone (subset_double_oppositeBox S))
    (subset_double_oppositeBox _)

private theorem balanced_split (a b : ℕ) :
    a * b ≤ ((a+b)/2) * ((a+b+1)/2) := by
  rcases Nat.le_total a b with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have h₁ : (a + (a+d))/2 = a + d/2 := by omega
    have h₂ : (a + (a+d)+1)/2 = a + (d+1)/2 := by omega
    have h₃ : d = d/2 + (d+1)/2 := by omega
    rw [h₁, h₂]
    nlinarith only [congrArg (a * ·) h₃, Nat.zero_le ((d/2) * ((d+1)/2))]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have h₁ : (b+d+b)/2 = b + d/2 := by omega
    have h₂ : (b+d+b+1)/2 = b + (d+1)/2 := by omega
    have h₃ : d = d/2 + (d+1)/2 := by omega
    rw [h₁, h₂]
    nlinarith only [congrArg (b * ·) h₃, Nat.zero_le ((d/2) * ((d+1)/2))]

/-- The sharp product bound with possibly different alphabet sizes. -/
theorem card_mul_card_oppositeBox_le (S : Finset (∀ i, A i)) :
    S.card * (oppositeBox S).card ≤ ∏ i, ((Fintype.card (A i))/2) *
      ((Fintype.card (A i)+1)/2) := by
  let D := fun i => S.image fun x => x i
  have h : S ⊆ Fintype.piFinset D :=
    fun x hx => Fintype.mem_piFinset.mpr fun i => mem_image_of_mem _ hx
  calc
    _ ≤ (Fintype.piFinset D).card * (oppositeBox S).card :=
      Nat.mul_le_mul_right _ (card_le_card h)
    _ = ∏ i, (D i).card * (Fintype.card (A i) - (D i).card) := by
      rw [card_oppositeBox, Fintype.card_piFinset, prod_mul_distrib]
    _ ≤ _ := by
      apply prod_le_prod' fun i _ => ?_
      have hcard := (D i).card_le_univ
      have he : (D i).card + (Fintype.card (A i) - (D i).card) = Fintype.card (A i) := by omega
      simpa only [he] using balanced_split (D i).card (Fintype.card (A i) - (D i).card)

/-- Complementary coordinate boxes attain the upper bound, for every alphabet profile. -/
theorem exists_sharp_opposite_pair :
    ∃ S T : Finset (∀ i, A i), T ⊆ oppositeBox S ∧
      S.card * T.card = ∏ i, ((Fintype.card (A i))/2) * ((Fintype.card (A i)+1)/2) := by
  have hex (i : ι) : ∃ d : Finset (A i), d ⊆ univ ∧ d.card = Fintype.card (A i)/2 :=
    exists_subset_card_eq (by simp [Nat.div_le_self])
  choose D _ hD using hex
  refine ⟨Fintype.piFinset D, Fintype.piFinset (fun i => (D i)ᶜ), ?_, ?_⟩
  · intro y hy
    refine (mem_oppositeBox _ _).mpr fun x hx i hxy => ?_
    exact (mem_compl.mp (Fintype.mem_piFinset.mp hy i)) (hxy ▸ Fintype.mem_piFinset.mp hx i)
  · rw [Fintype.card_piFinset, Fintype.card_piFinset, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    rw [card_compl, hD]
    congr 1
    omega

/-- Two ternary three-coordinate families of size at least three must agree
somewhere across the families. This strengthens the four-point chart obstruction. -/
theorem ternary_chart_collision (S T : Finset (Fin 3 → Fin 3)) :
    3 ≤ S.card ∧ 3 ≤ T.card → ∃ x ∈ S, ∃ y ∈ T, ∃ i, x i = y i := by
  rintro ⟨hS, hT⟩
  by_contra! h
  have hsub : T ⊆ oppositeBox S := fun y hy => (mem_oppositeBox _ _).mpr fun x hx i =>
    h x hx y hy i
  have hu := card_mul_card_oppositeBox_le S
  simp only [Fintype.card_fin, prod_const, card_univ] at hu
  have hlow := Nat.mul_le_mul hS (hT.trans (card_le_card hsub))
  omega

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
