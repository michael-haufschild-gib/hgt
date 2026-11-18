import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.SeparatedWordBoxes

/-!
# Minimum rectangle covers of ternary full-distance pairs

The coordinate separation bound in the proof of Choi–Jang, Lemma 2.1,
controls how many ordered pairs a single rectangle can contain. For
ternary words it gives the exact cover number in every dimension, even
when rectangles overlap. All optimal rectangles have maximal volume.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
open Finset
open scoped Classical
noncomputable section

variable {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, Fintype (A i)]

/-- All pairs that differ in every coordinate. -/
def fullDistancePairs : Finset ((∀ i, A i) × (∀ i, A i)) :=
  univ.biUnion fun x => ({x} : Finset _) ×ˢ oppositeBox {x}

theorem mem_fullDistancePairs (x y : ∀ i, A i) :
    (x,y) ∈ fullDistancePairs ↔ ∀ i, x i ≠ y i := by
  simp [fullDistancePairs, mem_oppositeBox]

/-- Exact pair count with possibly different alphabets in different coordinates. -/
theorem card_fullDistancePairs :
    (fullDistancePairs (A := A)).card = ∏ i, Fintype.card (A i) * (Fintype.card (A i)-1) := by
  unfold fullDistancePairs
  rw [card_biUnion]
  · simp [card_oppositeBox, Fintype.card_pi, prod_mul_distrib]
  · intro x _ y _ hne
    rw [Function.onFun, disjoint_left]
    intro v hx hy
    exact hne ((mem_singleton.mp (mem_product.mp hx).1).symm.trans
      (mem_singleton.mp (mem_product.mp hy).1))

/-- Union of the largest full-distance rectangles with the prescribed left sides. -/
def rectangleCoverage (L : Finset (Finset (∀ i, A i))) : Finset ((∀ i, A i) × (∀ i, A i)) :=
  L.biUnion fun S => S ×ˢ oppositeBox S

/-- Every rectangle inside the full-distance relation lies in its maximal completion. -/
theorem product_subset_fullDistancePairs_iff (S T : Finset (∀ i, A i)) :
    S ×ˢ T ⊆ fullDistancePairs ↔ T ⊆ oppositeBox S := by
  constructor
  · exact fun h y hy => (mem_oppositeBox _ _).mpr fun x hx =>
      (mem_fullDistancePairs _ _).mp (h (mem_product.mpr ⟨hx,hy⟩))
  · rintro h ⟨x,y⟩ hxy
    obtain ⟨hx,hy⟩ := mem_product.mp hxy
    exact (mem_fullDistancePairs _ _).mpr ((mem_oppositeBox _ _).mp (h hy) x hx)

/-- A union of rectangles can cover at most their number times the sharp one-box capacity. -/
theorem card_rectangleCoverage_le (L : Finset (Finset (∀ i, A i))) :
    (rectangleCoverage L).card ≤ L.card * ∏ i, (Fintype.card (A i)/2)*((Fintype.card (A i)+1)/2) := by
  apply card_biUnion_le_card_mul L _ _
  intro S _
  rw [card_product]
  exact card_mul_card_oppositeBox_le S

/-- One rectangle per word always covers the full relation. -/
theorem singleton_rectangleCoverage :
    rectangleCoverage (univ.image (fun x : ∀ i, A i => ({x} : Finset _))) = fullDistancePairs := by
  ext ⟨x,y⟩
  simp [rectangleCoverage, fullDistancePairs]

private theorem exists_singleton_cover :
    ∃ L : Finset (Finset (∀ i, A i)), rectangleCoverage L = fullDistancePairs ∧
      L.card = Fintype.card (∀ i, A i) := by
  let f := fun x : ∀ i, A i => ({x} : Finset (∀ i, A i))
  have hi : Function.Injective f := fun _ _ h => singleton_inj.mp h
  exact ⟨univ.image f,singleton_rectangleCoverage,
    (card_image_of_injective _ hi).trans card_univ⟩

private theorem coverage_le_sum (L : Finset (Finset (∀ i, A i))) :
    (rectangleCoverage L).card ≤ ∑ S ∈ L, S.card * (oppositeBox S).card := by
  unfold rectangleCoverage
  exact card_biUnion_le.trans_eq (sum_congr rfl (fun S _ => card_product S (oppositeBox S)))

/-- The ternary chart has exact rectangle cover number `3^d` in dimension `d`. -/
theorem ternary_rectangle_cover_number :
    IsLeast {k : ℕ | ∃ L : Finset (Finset (ι → Fin 3)),
      rectangleCoverage L = fullDistancePairs ∧ L.card = k} (3^Fintype.card ι) := by
  constructor
  · obtain ⟨L,hL,hcard⟩ := exists_singleton_cover (A := fun _ : ι => Fin 3)
    exact ⟨L,hL,by simpa only [Fintype.card_fun,Fintype.card_fin] using hcard⟩
  · rintro k ⟨L,hL,rfl⟩
    have h := card_rectangleCoverage_le L
    rw [hL,card_fullDistancePairs] at h
    simp only [Fintype.card_fin, prod_const, card_univ] at h
    have hv : (3*(3-1))^Fintype.card ι = 3^Fintype.card ι * 2^Fintype.card ι :=
      Nat.mul_pow _ _ _
    rw [hv] at h
    exact Nat.le_of_mul_le_mul_right h (by positivity)

/-- Saturation is rigid: in every minimum ternary cover each member has
maximal possible volume, even when overlaps were allowed. -/
theorem ternary_cover_saturation (L : Finset (Finset (ι → Fin 3))) :
    rectangleCoverage L = fullDistancePairs → L.card = 3^Fintype.card ι →
    ∀ S ∈ L, S.card * (oppositeBox S).card = 2^Fintype.card ι := by
  intro hcover hsize
  have hbound (S : Finset (ι → Fin 3)) :
      S.card * (oppositeBox S).card ≤ 2^Fintype.card ι := by
    simpa using card_mul_card_oppositeBox_le S
  apply (sum_eq_sum_iff_of_le (fun S (_ : S ∈ L) => hbound S)).mp
  apply le_antisymm (sum_le_sum (fun S _ => hbound S))
  have h := coverage_le_sum L
  rw [hcover, card_fullDistancePairs] at h
  simp only [Fintype.card_fin,prod_const,card_univ] at h
  change (3*2)^Fintype.card ι ≤ _ at h
  rw [mul_pow] at h
  simpa only [sum_const,nsmul_eq_mul,Nat.cast_id,hsize] using h

#print axioms card_fullDistancePairs
#print axioms product_subset_fullDistancePairs_iff
#print axioms ternary_rectangle_cover_number
#print axioms ternary_cover_saturation

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
