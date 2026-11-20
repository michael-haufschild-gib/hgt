import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.RankDefectsAtTheUnitaryMidpoint

/-!
# Negative coefficients at the rank-five unitary midpoint

Two heavy pairs intersect, since disjoint unitary blocks have product at
most the integer. At a largest block the heavy pairs therefore form a star
or a full triangle. In rank five the triangle has price zero. The negative
price occurs exactly when even the weakest partner crosses the midpoint
with the largest block, in which case the price is minus two.
-/

open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

noncomputable section

private def block (k p : ℕ) := p^k.factorization p

/-- Partners of one prime-power block that cross the midpoint together with it. -/
def heavyPartners (k p : ℕ) := (k.primeFactors.erase p).filter fun q => k < (block k p * block k q)^2

private theorem heavy_pair_iff {k p q : ℕ} (hpq : p ≠ q) :
    {p,q} ∈ heavyUnitaryPairs k ↔ p ∈ k.primeFactors ∧ q ∈ k.primeFactors ∧ k < (block k p*block k q)^2 := by
  simp [heavyUnitaryPairs, primePowerSubset, block, hpq, insert_subset_iff, and_assoc]

/-- Disjoint unitary divisors cannot both lie above the square root. -/
theorem overweight_subsets_intersect {k : ℕ} (hk : 0 < k) {S T : Finset ℕ}
    (hS : S ⊆ k.primeFactors) (hT : T ⊆ k.primeFactors)
    (hs : k < (primePowerSubset k S)^2) (ht : k < (primePowerSubset k T)^2) :
    ∃ p, p ∈ S ∧ p ∈ T := by
  apply Finset.not_disjoint_iff.mp
  intro hd
  have hm : primePowerSubset k S * primePowerSubset k T ≤ k := by
    unfold primePowerSubset
    rw [← prod_union hd]
    calc
      _ ≤ ∏ i ∈ k.primeFactors, i^k.factorization i :=
        Finset.prod_le_prod_of_subset_of_one_le (union_subset hS hT) (fun _ _ => Nat.zero_le _)
          (fun i hi _ => Nat.succ_le_of_lt (pow_pos (Nat.prime_of_mem_primeFactors hi).pos _))
      _ = k := (Nat.prod_primeFactors_pow_factorization hk.ne').symm
  rcases le_total (primePowerSubset k S) (primePowerSubset k T) with he | he
  · exact hs.not_ge (by simpa only [pow_two] using (Nat.mul_le_mul_left _ he).trans hm)
  · exact ht.not_ge (by simpa only [pow_two] using (Nat.mul_le_mul_right _ he).trans hm)

private theorem heavy_meet {k : ℕ} {S T : Finset ℕ} (hS : S ∈ heavyUnitaryPairs k)
    (hT : T ∈ heavyUnitaryPairs k) : ∃ p, p ∈ S ∧ p ∈ T := by
  obtain ⟨hs,hsq⟩ := mem_filter.mp hS
  obtain ⟨ht,htq⟩ := mem_filter.mp hT
  obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hs
  have hne := (card_pos.mp (show 0 < S.card by omega)).mono hsub
  exact overweight_subsets_intersect (Nat.zero_lt_of_lt (Nat.nonempty_primeFactors.mp hne))
    hsub (mem_powersetCard.mp ht).1 hsq htq

private def star (k p : ℕ) := (heavyPartners k p).image (fun q => ({p,q} : Finset ℕ))

private theorem star_card (k p : ℕ) : (star k p).card = (heavyPartners k p).card := by
  apply card_image_of_injOn
  intro q hq r hr he
  have hqp := (mem_erase.mp (mem_filter.mp hq).1).1
  have he' : ({p,q} : Finset ℕ) = {p,r} := he
  have hq' : q ∈ ({p,r} : Finset ℕ) := by rw [← he']; simp
  simpa [hqp] using hq'

private theorem star_subset {k p : ℕ} (hp : p ∈ k.primeFactors) : star k p ⊆ heavyUnitaryPairs k := by
  intro S hS
  obtain ⟨q,hq,rfl⟩ := mem_image.mp hS
  obtain ⟨hq,hcut⟩ := mem_filter.mp hq
  obtain ⟨hne,hmem⟩ := mem_erase.mp hq
  exact (heavy_pair_iff hne.symm).mpr ⟨hp,hmem,hcut⟩

private theorem edge_in_star {k p : ℕ} {S : Finset ℕ} (h : S ∈ heavyUnitaryPairs k) (hp : p ∈ S) :
    S ∈ star k p := by
  obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp (mem_powersetCard.mp (mem_filter.mp h).1).2
  obtain rfl | rfl := (show p=x ∨ p=y by simpa using hp)
  · obtain ⟨_,hy,hcut⟩ := (heavy_pair_iff hxy).mp h
    exact mem_image.mpr ⟨y,mem_filter.mpr ⟨mem_erase.mpr ⟨hxy.symm,hy⟩,hcut⟩,rfl⟩
  · obtain ⟨hx,_,hcut⟩ := (heavy_pair_iff hxy).mp h
    exact mem_image.mpr ⟨x,mem_filter.mpr ⟨mem_erase.mpr ⟨hxy,hx⟩,by simpa [mul_comm] using hcut⟩,
      pair_comm _ _⟩

private theorem triangle_exhausts {k p x y : ℕ} (hpx : p ≠ x) (hpy : p ≠ y) (hxy : x ≠ y)
    (A : {x,y} ∈ heavyUnitaryPairs k) (B : {p,x} ∈ heavyUnitaryPairs k)
    (C : {p,y} ∈ heavyUnitaryPairs k) :
    heavyUnitaryPairs k = {{x,y},{p,x},{p,y}} := by
  apply Subset.antisymm _ (by simpa only [insert_subset_iff,singleton_subset_iff] using ⟨A,B,C⟩)
  intro S hS
  have hcard := (mem_powersetCard.mp (mem_filter.mp hS).1).2
  have eqedge {u v : ℕ} (hu : u ∈ S) (hv : v ∈ S) (hne : u ≠ v) : S = {u,v} := by
    apply Eq.symm
    exact eq_of_subset_of_card_le (by simp [insert_subset_iff, hu, hv]) (by simp [hne, hcard])
  have meet {u v : ℕ} (he : {u,v} ∈ heavyUnitaryPairs k) : u ∈ S ∨ v ∈ S := by
    obtain ⟨q,hq,huv⟩ := heavy_meet hS he
    rcases (show q=u ∨ q=v by simpa using huv) with rfl | rfl
    · exact Or.inl hq
    · exact Or.inr hq
  simp only [mem_insert,mem_singleton]
  by_cases hp : p ∈ S
  · rcases meet A with hx | hy
    · exact Or.inr (Or.inl (eqedge hp hx hpx))
    · exact Or.inr (Or.inr (eqedge hp hy hpy))
  · exact Or.inl (eqedge ((meet B).resolve_left hp) ((meet C).resolve_left hp) hxy)

private theorem largest_star_or_triangle {k p : ℕ} (hp : p ∈ k.primeFactors)
    (hmax : ∀ q ∈ k.primeFactors, block k q ≤ block k p) :
    heavyUnitaryPairs k = star k p ∨ ∃ x y, p ≠ x ∧ p ≠ y ∧ x ≠ y ∧
      heavyUnitaryPairs k = {{x,y},{p,x},{p,y}} := by
  by_cases hs : ∀ S ∈ heavyUnitaryPairs k, p ∈ S
  · exact Or.inl (Subset.antisymm (fun _ h => edge_in_star h (hs _ h)) (star_subset hp))
  push_neg at hs
  obtain ⟨S,hS,hn⟩ := hs
  obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp (mem_powersetCard.mp (mem_filter.mp hS).1).2
  have hpx : p ≠ x := fun e => hn (by simp [e])
  have hpy : p ≠ y := fun e => hn (by simp [e])
  obtain ⟨hx,hy,hcut⟩ := (heavy_pair_iff hxy).mp hS
  have hB : {p,x} ∈ heavyUnitaryPairs k := (heavy_pair_iff hpx).mpr ⟨hp,hx,by
    rw [mul_comm] at hcut
    exact hcut.trans_le (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (hmax y hy)) 2)⟩
  have hC : {p,y} ∈ heavyUnitaryPairs k := (heavy_pair_iff hpy).mpr ⟨hp,hy,
    hcut.trans_le (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (hmax x hx)) 2)⟩
  exact Or.inr ⟨x,y,hpx,hpy,hxy,triangle_exhausts hpx hpy hxy hS hB hC⟩

private theorem triangle_card {p x y : ℕ} (hpx : p ≠ x) (hpy : p ≠ y) (hxy : x ≠ y) :
    ({{x,y},{p,x},{p,y}} : Finset (Finset ℕ)).card = 3 := by
  have h₁ : ({x,y} : Finset ℕ) ≠ {p,x} := by
    intro h
    have hp : p ∈ ({x,y} : Finset ℕ) := by rw [h]; exact mem_insert_self _ _
    simpa [hpx,hpy] using hp
  have h₂ : ({x,y} : Finset ℕ) ≠ {p,y} := by
    intro h
    have hp : p ∈ ({x,y} : Finset ℕ) := by rw [h]; exact mem_insert_self _ _
    simpa [hpx,hpy] using hp
  have h₃ : ({p,x} : Finset ℕ) ≠ {p,y} := by
    intro h
    have hx : x ∈ ({p,y} : Finset ℕ) := h ▸ (show x ∈ ({p,x} : Finset ℕ) by simp)
    simpa [hpx.symm,hxy] using hx
  simp [h₁,h₂,h₃]

/-- A maximum block either contains all heavy edges or belongs to a unique heavy triangle. -/
theorem heavyUnitaryPairs_geometry (k : ℕ) : k.primeFactors = ∅ ∨
    ∃ p ∈ k.primeFactors, (heavyUnitaryPairs k = (heavyPartners k p).image (fun q => ({p,q} : Finset ℕ)) ∨
      ∃ x y, p ≠ x ∧ p ≠ y ∧ x ≠ y ∧ heavyUnitaryPairs k = {{x,y},{p,x},{p,y}}) := by
  rcases k.primeFactors.eq_empty_or_nonempty with he | hn
  · exact Or.inl he
  obtain ⟨p,hp,hm⟩ := k.primeFactors.exists_max_image (block k) hn
  exact Or.inr ⟨p,hp,largest_star_or_triangle hp hm⟩

private theorem partners_le {k p : ℕ} (hp : p ∈ k.primeFactors) :
    (heavyPartners k p).card ≤ k.primeFactors.card-1 := by
  rw [← card_erase_of_mem hp]
  exact card_le_card (filter_subset _ _)

/-- The rank-five signed price is negative exactly on a full four-edge star.
Its sole possible negative value is minus two. -/
theorem negative_balanced_five_iff_full_star
    (k : {k : ℕ // k.primeFactors.card = 5 ∧ oddSmoothSupport k}) :
    (unitaryHalfWeight k < 0 ↔ ∃ p ∈ k.val.primeFactors,
      ∀ q ∈ k.val.primeFactors.erase p, k.val < (p^k.val.factorization p * q^k.val.factorization q)^2) ∧
    (unitaryHalfWeight k < 0 ↔ unitaryHalfWeight k = -2) ∧ -2 ≤ unitaryHalfWeight k := by
  have hc := k.property.1
  have hprice := balanced_five_unitary_weight k
  have hn := card_pos.mp (by omega : 0 < k.val.primeFactors.card)
  obtain ⟨p,hp,hm⟩ := k.val.primeFactors.exists_max_image (block k.val) hn
  have hbound : (heavyUnitaryPairs k).card ≤ 4 := by
    rcases largest_star_or_triangle hp hm with hs | ⟨x,y,hx,hy,hxy,hs⟩
    · rw [hs,star_card]
      have h := partners_le hp
      omega
    · rw [hs,triangle_card hx hy hxy]
      decide
  have heq : unitaryHalfWeight k < 0 ↔ (heavyUnitaryPairs k).card = 4 := by omega
  refine ⟨heq.trans ⟨?_,?_⟩,by omega,by omega⟩
  · intro hfour
    rcases largest_star_or_triangle hp hm with hs | ⟨x,y,hx,hy,hxy,hs⟩
    · rw [hs,star_card] at hfour
      have hfull : heavyPartners k p = k.val.primeFactors.erase p := eq_of_subset_of_card_le
        (filter_subset _ _) (by rw [card_erase_of_mem hp,hc,hfour])
      exact ⟨p,hp,fun q hq => (mem_filter.mp (show q ∈ heavyPartners k p by rwa [hfull])).2⟩
    · rw [hs,triangle_card hx hy hxy] at hfour
      omega
  · rintro ⟨v,hv,hall⟩
    have hfull : heavyPartners k v = k.val.primeFactors.erase v := filter_eq_self.mpr hall
    have hl := card_le_card (star_subset hv)
    rw [star_card,hfull,card_erase_of_mem hv,hc] at hl
    omega


end

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
