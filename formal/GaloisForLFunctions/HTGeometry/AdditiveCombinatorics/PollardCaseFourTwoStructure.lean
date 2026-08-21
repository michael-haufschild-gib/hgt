import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardCaseFourTwoMixed

/-!
# CASE 4.2 of Grynkiewicz's proof: the structure of the mixed cosets

A coset `α · H` is *mixed* when it meets both `A` and `B` while `A ∩ (α·H)` and `B ∩ (α·H)` are
disjoint — equivalently, when it is not contained in `A ∩ B`.  Writing `C_α = A ∩ (α·H)` and
`D_α = B ∩ (α·H)`, maximality of the Dyson witness gives `C_α · D_α⁻¹ · D_β ⊆ C_β`, from which:

* the `C_α` are translates of one another, so they all have the same cardinality and the same
  stabiliser `K`;
* each `D_α` lies inside a single `K`-coset;
* hence `#(C_α · D_β) = #C_α`, and every element of `C_α · D_β` has at least `#D_β`
  representations in `A × B`.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

omit [Fintype G] in
theorem smul_coset_eq {H : Finset G} (hH : IsSubgroupFinset H) {y : G} (hy : y ∈ H) (α : G) :
    y • (α • H) = α • H := by
  rw [smul_smul, mul_comm y α, ← smul_smul, hH.smul_eq hy]

omit [Fintype G] in
/-- **The relation `C_α · D_α⁻¹ · D_β ⊆ C_β`.** -/
theorem vitadel {A B H : Finset G} (hH : IsSubgroupFinset H)
    (hper : (A ∩ B) * H = A ∩ B)
    (hmax : ∀ z : G, (dysonSmall A B z).Nonempty → (dysonSmall A B z).card < B.card →
        (dysonSmall A B z).card ≤ (dysonSmall A B 1).card)
    {α β c d : G} (hdisj : Disjoint (A ∩ (α • H)) (B ∩ (α • H)))
    (hc : c ∈ A ∩ (α • H)) (hd : d ∈ B ∩ (α • H)) :
    (c * d⁻¹) • (B ∩ (β • H)) ⊆ A ∩ (β • H) := by
  classical
  have hcB : c ∉ B := by
    intro hcB
    exact (Finset.disjoint_left.1 hdisj) hc (Finset.mem_inter.2 ⟨hcB, (Finset.mem_inter.1 hc).2⟩)
  have hcH : c • H = α • H := hH.smul_eq_smul_of_mem (Finset.mem_inter.1 hc).2
  have hdH : d • H = α • H := hH.smul_eq_smul_of_mem (Finset.mem_inter.1 hd).2
  have hdc : d ∈ c • H := by rw [hcH, ← hdH]; exact hH.mem_smul_self d
  have hsubA := dysonSmall_full_of_mixed hH hper hmax (Finset.mem_inter.1 hc).1 hcB
    (Finset.mem_inter.1 hd).1 hdc
  have hyH : c * d⁻¹ ∈ H := by
    have h1 : c⁻¹ * d ∈ H := mem_smul_finset_iff.1 hdc
    have h2 : (c⁻¹ * d)⁻¹ ∈ H := hH.inv_mem h1
    simpa [mul_comm] using h2
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Finset.mem_smul_finset.1 hz
  refine Finset.mem_inter.2 ⟨?_, ?_⟩
  · exact hsubA (Finset.mem_smul_finset.2 ⟨w, (Finset.mem_inter.1 hw).1, rfl⟩)
  · have hwH : w ∈ β • H := (Finset.mem_inter.1 hw).2
    have hsm : (c * d⁻¹) • w ∈ (c * d⁻¹) • (β • H) := Finset.smul_mem_smul_finset hwH
    rwa [smul_coset_eq hH hyH β] at hsm

omit [Fintype G] in
/-- The slices `C_α` are translates of one another. -/
theorem smul_C_subset {A B H : Finset G} (hH : IsSubgroupFinset H)
    (hper : (A ∩ B) * H = A ∩ B)
    (hmax : ∀ z : G, (dysonSmall A B z).Nonempty → (dysonSmall A B z).card < B.card →
        (dysonSmall A B z).card ≤ (dysonSmall A B 1).card)
    {α β dα dβ : G} (hdisj : Disjoint (A ∩ (α • H)) (B ∩ (α • H)))
    (hdα : dα ∈ B ∩ (α • H)) (hdβ : dβ ∈ B ∩ (β • H)) :
    (dα⁻¹ * dβ) • (A ∩ (α • H)) ⊆ A ∩ (β • H) := by
  intro z hz
  obtain ⟨c, hc, rfl⟩ := Finset.mem_smul_finset.1 hz
  have hmem : (c * dα⁻¹) • dβ ∈ A ∩ (β • H) :=
    vitadel hH hper hmax (β := β) hdisj hc hdα (Finset.smul_mem_smul_finset hdβ)
  have heq : (dα⁻¹ * dβ) • c = (c * dα⁻¹) • dβ := by
    simp only [smul_eq_mul]
    simp [mul_comm, mul_left_comm]
  rw [heq]
  exact hmem

omit [Fintype G] in
/-- The slices `C_α` all have the same cardinality. -/
theorem card_C_eq {A B H : Finset G} (hH : IsSubgroupFinset H)
    (hper : (A ∩ B) * H = A ∩ B)
    (hmax : ∀ z : G, (dysonSmall A B z).Nonempty → (dysonSmall A B z).card < B.card →
        (dysonSmall A B z).card ≤ (dysonSmall A B 1).card)
    {α β dα dβ : G} (hdisjα : Disjoint (A ∩ (α • H)) (B ∩ (α • H)))
    (hdisjβ : Disjoint (A ∩ (β • H)) (B ∩ (β • H)))
    (hdα : dα ∈ B ∩ (α • H)) (hdβ : dβ ∈ B ∩ (β • H)) :
    (A ∩ (α • H)).card = (A ∩ (β • H)).card := by
  have h1 := Finset.card_le_card (smul_C_subset hH hper hmax hdisjα hdα hdβ)
  have h2 := Finset.card_le_card (smul_C_subset hH hper hmax hdisjβ hdβ hdα)
  rw [Finset.card_smul_finset] at h1 h2
  omega

omit [Fintype G] in
/-- The slices `C_α` are exact translates of one another. -/
theorem smul_C_eq {A B H : Finset G} (hH : IsSubgroupFinset H)
    (hper : (A ∩ B) * H = A ∩ B)
    (hmax : ∀ z : G, (dysonSmall A B z).Nonempty → (dysonSmall A B z).card < B.card →
        (dysonSmall A B z).card ≤ (dysonSmall A B 1).card)
    {α β dα dβ : G} (hdisjα : Disjoint (A ∩ (α • H)) (B ∩ (α • H)))
    (hdisjβ : Disjoint (A ∩ (β • H)) (B ∩ (β • H)))
    (hdα : dα ∈ B ∩ (α • H)) (hdβ : dβ ∈ B ∩ (β • H)) :
    (dα⁻¹ * dβ) • (A ∩ (α • H)) = A ∩ (β • H) := by
  refine Finset.eq_of_subset_of_card_le (smul_C_subset hH hper hmax hdisjα hdα hdβ) ?_
  rw [Finset.card_smul_finset]
  exact le_of_eq (card_C_eq hH hper hmax hdisjα hdisjβ hdα hdβ).symm

/-- Hence they all have the same stabiliser `K`. -/
theorem mulStab_C_eq {A B H : Finset G} (hH : IsSubgroupFinset H)
    (hper : (A ∩ B) * H = A ∩ B)
    (hmax : ∀ z : G, (dysonSmall A B z).Nonempty → (dysonSmall A B z).card < B.card →
        (dysonSmall A B z).card ≤ (dysonSmall A B 1).card)
    {α β dα dβ : G} (hdisjα : Disjoint (A ∩ (α • H)) (B ∩ (α • H)))
    (hdisjβ : Disjoint (A ∩ (β • H)) (B ∩ (β • H)))
    (hdα : dα ∈ B ∩ (α • H)) (hdβ : dβ ∈ B ∩ (β • H)) :
    mulStab (A ∩ (α • H)) = mulStab (A ∩ (β • H)) := by
  rw [← smul_C_eq hH hper hmax hdisjα hdisjβ hdα hdβ, mulStab_smul]

/-- Each `D_α` lies inside a single `K`-coset. -/
theorem D_sub_smul_mulStab {A B H : Finset G} (hH : IsSubgroupFinset H)
    (hper : (A ∩ B) * H = A ∩ B)
    (hmax : ∀ z : G, (dysonSmall A B z).Nonempty → (dysonSmall A B z).card < B.card →
        (dysonSmall A B z).card ≤ (dysonSmall A B 1).card)
    {α d₀ : G} (hdisj : Disjoint (A ∩ (α • H)) (B ∩ (α • H)))
    (hd₀ : d₀ ∈ B ∩ (α • H)) :
    B ∩ (α • H) ⊆ d₀ • mulStab (A ∩ (α • H)) := by
  intro d hd
  refine mem_smul_finset_iff.2 (mem_mulStab.2 ?_)
  exact smul_C_eq hH hper hmax hdisj hdisj hd₀ hd

omit [Fintype G] in
/-- A `K`-periodic set times a subset of a `K`-coset is a translate of the set. -/
theorem mul_eq_smul_of_periodic {C D K : Finset G} (hCK : C * K = C) {d₀ : G} (hd₀ : d₀ ∈ D)
    (hD : D ⊆ d₀ • K) : C * D = d₀ • C := by
  refine Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨c, hc, d, hd, rfl⟩ := mem_mul.1 hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_smul_finset.1 (hD hd)
    refine Finset.mem_smul_finset.2 ⟨c * k, ?_, ?_⟩
    · rw [← hCK]; exact Finset.mul_mem_mul hc hk
    · simp only [smul_eq_mul]
      rw [mul_comm d₀ (c * k), mul_assoc, mul_comm k d₀]
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_smul_finset.1 hz
    exact mem_mul.2 ⟨c, hc, d₀, hd₀, by rw [smul_eq_mul, mul_comm]⟩

/-- Consequently every element of `C · D` has at least `#D` representations in `A × B`. -/
theorem card_D_le_rep {A B C D : Finset G} (hCA : C ⊆ A) (hDB : D ⊆ B)
    (hCne : C.Nonempty) (hDne : D.Nonempty) (hprod : (C * D).card = C.card)
    {x : G} (hx : x ∈ C * D) : D.card ≤ rep A B x := by
  have h1 := card_add_card_le_rep_add_card_mul hCne hDne hx
  have h2 := rep_mono hCA hDB x
  omega

end GaloisForLFunctions.HTGeometry.AddComb
