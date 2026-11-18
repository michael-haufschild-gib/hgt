import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.SeparatedWordBoxes

/-!
# The size spectrum of separated word families

The coordinate obstruction of Choi–Jang is exact at the level of both
cardinalities. For ternary alphabets, every usable coordinate gives a
choice to at most one side. This gives the entire tradeoff, including the
sharp equal-size threshold in odd dimension.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
open Finset
open scoped Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Cardinalities realized by families differing across the two sides in every coordinate. -/
def separatedSizes (A : ι → Type*) [∀ i, Fintype (A i)] (s t : ℕ) : Prop :=
  ∃ S T : Finset (∀ i, A i), T ⊆ oppositeBox S ∧ S.card = s ∧ T.card = t

/-- Exact joint size region, including empty families and heterogeneous alphabets. -/
theorem separatedSizes_iff (A : ι → Type*) [∀ i, Fintype (A i)] (s t : ℕ) :
    separatedSizes A s t ↔ ∃ a : ι → ℕ, (∀ i, a i ≤ Fintype.card (A i)) ∧
      s ≤ ∏ i, a i ∧ t ≤ ∏ i, (Fintype.card (A i) - a i) := by
  constructor
  · rintro ⟨S,T,hT,rfl,rfl⟩
    let D := fun i => S.image (fun x => x i)
    have hS : S ⊆ Fintype.piFinset D :=
      fun x hx => Fintype.mem_piFinset.mpr fun i => mem_image_of_mem _ hx
    exact ⟨fun i => (D i).card, fun i => (D i).card_le_univ,
      by simpa only [Fintype.card_piFinset] using card_le_card hS,
      by simpa only [card_oppositeBox, D] using card_le_card hT⟩
  · rintro ⟨a,ha,hs,ht⟩
    have hd (i : ι) : ∃ D : Finset (A i), D ⊆ univ ∧ D.card = a i :=
      exists_subset_card_eq (by simpa using ha i)
    choose D _ hD using hd
    obtain ⟨S,hS,hs'⟩ := exists_subset_card_eq (s := Fintype.piFinset D)
      (n := s) (by simpa [Fintype.card_piFinset,hD] using hs)
    obtain ⟨T,hT,ht'⟩ := exists_subset_card_eq (s := Fintype.piFinset (fun i => (D i)ᶜ))
      (n := t) (by simpa [Fintype.card_piFinset,card_compl,hD] using ht)
    refine ⟨S,T,?_,hs',ht'⟩
    intro y hy
    apply (mem_oppositeBox S y).mpr
    intro x hx i he
    exact (mem_compl.mp (Fintype.mem_piFinset.mp (hT hy) i))
      (he ▸ Fintype.mem_piFinset.mp (hS hx) i)

private theorem ternary_split (D : Finset ι) :
    (∏ i, if i ∈ D then 2 else (1:ℕ)) = 2^D.card ∧
    (∏ i, 3-(if i ∈ D then 2 else (1:ℕ))) = 2^(Fintype.card ι - D.card) := by
  have hc : (univ.filter fun i => i ∉ D) = Dᶜ := by ext; simp
  constructor
  · simp [prod_ite]
  · have he (i : ι) : 3-(if i ∈ D then 2 else (1:ℕ)) = if i ∈ D then 1 else 2 := by
      split_ifs <;> rfl
    simp_rw [he]
    simp [prod_ite, hc,card_compl]

/-- In a positive-size ternary pair, each coordinate can double at most one
family. Every division of the coordinates is attainable. -/
theorem ternary_size_tradeoff (s t : ℕ) :
    separatedSizes (fun _ : ι => Fin 3) (s+1) (t+1) ↔
      ∃ k ≤ Fintype.card ι, s+1 ≤ 2^k ∧ t+1 ≤ 2^(Fintype.card ι-k) := by
  rw [separatedSizes_iff]
  simp only [Fintype.card_fin]
  constructor
  · rintro ⟨a,ha,hs,ht⟩
    let D := univ.filter fun i => a i = 2
    have he (i : ι) : a i = if i ∈ D then 2 else 1 := by
      have h₀ : a i ≠ 0 := by
        intro hz
        have h := prod_eq_zero (mem_univ i) hz
        omega
      have h₃ : 3-a i ≠ 0 := by
        intro hz
        have h := prod_eq_zero (f := fun j => 3-a j) (mem_univ i) hz
        omega
      have hi := ha i
      by_cases h : a i = 2
      · simp [D,h]
      · simp [D,h]
        omega
    have hf : a = fun i => if i ∈ D then 2 else 1 := funext he
    rw [hf, (ternary_split D).1] at hs
    rw [hf, (ternary_split D).2] at ht
    exact ⟨D.card,D.card_le_univ,hs,ht⟩
  · rintro ⟨k,hk,hs,ht⟩
    obtain ⟨D,_,hD⟩ := exists_subset_card_eq (s := (univ : Finset ι)) (n := k) (by simpa using hk)
    refine ⟨fun i => if i ∈ D then 2 else 1, fun i => by split_ifs <;> omega, ?_, ?_⟩
    · simpa only [(ternary_split D).1,hD] using hs
    · simpa only [(ternary_split D).2,hD] using ht

/-- The equal-size threshold in dimension `d` is exactly `2^(d/2)` with
integer division, including odd dimensions where rounding the volume
bound can overestimate the answer. -/
theorem ternary_equal_sizes (s : ℕ) :
    separatedSizes (fun _ : ι => Fin 3) (s+1) (s+1) ↔ s+1 ≤ 2^(Fintype.card ι/2) := by
  rw [ternary_size_tradeoff]
  constructor
  · rintro ⟨k,hk,h₁,h₂⟩
    by_cases h : k ≤ Fintype.card ι/2
    · exact h₁.trans (Nat.pow_le_pow_right (by omega) h)
    · exact h₂.trans (Nat.pow_le_pow_right (by omega) (by omega))
  · intro h
    exact ⟨_, Nat.div_le_self _ 2, h, h.trans (Nat.pow_le_pow_right (by omega) (by omega))⟩

#print axioms separatedSizes_iff
#print axioms ternary_size_tradeoff
#print axioms ternary_equal_sizes

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
