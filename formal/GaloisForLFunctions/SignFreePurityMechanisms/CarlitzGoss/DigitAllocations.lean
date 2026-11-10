import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.ContentPartitions
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.CastCard

/-!
# Realizing content partitions by digit occurrences

In a finite set of coloured tokens, any prescribed number no larger than the
available count can be selected independently in each colour. Consequently,
every admissible partition of digit-content vectors is realized by a partition
of the individual digit occurrences.

A divisible prefix of k nonempty parts, followed by one nonempty unrestricted
part, exists exactly when all inverse-content coordinates exceed k. No digit
counts are lost when passing from the vector criterion to finite subsets.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

/-- Selecting the requested number of tokens independently in each colour class. -/
theorem exists_subset_fibreCard {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (S : Finset α) (colour : α → β) (v : β → ℕ)
    (hv : ∀ h, v h ≤ (S.filter fun x => colour x = h).card) :
    ∃ T ⊆ S, ∀ h, (T.filter fun x => colour x = h).card = v h := by
  classical
  have hex (h : β) := exists_subset_card_eq (hv h)
  choose t ht hc using hex
  let T := univ.biUnion t
  have hsub : T ⊆ S := by
    intro x hx
    obtain ⟨h, _, hxh⟩ := mem_biUnion.mp hx
    exact (mem_filter.mp (ht h hxh)).1
  refine ⟨T, hsub, ?_⟩
  intro h
  have he : T.filter (fun x => colour x = h) = t h := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxT, hxh⟩ := mem_filter.mp hx
      obtain ⟨j, _, hxj⟩ := mem_biUnion.mp hxT
      have hj : colour x = j := (mem_filter.mp (ht j hxj)).2
      have hjh : j = h := hj.symm.trans hxh
      simpa only [hjh] using hxj
    · intro hx
      refine mem_filter.mpr ⟨mem_biUnion.mpr ⟨h, mem_univ h, hx⟩, ?_⟩
      exact (mem_filter.mp (ht h hx)).2
  rw [he, hc h]

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
variable {s : ℕ} {α : Type*} [DecidableEq α]

/-- Residue-class counts of a finite collection of digit tokens. -/
def tokenContent (colour : α → ZMod s) (S : Finset α) (h : ZMod s) : ℤ :=
  (S.filter fun x => colour x = h).card

omit [DecidableEq α] in
theorem tokenContent_nonneg (colour : α → ZMod s) (S : Finset α) (h : ZMod s) :
    0 ≤ tokenContent colour S h := Nat.cast_nonneg _

omit [DecidableEq α] in
theorem positive_tokenContent_iff (colour : α → ZMod s) (S : Finset α) :
    PositiveContent (tokenContent colour S) ↔ S.Nonempty := by
  constructor
  · rintro ⟨_, h, hh⟩
    dsimp only [tokenContent] at hh
    have hp : 0 < (S.filter fun x => colour x = h).card := by exact_mod_cast hh
    obtain ⟨x, hx⟩ := card_pos.mp hp
    exact ⟨x, (mem_filter.mp hx).1⟩
  · rintro ⟨x, hx⟩
    refine ⟨tokenContent_nonneg colour S, colour x, ?_⟩
    have hp : 0 < (S.filter fun y => colour y = colour x).card :=
      card_pos.mpr ⟨x, mem_filter.mpr ⟨hx, rfl⟩⟩
    dsimp only [tokenContent]
    exact_mod_cast hp

omit [DecidableEq α] in
theorem tokenContent_subset (colour : α → ZMod s) {S T : Finset α} (hT : T ⊆ S)
    (h : ZMod s) : tokenContent colour T h ≤ tokenContent colour S h := by
  apply Int.ofNat_le.mpr
  apply card_le_card
  intro x hx
  exact mem_filter.mpr ⟨hT (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩

variable [NeZero s]

theorem exists_subset_tokenContent (colour : α → ZMod s) (S : Finset α) (v : ZMod s → ℤ)
    (hv0 : ∀ h, 0 ≤ v h) (hv : ∀ h, v h ≤ tokenContent colour S h) :
    ∃ T ⊆ S, tokenContent colour T = v := by
  have hn (h : ZMod s) : (v h).toNat ≤ (S.filter fun x => colour x = h).card := by
    have hh := hv h
    have hh0 := hv0 h
    dsimp only [tokenContent] at hh
    omega
  obtain ⟨T, hT, hc⟩ := exists_subset_fibreCard S colour (fun h => (v h).toNat) hn
  refine ⟨T, hT, ?_⟩
  funext h
  dsimp only [tokenContent]
  rw [hc h]
  have hh := hv0 h
  omega

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
variable {s : ℕ} {α : Type*} [DecidableEq α]

theorem tokenContent_sdiff (colour : α → ZMod s) {S T : Finset α} (hT : T ⊆ S) :
    tokenContent colour (S \ T) = tokenContent colour S - tokenContent colour T := by
  funext h
  dsimp only [tokenContent, Pi.sub_apply]
  have hf : (S \ T).filter (fun x => colour x = h) =
      (S.filter fun x => colour x = h) \ (T.filter fun x => colour x = h) := by
    ext x
    simp only [mem_filter, mem_sdiff]
    tauto
  rw [hf]
  apply cast_card_sdiff
  intro x hx
  exact mem_filter.mpr ⟨hT (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩

/-- A finite digit collection split into positive divisible parts and one nonempty last part. -/
inductive TokenPrefix (p : ℕ) (colour : α → ZMod s) : ℕ → Finset α → Prop
  | zero {S : Finset α} : S.Nonempty → TokenPrefix p colour 0 S
  | cons {k : ℕ} {S T : Finset α} : T ⊆ S → DivisibleContent p (tokenContent colour T) →
      TokenPrefix p colour k (S \ T) → TokenPrefix p colour (k + 1) S

variable [NeZero s]

/-- Every admissible content partition is realized by an actual partition of digit tokens. -/
theorem tokenPrefix_iff_contentPrefix (p k : ℕ) (colour : α → ZMod s) (S : Finset α) :
    TokenPrefix p colour k S ↔ HasContentPrefix p k (tokenContent colour S) := by
  constructor
  · intro hP
    induction hP with
    | @zero S hS =>
      exact ⟨0, tokenContent colour S, DivisiblePartition.nil,
        (positive_tokenContent_iff colour S).mpr hS, (zero_add _).symm⟩
    | @cons k S T hT hJ hP ih =>
      obtain ⟨v, w, hV, hw, he⟩ := ih
      refine ⟨tokenContent colour T + v, w, DivisiblePartition.cons hJ hV, hw, ?_⟩
      have hd := tokenContent_sdiff colour hT
      rw [he] at hd
      funext h
      have hh := congrFun hd h
      dsimp only [Pi.add_apply, Pi.sub_apply] at hh ⊢
      linarith only [hh]
  · rintro ⟨v, w, hV, hw, he⟩
    induction hV generalizing S with
    | nil =>
      apply TokenPrefix.zero
      apply (positive_tokenContent_iff colour S).mp
      simpa only [he, zero_add] using hw
    | @cons k v₀ v hJ hV ih =>
      have hvle (h : ZMod s) : v₀ h ≤ tokenContent colour S h := by
        have hh := congrFun he h
        have hv := hV.nonneg h
        have hw0 := hw.1 h
        dsimp only [Pi.add_apply] at hh
        omega
      obtain ⟨T, hT, ht⟩ := exists_subset_tokenContent colour S v₀ hJ.1.1 hvle
      apply TokenPrefix.cons hT
      · simpa only [ht] using hJ
      · apply ih
        have hd := tokenContent_sdiff colour hT
        rw [ht, he] at hd
        funext h
        have hh := congrFun hd h
        dsimp only [Pi.add_apply, Pi.sub_apply] at hh ⊢
        linarith only [hh]

/-- The exact inverse-content threshold for a finite collection of digit tokens. -/
theorem tokenPrefix_iff_inverseContent (p k : ℕ) (hp : 2 ≤ p)
    (colour : α → ZMod s) (S : Finset α) :
    TokenPrefix p colour k S ↔
      ∀ h, (k : ℚ) < inverseContent (p : ℚ) (fun j => (tokenContent colour S j : ℚ)) h := by
  rw [tokenPrefix_iff_contentPrefix, hasContentPrefix_iff p k hp]
  exact and_iff_right (tokenContent_nonneg colour S)

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.tokenPrefix_iff_inverseContent
