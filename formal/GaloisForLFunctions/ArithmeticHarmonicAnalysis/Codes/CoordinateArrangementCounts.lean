import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.DivisibleSymbolOrthogonality
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum

/-!
# Point counts by coordinate pattern

The face-stratum argument of Andrusov, §4.1 (arXiv:2610.16230), works for
different alphabets and different sets of distinguished symbols at each
coordinate. The resulting formula counts Hamming shells and arrangements
with prescribed zero sets in the same ambient word space.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes

open Finset
open scoped Classical
noncomputable section

variable {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, Fintype (A i)]

/-- Coordinates at which the letter belongs to its distinguished subset. -/
def matchSet (D : ∀ i, Finset (A i)) (x : ∀ i, A i) : Finset ι :=
  univ.filter fun i => x i ∈ D i

/-- Words whose coordinate pattern is one of the prescribed faces. -/
def arrangementWords (D : ∀ i, Finset (A i)) (K : Finset (Finset ι)) :
    Finset (∀ i, A i) := univ.filter fun x => matchSet D x ∈ K

/-- A single stratum is a Cartesian box, including its empty factors. -/
theorem matchSet_fiber (D : ∀ i, Finset (A i)) (s : Finset ι) :
    univ.filter (fun x => matchSet D x = s) =
      Fintype.piFinset (fun i => if i ∈ s then D i else (D i)ᶜ) := by
  ext x
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  constructor
  · intro h i
    have hi := Finset.ext_iff.mp h i
    simp only [matchSet, mem_filter, mem_univ, true_and] at hi
    by_cases hs : i ∈ s <;> simp [hs, hi]
  · intro h
    ext i
    have hi := h i
    by_cases hs : i ∈ s <;> simpa [matchSet, hs] using hi

/-- Each admissible pattern contributes the product of its local multiplicities. -/
theorem card_arrangementWords (D : ∀ i, Finset (A i)) (K : Finset (Finset ι)) :
    (arrangementWords D K).card =
      ∑ s ∈ K, ∏ i, if i ∈ s then (D i).card else Fintype.card (A i) - (D i).card := by
  have hm : ((arrangementWords D K : Finset _) : Set _).MapsTo (matchSet D) K :=
    fun _ hx => (mem_filter.mp hx).2
  rw [card_eq_sum_card_fiberwise hm]
  refine sum_congr rfl fun s hs => ?_
  have hf : (arrangementWords D K).filter (fun x => matchSet D x = s) =
      univ.filter (fun x => matchSet D x = s) := by
    ext x
    simp only [arrangementWords, mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    exact fun h => h.symm ▸ hs
  rw [hf, matchSet_fiber, Fintype.card_piFinset]
  exact prod_congr rfl fun i _ => by split_ifs <;> simp_all

variable {F : Type*} [Fintype F]

/-- Moving the distinguished point independently in every coordinate leaves
the face enumerator unchanged. -/
theorem card_pointArrangement (c : ι → F) (K : Finset (Finset ι)) :
    (arrangementWords (fun i => {c i}) K).card =
      ∑ s ∈ K, (Fintype.card F - 1) ^ (Fintype.card ι - s.card) := by
  rw [card_arrangementWords]
  refine sum_congr rfl fun s _ => ?_
  simp only [card_singleton]
  rw [prod_ite]
  simp [← Finset.card_compl, Finset.compl_eq_univ_sdiff]

/-- Selecting one layer of the face lattice gives the Hamming sphere about
an arbitrary word; the layer index counts matches. -/
theorem card_exact_matches (c : ι → F) (k : ℕ) :
    (arrangementWords (fun i => {c i}) (univ.powersetCard k)).card =
      (Fintype.card ι).choose k * (Fintype.card F - 1) ^ (Fintype.card ι - k) := by
  rw [card_pointArrangement]
  calc
    _ = ∑ _s ∈ (univ : Finset ι).powersetCard k,
        (Fintype.card F - 1) ^ (Fintype.card ι - k) := by
      exact sum_congr rfl fun s hs => by rw [(mem_powersetCard.mp hs).2]
    _ = _ := by simp [card_powersetCard]

variable [Field F]

/-- The full ambient code has the binomial weight spectrum, with no
restriction on the size of the field or length of the code. -/
theorem card_words_weight (k : ℕ) :
    (univ.filter fun x : ι → F => weight x = k).card =
      (Fintype.card ι).choose k * (Fintype.card F - 1) ^ k := by
  let D : ι → Finset F := fun _ => ({0} : Finset F)ᶜ
  have hwords : (univ.filter fun x : ι → F => weight x = k) =
      arrangementWords D (univ.powersetCard k) := by
    ext x
    simp [arrangementWords, matchSet, D, weight]
  rw [hwords, card_arrangementWords]
  have hF : Fintype.card F - (Fintype.card F - 1) = 1 := by
    have := Fintype.card_pos (α := F)
    omega
  calc
    _ = ∑ _s ∈ (univ : Finset ι).powersetCard k, (Fintype.card F - 1) ^ k := by
      refine sum_congr rfl fun s hs => ?_
      simp only [D, card_compl, card_singleton, hF]
      rw [prod_ite]
      simp [(mem_powersetCard.mp hs).2]
    _ = _ := by simp [card_powersetCard]

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
