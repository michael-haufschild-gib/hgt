import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.CoordinateArrangementCounts
import GaloisForLFunctions.HTGeometry.ProuhetAlternating
import Mathlib.NumberTheory.Fermat
import Mathlib.Combinatorics.Colex

/-!
# Recovering labelled coordinate patterns from one point count

For alphabet sizes equal to successive Fermat numbers, the binary
place of each stratum records its set of free coordinates. This recovers
the entire face family from one integer and attains the smallest possible
ambient cardinality among all marked alphabets.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
open Finset
open scoped Classical
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- A face is identified by the bit mask of its free coordinates. -/
def faceIndex (e : ι ↪ ℕ) (s : Finset ι) := ∑ i ∈ sᶜ.map e, 2^i

theorem faceIndex_injective (e : ι ↪ ℕ) : Function.Injective (faceIndex e) := by
  intro s t h
  have hh := congrArg (fun n : ℕ => n.bitIndices.toFinset) h
  simpa only [faceIndex,toFinset_bitIndices_sum_two_pow,map_inj,compl_inj_iff] using hh

/-- The alphabet sizes are Fermat numbers. Each free-site choice contributes
a different binary place in the stratum index. -/
abbrev labelledLetter (e : ι ↪ ℕ) (i : ι) := Fin (2^(2^e i)+1)

def labelledCount (e : ι ↪ ℕ) (K : Finset (Finset ι)) :=
  (arrangementWords (fun i => ({0} : Finset (labelledLetter e i))) K).card

theorem labelledCount_eq (e : ι ↪ ℕ) (K : Finset (Finset ι)) :
    labelledCount e K = ∑ j ∈ K.image (faceIndex e), 2^j := by
  rw [labelledCount,card_arrangementWords,sum_image (faceIndex_injective e).injOn]
  refine sum_congr rfl fun s _ => ?_
  simp only [labelledLetter,card_singleton,Fintype.card_fin,Nat.add_sub_cancel,
    prod_ite,prod_const_one,one_mul,faceIndex,sum_map,prod_pow_eq_pow_sum]
  have he : (univ.filter fun i => i ∉ s) = sᶜ := by ext; simp
  rw [he]

/-- Binary digits of one heterogeneous point count exactly identify all labelled faces. -/
theorem labelledCount_decode (e : ι ↪ ℕ) (K : Finset (Finset ι)) :
    (labelledCount e K).bitIndices.toFinset = K.image (faceIndex e) := by
  rw [labelledCount_eq,bitIndices_sum_two_pow_finset,sort_toFinset]

theorem labelledCount_testBit (e : ι ↪ ℕ) (K : Finset (Finset ι)) (s : Finset ι) :
    (labelledCount e K).testBit (faceIndex e s) = true ↔ s ∈ K := by
  rw [← Nat.mem_bitIndices,← List.mem_toFinset,labelledCount_decode]
  constructor
  · intro h
    obtain ⟨t,ht,he⟩ := mem_image.mp h
    exact faceIndex_injective e he ▸ ht
  · exact mem_image_of_mem _

theorem labelledCount_injective (e : ι ↪ ℕ) : Function.Injective (labelledCount e) := by
  intro K L he
  ext s
  rw [← labelledCount_testBit e K,he,labelledCount_testBit]

/-- Any single point count which distinguishes every face family requires an ambient
word set this large. The bound allows arbitrary alphabets and arbitrary marked subsets. -/
theorem word_space_lower_bound {A : ι → Type*} [∀ i, Fintype (A i)] (D : ∀ i, Finset (A i))
    (h : Function.Injective (fun K : Finset (Finset ι) => (arrangementWords D K).card)) :
    2^(2^Fintype.card ι) ≤ Fintype.card (∀ i, A i)+1 := by
  let f (K : Finset (Finset ι)) : Fin (Fintype.card (∀ i, A i)+1) :=
    ⟨(arrangementWords D K).card,Nat.lt_succ_of_le (arrangementWords D K).card_le_univ⟩
  have hi : Function.Injective f := fun K L hh => h (congrArg Fin.val hh)
  simpa only [Fintype.card_finset,Fintype.card_fin] using Fintype.card_le_of_injective f hi

/-- With consecutive coordinate labels, the Fermat product attains the information bound. -/
theorem labelledWordSpace_optimal (n : ℕ) :
    Fintype.card (∀ i : Fin n, labelledLetter Fin.valEmbedding i)+1 = 2^(2^n) := by
  have h : (∏ i : Fin n, Nat.fermatNumber i.val) = Nat.fermatNumber n - 2 := by
    rw [Fin.prod_univ_eq_prod_range Nat.fermatNumber n,Nat.prod_fermatNumber]
  have hp : 0 < 2^(2^n) := by positivity
  rw [Fintype.card_pi]
  simp only [labelledLetter,Fintype.card_fin]
  change (∏ i : Fin n, Nat.fermatNumber i.val)+1 = _
  rw [h]
  unfold Nat.fermatNumber
  omega

/-- No scalar observations are wasted: every possible count between zero
and the size of the optimal word space is realized by exactly one family. -/
def labelledCountEquiv (n : ℕ) :
    Finset (Finset (Fin n)) ≃ Fin (2^(2^n)) := by
  let f (K : Finset (Finset (Fin n))) : Fin (2^(2^n)) :=
    ⟨labelledCount Fin.valEmbedding K, by
      rw [← labelledWordSpace_optimal]
      exact Nat.lt_succ_of_le (arrangementWords _ K).card_le_univ⟩
  have hi : Function.Injective f := fun K L hh => labelledCount_injective _ (congrArg Fin.val hh)
  exact Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hi, by simp⟩)


end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
