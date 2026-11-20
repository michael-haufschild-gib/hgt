import GaloisForLFunctions.ArithmeticCountingPositivity.AUniformSquarefreeMajority

/-!
# Squarefree pairs at every sufficiently short ordinary lag

Intersect the squarefree sites with a translate before discarding an
initial segment. The enclosing interval gains only the lag in length.
Thus one squarefree surplus pays simultaneously for the boundary loss
and for removing the small indices where logarithmic gaps are large.
-/
noncomputable section
open Finset
namespace GaloisForLFunctions.ArithmeticCountingPositivity

def squarefreeShiftEndpoints (N b J : ℕ) : Finset ℕ :=
  let S := (Icc 1 N).filter Squarefree
  (S ∩ S.image (fun n => n+b)).filter fun m => J ≤ m

theorem mem_squarefree_shift_endpoints {m N b J : ℕ} :
    m ∈ squarefreeShiftEndpoints N b J ↔
      1 ≤ m-b ∧ m≤N ∧ J ≤ m ∧ Squarefree m ∧ Squarefree (m-b) := by
  classical
  constructor
  · intro h
    obtain ⟨hm,hJ⟩ := mem_filter.mp h
    obtain ⟨hS,hI⟩ := mem_inter.mp hm
    obtain ⟨n,hn,he⟩ := mem_image.mp hI
    have hmN := (mem_Icc.mp (mem_filter.mp hS).1).2
    have hn1 := (mem_Icc.mp (mem_filter.mp hn).1).1
    have hd : m-b=n := by omega
    exact ⟨by omega,hmN,hJ,(mem_filter.mp hS).2,by simpa only [hd] using (mem_filter.mp hn).2⟩
  · rintro ⟨hm,hmN,hJ,hs,hs'⟩
    refine mem_filter.mpr ⟨mem_inter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hmN⟩,hs⟩,?_⟩,hJ⟩
    exact mem_image.mpr ⟨m-b,mem_filter.mpr ⟨mem_Icc.mpr ⟨hm,by omega⟩,hs'⟩,by omega⟩

/-- For every N, positive density survives every shift and lower
cutoff whose combined cost is less than N/36. -/
theorem squarefree_shift_endpoints_lower (N b J : ℕ) :
    (N:ℝ)/36-b-J ≤ ((squarefreeShiftEndpoints N b J).card:ℝ) := by
  classical
  let S := (Icc 1 N).filter Squarefree
  let T := S.image (fun n => n+b)
  let P := S ∩ T
  have hT : T.card=S.card := card_image_of_injective S (fun _ _ h => Nat.add_right_cancel h)
  have hsub : S ∪ T ⊆ Icc 1 (N+b) := by
    intro n hn
    rcases mem_union.mp hn with h|h
    · have h' := mem_Icc.mp (mem_filter.mp h).1
      exact mem_Icc.mpr ⟨h'.1,by omega⟩
    · obtain ⟨k,hk,rfl⟩ := mem_image.mp h
      have h' := mem_Icc.mp (mem_filter.mp hk).1
      exact mem_Icc.mpr ⟨by omega,by omega⟩
  have hcard := card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hu := card_union_add_card_inter S T
  rw [hT] at hu
  have hbad : (P.filter fun m => ¬J ≤ m) ⊆ range J :=
    fun m hm => mem_range.mpr (lt_of_not_ge (mem_filter.mp hm).2)
  have hsmall := card_le_card hbad
  rw [card_range] at hsmall
  have hsplit := card_filter_add_card_filter_not (s:=P) (p:=fun m => J ≤ m)
  have hall : 2*S.card ≤ N+b+J+(squarefreeShiftEndpoints N b J).card := by
    change 2*S.card ≤ N+b+J+(P.filter fun m => J ≤ m).card
    change (S ∪ T).card+P.card=S.card+S.card at hu
    omega
  have hol : (2:ℝ)*S.card ≤ N+b+J+((squarefreeShiftEndpoints N b J).card:ℝ) := by exact_mod_cast hall
  have hsf : (37/72:ℝ)*N ≤ (S.card:ℝ) := squarefree_majority_all_cutoffs N
  linarith only [hol,hsf]

#print axioms mem_squarefree_shift_endpoints
#print axioms squarefree_shift_endpoints_lower
end GaloisForLFunctions.ArithmeticCountingPositivity
