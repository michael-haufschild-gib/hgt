import GaloisForLFunctions.HTGeometry.SymmetricCharacters.TheFirstInteractionAboveTheCornerStaircase
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Stable partitions above the corner staircase

A partition with k distinct parts and d boxes above the minimal
staircase is equivalent, for d ≤ k, to an ordered pair of partitions
of total size d. Horizontal extras of length a enlarge gap k+1−a.
Vertical extras of length b repeat row level b. No two extras of
opposite colors can cross in this degree range.
-/

namespace GaloisForLFunctions.StaircasePacking
open Finset
noncomputable section

/-- Partitions of a given excess area with exactly k distinct parts. -/
abbrev cornerShell (k d : ℕ) :=
  {p : Nat.Partition ((k+1).choose 2+d) // p.parts.toFinset.card=k}

/-- An ordered pair of positive-part partitions of total size d. -/
abbrev cornerBipartitions (d : ℕ) := {p : Multiset ℕ × Multiset ℕ //
  (∀ a ∈ p.1, 0 < a) ∧ (∀ b ∈ p.2, 0 < b) ∧ p.1.sum+p.2.sum=d}

private def bundle (k : ℕ) (f : ℕ → ℕ) : Multiset ℕ :=
  ∑ i ∈ Icc 1 k, Multiset.replicate (f i) i

private theorem bundle_count (k a : ℕ) (f : ℕ → ℕ) :
    (bundle k f).count a = if a ∈ Icc 1 k then f a else 0 := by
  classical
  simp [bundle,Multiset.count_sum',Multiset.count_replicate]

private theorem bundle_pos (k : ℕ) (f : ℕ → ℕ) {a : ℕ} (ha : a ∈ bundle k f) : 0<a := by
  have hp := Multiset.count_pos.mpr ha
  rw [bundle_count] at hp
  split at hp
  · exact (mem_Icc.mp ‹a ∈ Icc 1 k›).1
  · exact False.elim (Nat.lt_irrefl _ hp)

private theorem sum_bundle (k : ℕ) (f : ℕ → ℕ) :
    (bundle k f).sum = ∑ i ∈ Icc 1 k, i*f i := by
  have aux (s : Finset ℕ) : (∑ i ∈ s, Multiset.replicate (f i) i).sum=∑ i ∈ s, i*f i := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [sum_insert ha,ih,Multiset.sum_replicate,nsmul_eq_mul,Nat.mul_comm]
  exact aux _

private theorem sum_reflect (k : ℕ) (f : ℕ → ℕ) :
    (∑ i ∈ Icc 1 k, f (k+1-i)) = ∑ i ∈ Icc 1 k, f i := by
  have hm (i) (hi : i ∈ Icc 1 k) : k+1-i ∈ Icc 1 k := by
    obtain ⟨h₁,h₂⟩ := mem_Icc.mp hi
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  refine sum_nbij' (fun i => k+1-i) (fun i => k+1-i) hm hm ?_ ?_ (fun _ _ => rfl)
  all_goals intro i hi; have := (mem_Icc.mp hi).2; omega

private theorem gap_reflect (k : ℕ) (f : ℕ → ℕ) :
    gapArea k (fun i => f (k+1-i)) = ∑ i ∈ Icc 1 k, i*f i :=
  sum_reflect k (fun i => i*f i)

private theorem bundle_reconstruct {k : ℕ} (s : Multiset ℕ)
    (hs : ∀ a ∈ s, a ∈ Icc 1 k) : bundle k (fun i => s.count i)=s := by
  apply Multiset.ext.mpr
  intro a
  rw [bundle_count]
  split
  · rfl
  · exact (Multiset.count_eq_zero.mpr fun ha => ‹a ∉ Icc 1 k› (hs a ha)).symm

private theorem colors_in_range {k d : ℕ} (hd : d ≤ k) (p : cornerBipartitions d) :
    (∀ a ∈ p.1.1, a ∈ Icc 1 k) ∧ ∀ b ∈ p.1.2, b ∈ Icc 1 k := by
  have hmass := p.2.2.2
  constructor
  · intro a ha
    exact mem_Icc.mpr ⟨p.2.1 a ha,by have := Multiset.le_sum_of_mem ha; omega⟩
  · intro b hb
    exact mem_Icc.mpr ⟨p.2.2.1 b hb,by have := Multiset.le_sum_of_mem hb; omega⟩

private theorem color_area {k d : ℕ} (hd : d ≤ k) (p : cornerBipartitions d) :
    gapArea k (fun i => p.1.1.count (k+1-i)) +
      repeatArea k (fun i => p.1.2.count i) = d := by
  obtain ⟨ha,hb⟩ := colors_in_range hd p
  rw [gap_reflect k (fun i => p.1.1.count i),repeatArea,
    ←sum_bundle k (fun i => p.1.1.count i),←sum_bundle k (fun i => p.1.2.count i),
    bundle_reconstruct _ ha,bundle_reconstruct _ hb,p.2.2.2]

private def colorsToCorner {k d : ℕ} (hd : d ≤ k) (p : cornerBipartitions d) : cornerShell k d :=
  let x := fun i => p.1.1.count (k+1-i)
  let y := fun i => p.1.2.count i
  ⟨⟨cornerRows x y k,(cornerPartition k x y).parts_pos,
    (cornerPartition_low_degree hd x y).mpr (color_area hd p)⟩,cornerPartition_distinct k x y⟩

private theorem colorsToCorner_injective {k d : ℕ} (hd : d ≤ k) :
    Function.Injective (colorsToCorner hd) := by
  intro p q he
  have hh := congrArg (fun z : cornerShell k d => z.1.parts) he
  change cornerRows (fun i => p.1.1.count (k+1-i)) (fun i => p.1.2.count i) k =
    cornerRows (fun i => q.1.1.count (k+1-i)) (fun i => q.1.2.count i) k at hh
  have h := cornerRows_coordinates hh
  have hp := colors_in_range hd p
  have hq := colors_in_range hd q
  apply Subtype.ext
  apply Prod.ext
  · apply Multiset.ext.mpr
    intro a
    by_cases ha : a ∈ Icc 1 k
    · obtain ⟨h₁,h₂⟩ := mem_Icc.mp ha
      have hr : k+1-a ∈ Icc 1 k := mem_Icc.mpr ⟨by omega,by omega⟩
      have hh := (h (k+1-a) hr).1
      simpa only [show k+1-(k+1-a)=a by omega] using hh
    · rw [Multiset.count_eq_zero.mpr (fun hm => ha (hp.1 _ hm)),
        Multiset.count_eq_zero.mpr (fun hm => ha (hq.1 _ hm))]
  · apply Multiset.ext.mpr
    intro b
    by_cases hb : b ∈ Icc 1 k
    · exact (h b hb).2
    · rw [Multiset.count_eq_zero.mpr (fun hm => hb (hp.2 _ hm)),
        Multiset.count_eq_zero.mpr (fun hm => hb (hq.2 _ hm))]

private theorem colorsToCorner_surjective {k d : ℕ} (hd : d ≤ k) :
    Function.Surjective (colorsToCorner hd) := by
  intro p
  obtain ⟨x,y,he⟩ := cornerRows_exhaust p.1
  rw [p.2] at he
  have ha := (cornerPartition_low_degree hd x y).mp (by rw [he,p.1.parts_sum])
  let A := bundle k (fun i => x (k+1-i))
  let B := bundle k y
  have hrefl : gapArea k (fun i => x (k+1-(k+1-i))) = gapArea k x := by
    unfold gapArea
    apply sum_congr rfl
    intro i hi
    have := (mem_Icc.mp hi).2
    dsimp only
    rw [show k+1-(k+1-i)=i by omega]
  have hm : A.sum+B.sum=d := by
    rw [show A.sum=_ from sum_bundle ..,show B.sum=_ from sum_bundle ..,
      ←gap_reflect,hrefl]
    exact ha
  let c : cornerBipartitions d := ⟨(A,B),fun _ h => bundle_pos _ _ h,fun _ h => bundle_pos _ _ h,hm⟩
  refine ⟨c,Subtype.ext (Nat.Partition.ext ?_)⟩
  refine Eq.trans ?_ he
  apply cornerRows_eq_iff_coordinates.mpr
  intro i hi
  obtain ⟨h₁,h₂⟩ := mem_Icc.mp hi
  have hr : k+1-i ∈ Icc 1 k := mem_Icc.mpr ⟨by omega,by omega⟩
  change A.count (k+1-i)=x i ∧ B.count i=y i
  simp only [A,B,bundle_count,if_pos hr,if_pos hi,show k+1-(k+1-i)=i by omega,and_self]

/-- All stable excess degrees are indexed by two ordinary partitions
of total size d, independently of the number k of distinct part sizes. -/
def stableCornerShellEquiv {k d : ℕ} (hd : d ≤ k) : cornerBipartitions d ≃ cornerShell k d :=
  Equiv.ofBijective _ ⟨colorsToCorner_injective hd,colorsToCorner_surjective hd⟩

/-- The exact shell count stabilizes as soon as the corner count reaches
the excess. The equivalence also matches individual shapes across ranks. -/
def stableCornerShellChange {k l d : ℕ} (hk : d ≤ k) (hl : d ≤ l) :
    cornerShell k d ≃ cornerShell l d :=
  (stableCornerShellEquiv hk).symm.trans (stableCornerShellEquiv hl)

/-- Splitting the total size according to the first color identifies a
bipartition with two ordinary partitions of complementary sizes. -/
def cornerBipartitionsBySize (d : ℕ) : cornerBipartitions d ≃
    (Σ i : Fin (d+1), Nat.Partition i.val × Nat.Partition (d-i.val)) where
  toFun p :=
    let h := p.2.2.2
    ⟨⟨p.1.1.sum,by omega⟩,
      ⟨p.1.1,fun hmem => p.2.1 _ hmem,rfl⟩,
      ⟨p.1.2,fun hmem => p.2.2.1 _ hmem,by dsimp; omega⟩⟩
  invFun q := ⟨(q.2.1.parts,q.2.2.parts),fun _ h => q.2.1.parts_pos h,fun _ h => q.2.2.parts_pos h,by
    rw [q.2.1.parts_sum,q.2.2.parts_sum]
    have := q.1.isLt
    omega⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨i,hi⟩,⟨⟨s,hs,hsi⟩,⟨t,ht,hst⟩⟩⟩
    change s.sum = i at hsi
    subst i
    rfl

/-- The exact shell size in excess degree d is the convolution of the
ordinary partition numbers; the corner count drops out for d ≤ k. -/
theorem stableCornerShell_card {k d : ℕ} (hd : d ≤ k) :
    Nat.card (cornerShell k d) =
      ∑ i : Fin (d+1), Nat.card (Nat.Partition i.val) * Nat.card (Nat.Partition (d-i.val)) := by
  rw [Nat.card_congr ((stableCornerShellEquiv hd).symm.trans (cornerBipartitionsBySize d))]
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.card_prod]

end
end GaloisForLFunctions.StaircasePacking
