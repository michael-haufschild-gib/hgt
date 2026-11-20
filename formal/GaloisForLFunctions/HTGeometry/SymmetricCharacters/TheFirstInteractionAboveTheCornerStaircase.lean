import GaloisForLFunctions.HTGeometry.SymmetricCharacters.StaircasePacking
import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# The first interaction above the corner staircase

Slonim's Lemma 8.3 prices k distinct positive row lengths by the k-step
staircase. Write xᵢ for the extra gap before length i and yⱼ for the
extra rows at length j, indexing lengths from shortest to longest.
The area has two linear excess terms and one mixed term. A nonzero
mixed term costs at least k+2 boxes above the staircase. A unit gap
and a unit row repetition at the same index attain the bound.
-/

namespace GaloisForLFunctions.StaircasePacking
open Finset
noncomputable section

/-- The jth distinct positive row length; index zero has length zero. -/
def cornerLength (x : ℕ → ℕ) (j : ℕ) : ℕ := j+∑ i ∈ Icc 1 j, x i

private theorem length_succ (x : ℕ → ℕ) (j : ℕ) :
    cornerLength x (j+1) = cornerLength x j + 1 + x (j+1) := by
  rw [cornerLength, sum_Icc_succ_top (by omega : 1 ≤ j+1)]
  unfold cornerLength
  omega

theorem cornerLength_strictMono (x : ℕ → ℕ) : StrictMono (cornerLength x) :=
  strictMono_nat_of_lt_succ fun n => by rw [length_succ]; omega

/-- The row multiset in gap and multiplicity coordinates. -/
def cornerRows (x y : ℕ → ℕ) : ℕ → Multiset ℕ
  | 0 => 0
  | j+1 => cornerRows x y j + Multiset.replicate (y (j+1)+1) (cornerLength x (j+1))

private theorem mem_cornerRows (x y : ℕ → ℕ) (k n : ℕ) :
    n ∈ cornerRows x y k ↔ ∃ j ∈ Icc 1 k, cornerLength x j = n := by
  induction k with
  | zero => simp [cornerRows]
  | succ k ih =>
    have hset : Icc 1 (k+1) = insert (k+1) (Icc 1 k) := by
      ext j
      simp only [mem_Icc,mem_insert]
      omega
    simp only [cornerRows,Multiset.mem_add,ih,Multiset.mem_replicate,hset,mem_insert]
    constructor
    · rintro (⟨j,hj,he⟩ | hh)
      · exact ⟨j,Or.inr hj,he⟩
      · exact ⟨_,Or.inl rfl,hh.2.symm⟩
    · rintro ⟨j,hj,he⟩
      rcases hj with rfl|hj
      · exact Or.inr (by simp [he])
      · exact Or.inl ⟨j,hj,he⟩

/-- The coordinates always produce an integer partition. -/
def cornerPartition (k : ℕ) (x y : ℕ → ℕ) : Nat.Partition (cornerRows x y k).sum where
  parts := cornerRows x y k
  parts_sum := rfl
  parts_pos := by
    intro n hn
    obtain ⟨j,hj,rfl⟩ := (mem_cornerRows x y k n).mp hn
    exact (mem_Icc.mp hj).1.trans (Nat.le_add_right j _)

/-- Every one of the k length levels occurs and no two are equal. -/
theorem cornerPartition_distinct (k : ℕ) (x y : ℕ → ℕ) :
    (cornerPartition k x y).parts.toFinset.card = k := by
  have hs : (cornerRows x y k).toFinset = (Icc 1 k).image (cornerLength x) := by
    ext n
    rw [Multiset.mem_toFinset,mem_cornerRows,mem_image]
  change (cornerRows x y k).toFinset.card = k
  rw [hs,card_image_of_injective _ (cornerLength_strictMono x).injective]
  simp [Nat.card_Icc]

private theorem cornerLength_congr {x x' : ℕ → ℕ} {k : ℕ}
    (h : ∀ i ≤ k, x i = x' i) : cornerLength x k = cornerLength x' k := by
  unfold cornerLength
  rw [sum_congr rfl fun i hi => h i (mem_Icc.mp hi).2]

private theorem cornerRows_congr {x x' y y' : ℕ → ℕ} {k : ℕ}
    (hx : ∀ i ≤ k, x i = x' i) (hy : ∀ i ≤ k, y i = y' i) :
    cornerRows x y k = cornerRows x' y' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [cornerRows,cornerRows,ih (fun i hi => hx i (hi.trans (Nat.le_succ _)))
      (fun i hi => hy i (hi.trans (Nat.le_succ _))),hy _ le_rfl,cornerLength_congr hx]

private theorem realize_levels (s : Finset ℕ) (w : ℕ → ℕ) (hs : ∀ a ∈ s, 0 < a)
    (hw : ∀ a ∈ s, 0 < w a) : ∃ x y : ℕ → ℕ,
    cornerRows x y s.card = ∑ a ∈ s, Multiset.replicate (w a) a ∧
    ∀ b : ℕ, 0 < b → (∀ a ∈ s, a < b) → cornerLength x s.card < b := by
  induction s using Finset.induction_on_max with
  | empty => exact ⟨0,0,by simp [cornerRows],by simpa [cornerLength]⟩
  | insert a s hmax ih =>
    have ha : a ∉ s := fun h => (hmax a h).false
    obtain ⟨x,y,he,htop⟩ := ih (fun b hb => hs b (mem_insert_of_mem hb))
      (fun b hb => hw b (mem_insert_of_mem hb))
    let k := s.card
    let x' := Function.update x (k+1) (a-cornerLength x k-1)
    let y' := Function.update y (k+1) (w a-1)
    have hx (i : ℕ) (hi : i ≤ k) : x' i=x i := Function.update_of_ne (by omega) _ _
    have hy (i : ℕ) (hi : i ≤ k) : y' i=y i := Function.update_of_ne (by omega) _ _
    have hbase := htop a (hs a (mem_insert_self a s)) hmax
    have hnew : cornerLength x' (k+1)=a := by
      rw [length_succ,cornerLength_congr hx,show x' (k+1)=_ from Function.update_self ..]
      change cornerLength x k+1+(a-cornerLength x k-1)=a
      change cornerLength x k < a at hbase
      omega
    have hrep : y' (k+1)+1=w a := by
      rw [show y' (k+1)=_ from Function.update_self ..]
      have := hw a (mem_insert_self a s)
      omega
    refine ⟨x',y',?_,?_⟩
    · rw [card_insert_of_notMem ha,cornerRows,cornerRows_congr hx hy,hnew,hrep,he,sum_insert ha,add_comm]
    · intro b _ hb
      rw [card_insert_of_notMem ha,hnew]
      exact hb a (mem_insert_self a s)

/-- Every integer partition is represented, with one index per distinct
positive part. In particular the excess formula applies to every shape. -/
theorem cornerRows_exhaust {n : ℕ} (p : Nat.Partition n) :
    ∃ x y : ℕ → ℕ, cornerRows x y p.parts.toFinset.card = p.parts := by
  obtain ⟨x,y,he,_⟩ := realize_levels p.parts.toFinset (fun a => p.parts.count a)
    (fun _ h => p.parts_pos (Multiset.mem_toFinset.mp h))
    (fun _ h => Multiset.count_pos.mpr (Multiset.mem_toFinset.mp h))
  refine ⟨x,y,he.trans ?_⟩
  apply Multiset.ext.mpr
  intro a
  rw [Multiset.count_sum']
  by_cases ha : a ∈ p.parts
  · simp [Multiset.count_replicate,ha]
  · simp [Multiset.count_replicate,ha,Multiset.count_eq_zero.mpr ha]

private theorem row_le_last {x y : ℕ → ℕ} {k a : ℕ} (ha : a ∈ cornerRows x y k) :
    a ≤ cornerLength x k := by
  obtain ⟨j,hj,rfl⟩ := (mem_cornerRows x y k a).mp ha
  exact (cornerLength_strictMono x).monotone (mem_Icc.mp hj).2

private theorem last_count (x y : ℕ → ℕ) (k : ℕ) :
    (cornerRows x y (k+1)).count (cornerLength x (k+1)) = y (k+1)+1 := by
  have hn : cornerLength x (k+1) ∉ cornerRows x y k := fun h =>
    (not_le_of_gt (cornerLength_strictMono x (Nat.lt_succ_self k))) (row_le_last h)
  rw [cornerRows,Multiset.count_add,Multiset.count_eq_zero.mpr hn,
    Multiset.count_replicate_self,zero_add]

/-- Distinct-part lengths and their multiplicities recover every gap
and every repetition from the partition itself. -/
theorem cornerRows_coordinates {k : ℕ} {x y x' y' : ℕ → ℕ}
    (he : cornerRows x y k = cornerRows x' y' k) :
    ∀ i ∈ Icc 1 k, x i=x' i ∧ y i=y' i := by
  induction k with
  | zero => simp
  | succ k ih =>
    have last (f g : ℕ → ℕ) : cornerLength f (k+1) ∈ cornerRows f g (k+1) :=
      (mem_cornerRows ..).mpr ⟨_,mem_Icc.mpr ⟨Nat.succ_pos _,le_rfl⟩,rfl⟩
    have hlen : cornerLength x (k+1)=cornerLength x' (k+1) := le_antisymm
      (row_le_last (he ▸ last x y)) (row_le_last (he.symm ▸ last x' y'))
    have hcount := last_count x y k
    rw [he,hlen,last_count] at hcount
    have hy : y (k+1)=y' (k+1) := by omega
    have hprev : cornerRows x y k=cornerRows x' y' k := by
      change cornerRows x y k+_ = cornerRows x' y' k+_ at he
      rw [hy,hlen] at he
      exact add_right_cancel he
    have hc := ih hprev
    intro i hi
    by_cases h : i=k+1
    · subst i
      have hb : cornerLength x k=cornerLength x' k := by
        unfold cornerLength
        rw [sum_congr rfl fun j hj => (hc j hj).1]
      rw [length_succ,length_succ,hb] at hlen
      exact ⟨by omega,hy⟩
    · exact hc i (mem_Icc.mpr ⟨(mem_Icc.mp hi).1,by have := (mem_Icc.mp hi).2; omega⟩)

theorem cornerRows_eq_iff_coordinates {k : ℕ} {x y x' y' : ℕ → ℕ} :
    cornerRows x y k=cornerRows x' y' k ↔ ∀ i ∈ Icc 1 k, x i=x' i ∧ y i=y' i := by
  refine ⟨cornerRows_coordinates,?_⟩
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    have hk : cornerRows x y k=cornerRows x' y' k :=
      ih fun i hi => h i (mem_Icc.mpr ⟨(mem_Icc.mp hi).1,(mem_Icc.mp hi).2.trans (Nat.le_succ _)⟩)
    have hlen : cornerLength x (k+1)=cornerLength x' (k+1) := by
      unfold cornerLength
      rw [sum_congr rfl fun j hj => (h j hj).1]
    rw [cornerRows,cornerRows,hk,hlen,
      (h _ (mem_Icc.mpr ⟨Nat.succ_pos _,le_rfl⟩)).2]

/-- Extra area from gaps at distinct length levels. -/
def gapArea (k : ℕ) (x : ℕ → ℕ) := ∑ i ∈ Icc 1 k, (k+1-i)*x i
/-- Extra area from row repetitions at the staircase lengths. -/
def repeatArea (k : ℕ) (y : ℕ → ℕ) := ∑ j ∈ Icc 1 k, j*y j
/-- Extra boxes lying both in a repeated row and in an added column. -/
def mixedArea (k : ℕ) (x y : ℕ → ℕ) := ∑ j ∈ Icc 1 k, y j*(∑ i ∈ Icc 1 j, x i)

private theorem gapArea_succ (k : ℕ) (x : ℕ → ℕ) :
    gapArea (k+1) x = gapArea k x + ∑ i ∈ Icc 1 (k+1), x i := by
  unfold gapArea
  rw [sum_Icc_succ_top (by omega : 1 ≤ k+1),sum_Icc_succ_top (by omega : 1 ≤ k+1) x]
  have he (i) (hi : i ∈ Icc 1 k) : (k+1+1-i)*x i = (k+1-i)*x i+x i := by
    have := (mem_Icc.mp hi).2
    rw [show k+1+1-i=(k+1-i)+1 by omega,add_mul,one_mul]
  rw [sum_congr rfl he,sum_add_distrib,show k+1+1-(k+1)=1 by omega,one_mul,add_assoc]

/-- Exact excess-area decomposition for partitions with k distinct parts. -/
theorem cornerPartition_area (k : ℕ) (x y : ℕ → ℕ) :
    (cornerRows x y k).sum = (k+1).choose 2 + gapArea k x + repeatArea k y + mixedArea k x y := by
  induction k with
  | zero => simp [cornerRows,gapArea,repeatArea,mixedArea]
  | succ k ih =>
    rw [cornerRows,Multiset.sum_add,Multiset.sum_replicate,ih,gapArea_succ,
      Nat.choose_succ_succ,Nat.choose_one_right]
    simp only [repeatArea,mixedArea,sum_Icc_succ_top (by omega : 1 ≤ k+1),cornerLength,nsmul_eq_mul]
    ring

private theorem linear_cost_of_crossing {k i j : ℕ} (x y : ℕ → ℕ)
    (hi : i ∈ Icc 1 j) (hj : j ∈ Icc 1 k) (hx : 0 < x i) (hy : 0 < y j) :
    k+1 ≤ gapArea k x + repeatArea k y := by
  have hik := mem_Icc.mpr ⟨(mem_Icc.mp hi).1,(mem_Icc.mp hi).2.trans (mem_Icc.mp hj).2⟩
  have hg : (k+1-i)*x i ≤ gapArea k x := single_le_sum (fun _ _ => Nat.zero_le _) hik
  have hr : j*y j ≤ repeatArea k y := single_le_sum (fun _ _ => Nat.zero_le _) hj
  have h₁ := Nat.le_mul_of_pos_right (k+1-i) hx
  have h₂ := Nat.le_mul_of_pos_right j hy
  have hij := (mem_Icc.mp hi).2
  have hjk := (mem_Icc.mp hj).2
  omega

/-- Below linear excess k+1, extra columns and extra rows are disjoint. -/
theorem mixedArea_eq_zero_of_small_linear_cost {k : ℕ} (x y : ℕ → ℕ)
    (h : gapArea k x + repeatArea k y ≤ k) : mixedArea k x y = 0 := by
  apply sum_eq_zero
  intro j hj
  by_cases hy : y j=0
  · rw [hy,zero_mul]
  · rw [show (∑ i ∈ Icc 1 j, x i)=0 by
      apply sum_eq_zero
      intro i hi
      by_contra hx
      exact (Nat.not_succ_le_self k) ((linear_cost_of_crossing x y hi hj
        (Nat.pos_of_ne_zero hx) (Nat.pos_of_ne_zero hy)).trans h),mul_zero]

/-- The first mixed correction requires at least k+2 boxes above the
minimal k-corner partition. -/
theorem area_of_mixed_cornerPartition {k : ℕ} (x y : ℕ → ℕ) (h : 0 < mixedArea k x y) :
    (k+1).choose 2 + k+2 ≤ (cornerRows x y k).sum := by
  have hlin : k < gapArea k x+repeatArea k y := lt_of_not_ge fun hle =>
    h.ne' (mixedArea_eq_zero_of_small_linear_cost x y hle)
  rw [cornerPartition_area]
  omega

/-- In the first k excess degrees the linear area equation describes
the exact same partitions as the full area equation. -/
theorem cornerPartition_low_degree {k d : ℕ} (hd : d ≤ k) (x y : ℕ → ℕ) :
    (cornerRows x y k).sum = (k+1).choose 2+d ↔ gapArea k x+repeatArea k y = d := by
  rw [cornerPartition_area]
  constructor
  · intro h
    have hz := mixedArea_eq_zero_of_small_linear_cost x y (by omega : gapArea k x+repeatArea k y ≤ k)
    omega
  · intro h
    rw [mixedArea_eq_zero_of_small_linear_cost x y (h.le.trans hd)]
    omega

private def unitAt (i j : ℕ) : ℕ := if j=i then 1 else 0

/-- Every level attains the first mixed correction by adding one gap and
one repetition there. The actual excess is k+2 at each of these k partitions. -/
theorem first_mixed_cornerPartition {i k : ℕ} (hi : i ∈ Icc 1 k) :
    ∃ x y : ℕ → ℕ, gapArea k x = k+1-i ∧ repeatArea k y = i ∧ mixedArea k x y = 1 ∧
      (cornerRows x y k).sum = (k+1).choose 2+k+2 := by
  let f := unitAt i
  have hg : gapArea k f=k+1-i := by simp [gapArea,f,unitAt,mul_ite,hi]
  have hr : repeatArea k f=i := by simp [repeatArea,f,unitAt,mul_ite,hi]
  have hm : mixedArea k f f=1 := by
    have hii : i ∈ Icc 1 i := mem_Icc.mpr ⟨(mem_Icc.mp hi).1,le_rfl⟩
    simp [mixedArea,f,unitAt,ite_mul,hi,hii]
  refine ⟨f,f,hg,hr,hm,?_⟩
  rw [cornerPartition_area,hg,hr,hm]
  have := (mem_Icc.mp hi).2
  omega

#print axioms cornerPartition_distinct
#print axioms cornerRows_exhaust
#print axioms cornerRows_coordinates
#print axioms cornerPartition_area
#print axioms area_of_mixed_cornerPartition
#print axioms cornerPartition_low_degree
#print axioms first_mixed_cornerPartition
end
end GaloisForLFunctions.StaircasePacking
