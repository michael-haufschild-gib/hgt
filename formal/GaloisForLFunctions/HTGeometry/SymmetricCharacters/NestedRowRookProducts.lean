import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# Nested rows in Waters' rook expansion

Filling nested rows in order leaves exactly the row width minus the number
of earlier rows available. An auxiliary column turns a placement with one
missing row into a full placement. On a staircase with optional diagonal
cells the full count splits into independent binary choices.
-/

namespace GaloisForLFunctions.StaircasePacking
open Finset
noncomputable section
open scoped Classical

/-- A placement with one rook in each of the first n rows. -/
abbrev NestedRowRooks {α : Type*} (U : ℕ → Finset α) (n : ℕ) :=
  {f : Fin n ↪ α // ∀ i : Fin n, f i ∈ U i.val}

private theorem finite_row_rooks {α : Type*} (U : ℕ → Finset α) (n : ℕ) :
    Finite (NestedRowRooks U n) := by
  let code (f : NestedRowRooks U n) (i : Fin n) : U i := ⟨f.val i,f.property i⟩
  apply Finite.of_injective code
  intro f g h
  exact Subtype.ext (Function.Embedding.ext fun i => congrArg Subtype.val (congrFun h i))

private def unusedColumns {α : Type*} (U : ℕ → Finset α) {n : ℕ} (f : NestedRowRooks U n) :=
  U n \ univ.map f.val

/-- The last rook occupies exactly one unused column of the new row. -/
private def lastRookEquiv {α : Type*} (U : ℕ → Finset α) (n : ℕ) :
    NestedRowRooks U (n+1) ≃ (f : NestedRowRooks U n) × ↥(unusedColumns U f) := by
  let old (g : NestedRowRooks U (n+1)) : NestedRowRooks U n :=
    ⟨Fin.Embedding.init g.val,fun i => g.property i.castSucc⟩
  let fresh (g : NestedRowRooks U (n+1)) : unusedColumns U (old g) :=
    ⟨g.val (Fin.last n),mem_sdiff.mpr ⟨g.property _,by
      rintro h
      obtain ⟨i,_,hi⟩ := mem_map.mp h
      exact Fin.castSucc_ne_last i (g.val.injective hi)⟩⟩
  let encode (g : NestedRowRooks U (n+1)) := Sigma.mk (β := fun f => ↥(unusedColumns U f)) (old g) (fresh g)
  have unused (f : NestedRowRooks U n) (x : unusedColumns U f) : x.val ∉ Set.range f.val := by
    rintro ⟨i,hi⟩
    exact (mem_sdiff.mp x.property).2 (mem_map.mpr ⟨i,mem_univ _,hi⟩)
  let append (f : NestedRowRooks U n) (x : unusedColumns U f) : NestedRowRooks U (n+1) := by
    refine ⟨Fin.Embedding.snoc f.val (unused f x),?_⟩
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.Embedding.snoc_last]
      exact (mem_sdiff.mp x.property).1
    · rw [Fin.Embedding.snoc_castSucc]
      exact f.property j
  refine Equiv.ofBijective encode ⟨?_,?_⟩
  · intro g h he
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact congrArg (fun v => (v.2 : α)) he
    · exact congrArg (fun v => v.1.val j) he
  · rintro ⟨f,x⟩
    refine ⟨append f x,?_⟩
    have sigma_ext {s t : (f : NestedRowRooks U n) × ↥(unusedColumns U f)}
        (hf : s.1=t.1) (hx : s.2.val=t.2.val) : s=t := by
      rcases s with ⟨a,⟨y,hy⟩⟩
      rcases t with ⟨b,⟨z,hz⟩⟩
      change a=b at hf
      change y=z at hx
      subst b
      subst z
      rfl
    apply sigma_ext
    · apply Subtype.ext
      exact Fin.Embedding.init_snoc (ha := unused f x)
    · exact Fin.Embedding.snoc_last (ha := unused f x)

/-- Product formula for full placements in arbitrary nested finite rows. -/
theorem card_nestedRowRooks {α : Type*} (U : ℕ → Finset α) (hU : Monotone U) (n : ℕ) :
    Nat.card (NestedRowRooks U n) = ∏ i ∈ range n, ((U i).card-i) := by
  induction n with
  | zero =>
    letI : Unique (NestedRowRooks U 0) := {
      default := ⟨⟨Fin.elim0,fun i => i.elim0⟩,fun i => i.elim0⟩
      uniq := fun f => Subtype.ext (Function.Embedding.ext fun i => i.elim0) }
    rw [Nat.card_unique,prod_range_zero]
  | succ n ih =>
    letI := finite_row_rooks U n
    letI := Fintype.ofFinite (NestedRowRooks U n)
    have hc (f : NestedRowRooks U n) :
        Nat.card ↥(unusedColumns U f) = (U n).card-n := by
      have hs : univ.map f.val ⊆ U n := by
        intro x hx
        obtain ⟨i,_,rfl⟩ := mem_map.mp hx
        exact hU i.isLt.le (f.property i)
      rw [Nat.card_eq_finsetCard,unusedColumns,card_sdiff_of_subset hs,card_map,card_univ,Fintype.card_fin]
    rw [Nat.card_congr (lastRookEquiv U n),Nat.card_sigma,prod_range_succ]
    simp only [hc,sum_const,card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card,ih,Nat.cast_id]

/-- In increasing row order the strict staircase has widths 0,1,… .
D specifies the optional diagonal and e is the number of auxiliary columns. -/
def watersNestedRow (D : Finset ℕ) (e i : ℕ) : Finset ℕ :=
  range (i+e+if i∈D then 1 else 0)

private theorem watersNestedRow_mono (D : Finset ℕ) (e : ℕ) :
    Monotone (watersNestedRow D e) := by
  intro i j hij
  obtain rfl|h := eq_or_lt_of_le hij
  · exact Subset.rfl
  · apply range_mono
    split_ifs <;> omega

/-- Factorial rook product with any number of auxiliary columns.
Every optional diagonal cell increases exactly one linear factor. -/
theorem augmented_waters_product (D : Finset ℕ) (e n : ℕ) :
    Nat.card (NestedRowRooks (watersNestedRow D e) n) =
      ∏ i ∈ range n, (e + if i∈D then 1 else 0) := by
  rw [card_nestedRowRooks _ (watersNestedRow_mono D e)]
  apply prod_congr rfl
  intro i hi
  rw [watersNestedRow,card_range]
  omega

/-- A single auxiliary column gives one binary choice per optional cell. -/
theorem augmented_waters_binary (D : Finset ℕ) (n : ℕ) :
    Nat.card (NestedRowRooks (watersNestedRow D 1) n) = 2^((range n).filter (·∈D)).card := by
  rw [augmented_waters_product]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ,range_add_one]
    by_cases h : n∈D
    · simp [filter_insert,h,ih,pow_succ]
    · simp [filter_insert,h,ih]

/-- With no auxiliary column, a full placement exists exactly on the
complete staircase. There it is unique. -/
theorem full_waters_count (D : Finset ℕ) (n : ℕ) :
    Nat.card (NestedRowRooks (watersNestedRow D 0) n) = if range n ⊆ D then 1 else 0 := by
  rw [augmented_waters_product]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ,range_add_one,ih]
    by_cases h : n∈D <;> by_cases hs : range n ⊆ D <;> simp [h,hs,insert_subset_iff]

/-- An augmented placement in which the auxiliary column is the unique
omitted ordinary row. All other column labels shift down by one. -/
abbrev WatersOmittedRow (D : Finset ℕ) (n : ℕ) :=
  {f : NestedRowRooks (watersNestedRow D 1) n // ∃ i, f.val i=0}

private def noAuxiliaryEquiv (D : Finset ℕ) (n : ℕ) :
    {f : NestedRowRooks (watersNestedRow D 1) n // ¬ ∃ i, f.val i=0} ≃
      NestedRowRooks (watersNestedRow D 0) n where
  toFun f := by
    have hn (i : Fin n) : f.val.val i ≠ 0 := fun h => f.property ⟨i,h⟩
    refine ⟨⟨fun i => f.val.val i-1,fun {i j} he => f.val.val.injective ?_⟩,?_⟩
    · change f.val.val i-1=f.val.val j-1 at he
      have := hn i
      have := hn j
      omega
    · intro i
      have hp := mem_range.mp (f.val.property i)
      have := hn i
      apply mem_range.mpr
      change f.val.val i < i.val+1+(if i.val∈D then 1 else 0) at hp
      change f.val.val i-1 < i.val+0+(if i.val∈D then 1 else 0)
      omega
  invFun f := by
    refine ⟨⟨⟨fun i => f.val i+1,fun {i j} h => f.val.injective (Nat.succ.inj h)⟩,?_⟩,?_⟩
    · intro i
      have hp := mem_range.mp (f.property i)
      change f.val i < i.val+0+(if i.val∈D then 1 else 0) at hp
      apply mem_range.mpr
      change f.val i+1 < i.val+1+(if i.val∈D then 1 else 0)
      omega
    · rintro ⟨i,hi⟩
      exact Nat.succ_ne_zero _ hi
  left_inv := by
    intro f
    apply Subtype.ext
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    change f.val.val i-1+1=f.val.val i
    have hn : f.val.val i ≠ 0 := fun h => f.property ⟨i,h⟩
    omega
  right_inv f := Subtype.ext (Function.Embedding.ext fun _ => Nat.add_sub_cancel ..)

/-- On a fixed board the number of one-vacancy placements depends only
on the number of diagonal cells. A full rim loses one configuration. -/
theorem card_watersOmittedRow (D : Finset ℕ) (n : ℕ) :
    Nat.card (WatersOmittedRow D n) +
      (if range n ⊆ D then 1 else 0) = 2^((range n).filter (·∈D)).card := by
  let A := NestedRowRooks (watersNestedRow D 1) n
  letI := finite_row_rooks (watersNestedRow D 1) n
  letI := Fintype.ofFinite A
  let P (f : A) := ∃ i, f.val i=0
  have hc : Fintype.card {f : A // P f} + Fintype.card {f : A // ¬ P f} = Fintype.card A := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl P)
  simp only [← Nat.card_eq_fintype_card] at hc
  change Nat.card (WatersOmittedRow D n) + Nat.card {f : A // ¬ P f} = Nat.card A at hc
  rw [Nat.card_congr (noAuxiliaryEquiv D n),full_waters_count] at hc
  exact hc.trans (augmented_waters_binary D n)

/-- Summing over all optional rims gives 3^n-1 one-vacancy placements
in the second possible moment of Waters' expansion. -/
theorem waters_second_placement_sum (n : ℕ) :
    (∑ D ∈ (range n).powerset, Nat.card (WatersOmittedRow D n)) + 1 = 3^n := by
  have h (D : Finset ℕ) (hD : D ∈ (range n).powerset) :
      Nat.card (WatersOmittedRow D n) + (if D = range n then 1 else 0) = 2^D.card := by
    have hs := mem_powerset.mp hD
    have he : range n ⊆ D ↔ D=range n := ⟨fun hh => Subset.antisymm hs hh,fun hh => hh ▸ Subset.rfl⟩
    have hf : (range n).filter (·∈D) = D := by
      ext x
      exact ⟨fun hx => (mem_filter.mp hx).2,fun hx => mem_filter.mpr ⟨hs hx,hx⟩⟩
    simpa only [he,hf] using card_watersOmittedRow D n
  have hsum := sum_congr rfl h
  rw [sum_add_distrib] at hsum
  have hbox : range n ∈ (range n).powerset := mem_powerset.mpr Subset.rfl
  have hone : (∑ D ∈ (range n).powerset, if D=range n then 1 else 0 : ℕ)=1 := by simp [hbox]
  rw [hone] at hsum
  rw [hsum]
  simpa only [prod_const,card_range,show (1:ℕ)+2=3 from rfl] using
    (prod_one_add (f := fun _ : ℕ => (2:ℕ)) (range n)).symm

#print axioms waters_second_placement_sum
#print axioms card_nestedRowRooks
#print axioms augmented_waters_product
#print axioms augmented_waters_binary
#print axioms full_waters_count
end
end GaloisForLFunctions.StaircasePacking
