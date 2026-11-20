import GaloisForLFunctions.HTGeometry.SymmetricCharacters.WatersRookSupport
import GaloisForLFunctions.HTGeometry.SymmetricCharacters.NestedRowRookProducts

/-!
# The second rook coefficient of the KMK moments

The cells on the optional rim are indexed by column. Reversing the rows
identifies each contributing Young diagram with a nested-row board. A
rook-free row fills the auxiliary column, giving a bijection between
actual placements and the one-vacancy assignments.
-/

namespace GaloisForLFunctions.StaircasePacking
open Finset
noncomputable section
open scoped Classical

/-- A physical rook placement on the cell set of a Young diagram. -/
abbrev BoardPlacement (B : Finset (ℕ×ℕ)) (g : ℕ) :=
  {R : Finset (ℕ×ℕ) // R ⊆ B ∧ R.card=g ∧
    Set.InjOn Prod.fst (R : Set (ℕ×ℕ)) ∧ Set.InjOn Prod.snd (R : Set (ℕ×ℕ))}

/-- The board at the next moment with diagonal cells indexed by D. -/
def watersRimBoard (g : ℕ) (D : Finset ℕ) : Finset (ℕ×ℕ) :=
  (rookStaircase g).cells ∪ D.image (fun j => (g-j,j))

private theorem rim_row_bound {g : ℕ} {D : Finset ℕ}
    {p : ℕ×ℕ} (hp : p∈watersRimBoard g D) : p.1≤g := by
  rcases mem_union.mp hp with h | h
  · have := mem_rookStaircase.mp h
    omega
  · obtain ⟨j,_,rfl⟩ := mem_image.mp h
    exact Nat.sub_le ..

private theorem rim_row_cells {g : ℕ} {D : Finset ℕ} (hD : D ⊆ range (g+1))
    (i : Fin (g+1)) (y : ℕ) :
    (g-i.val,y)∈watersRimBoard g D ↔ y∈watersNestedRow D 0 i := by
  have hi := i.isLt
  simp only [watersRimBoard,mem_union,mem_image,watersNestedRow,mem_range,Nat.add_zero]
  constructor
  · rintro (h|⟨j,hj,he⟩)
    · have hl := mem_rookStaircase.mp h
      change g-i.val+y<g at hl
      split_ifs <;> omega
    · have h₁ := congrArg Prod.fst he
      have h₂ := congrArg Prod.snd he
      change g-j=g-i.val at h₁
      change j=y at h₂
      have hj' := mem_range.mp (hD hj)
      have hij : j=i.val := by omega
      rw [← hij,if_pos hj]
      omega
  · intro h
    by_cases hl : y < i.val
    · exact Or.inl (mem_rookStaircase.mpr (by dsimp; omega))
    · right
      split_ifs at h with hd
      · exact ⟨i.val,hd,Prod.ext rfl (by dsimp; omega)⟩
      · omega

private def physicalRooks {g : ℕ} {D : Finset ℕ} (f : WatersOmittedRow D (g+1)) : Finset (ℕ×ℕ) :=
  (univ.filter fun i : Fin (g+1) => f.val.val i≠0).image
    (fun i => (g-i.val,f.val.val i-1))

private theorem mem_physicalRooks {g : ℕ} {D : Finset ℕ} (f : WatersOmittedRow D (g+1))
    (i : Fin (g+1)) (y : ℕ) : (g-i.val,y)∈physicalRooks f ↔ f.val.val i=y+1 := by
  simp only [physicalRooks,mem_image,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨j,hj,he⟩
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    change g-j.val=g-i.val at h₁
    change f.val.val j-1=y at h₂
    have hi := i.isLt
    have hj' := j.isLt
    have hji : j=i := Fin.ext (by omega)
    subst j
    omega
  · intro he
    exact ⟨i,by omega,Prod.ext rfl (by dsimp; omega)⟩

private def decodeRimRooks {g : ℕ} {D : Finset ℕ} (hD : D ⊆ range (g+1))
    (f : WatersOmittedRow D (g+1)) : BoardPlacement (watersRimBoard g D) g := by
  let E := univ.filter fun i : Fin (g+1) => f.val.val i≠0
  let cell (i : Fin (g+1)) := (g-i.val,f.val.val i-1)
  have hf : Function.Injective (fun i : Fin (g+1) => g-i.val) := by
    intro i j he
    change g-i.val = g-j.val at he
    have := i.isLt
    have := j.isLt
    exact Fin.ext (by omega)
  refine ⟨physicalRooks f,?_,?_,?_,?_⟩
  · intro p hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    apply (rim_row_cells hD i _).mpr
    have hb := mem_range.mp (f.val.property i)
    have hpos := (mem_filter.mp hi).2
    change f.val.val i < i.val+1+(if i.val∈D then 1 else 0) at hb
    apply mem_range.mpr
    omega
  · obtain ⟨j,hj⟩ := f.property
    have he : E = univ.erase j := by
      ext i
      simp only [E,mem_filter,mem_univ,true_and,mem_erase,and_true]
      exact not_congr ⟨fun he => f.val.val.injective (he.trans hj.symm),fun he => he ▸ hj⟩
    change (E.image cell).card=g
    rw [card_image_of_injective _ (fun i j h => hf (congrArg Prod.fst h)),he,card_erase_of_mem (mem_univ _),
      card_univ,Fintype.card_fin]
    omega
  · intro a ha b hb he
    obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := mem_image.mp hb
    exact congrArg cell (hf he)
  · intro a ha b hb he
    obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hb
    have hi' := (mem_filter.mp hi).2
    have hj' := (mem_filter.mp hj).2
    change f.val.val i-1=f.val.val j-1 at he
    exact congrArg cell (f.val.val.injective (by omega))

private theorem decodeRimRooks_injective {g : ℕ} {D : Finset ℕ} (hD : D ⊆ range (g+1)) :
    Function.Injective (decodeRimRooks hD) := by
  intro f h eq
  have hs : physicalRooks f = physicalRooks h := congrArg Subtype.val eq
  apply Subtype.ext
  apply Subtype.ext
  apply Function.Embedding.ext
  intro i
  have iff_y (y : ℕ) : f.val.val i=y+1 ↔ h.val.val i=y+1 := by rw [← mem_physicalRooks,hs,mem_physicalRooks]
  by_cases hz : f.val.val i=0
  · by_contra ne
    have hp : h.val.val i=h.val.val i-1+1 := by omega
    have := (iff_y _).mpr hp
    omega
  · have hp : f.val.val i=f.val.val i-1+1 := by omega
    have := (iff_y _).mp hp
    omega

private theorem decodeRimRooks_surjective {g : ℕ} {D : Finset ℕ} (hD : D ⊆ range (g+1)) :
    Function.Surjective (decodeRimRooks hD) := by
  intro R
  let occ (i : Fin (g+1)) := ∃ j, (g-i.val,j)∈R.val
  let O := univ.filter occ
  let row (i : Fin (g+1)) := g-i.val
  have hr : Function.Injective row := by
    intro i j he
    change g-i.val=g-j.val at he
    have := i.isLt
    have := j.isLt
    exact Fin.ext (by omega)
  have hrow : O.image row = R.val.image Prod.fst := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
      obtain ⟨j,hj⟩ := (mem_filter.mp hi).2
      exact mem_image.mpr ⟨(g-i.val,j),hj,rfl⟩
    · intro hx
      obtain ⟨⟨a,b⟩,hp,rfl⟩ := mem_image.mp hx
      have ha : a≤g := rim_row_bound (R.property.1 hp)
      let i : Fin (g+1) := ⟨g-a,by omega⟩
      have hi : g-i.val=a := by dsimp [i]; omega
      exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,b,hi.symm ▸ hp⟩,hi⟩
  have hcount := congrArg Finset.card hrow
  rw [card_image_of_injective O hr,card_image_of_injOn R.property.2.2.1,R.property.2.1] at hcount
  let T := univ.filter fun i : Fin (g+1) => ¬occ i
  have hall := univ.card_filter_add_card_filter_not occ
  change O.card+T.card=(univ : Finset (Fin (g+1))).card at hall
  rw [card_univ,Fintype.card_fin,hcount] at hall
  obtain ⟨i₀,hi₀⟩ := card_eq_one.mp (show T.card=1 by omega)
  have absent (i : Fin (g+1)) : ¬occ i ↔ i=i₀ := by
    have he : i∈T ↔ i=i₀ := by rw [hi₀,mem_singleton]
    simpa only [T,mem_filter,mem_univ,true_and] using he
  let col (i : Fin (g+1)) := if h : occ i then h.choose+1 else 0
  have hzero (i : Fin (g+1)) : col i=0 ↔ i=i₀ := by
    rw [← absent]
    by_cases h : occ i <;> simp [col,h]
  have geometric (i : Fin (g+1)) (j : ℕ) : col i=j+1 ↔ (g-i.val,j)∈R.val := by
    by_cases h : occ i
    · have hs := h.choose_spec
      simp only [col,dif_pos h,Nat.succ.injEq]
      constructor
      · rintro rfl
        exact hs
      · intro hx
        exact congrArg Prod.snd (R.property.2.2.1 hs hx rfl)
    · simp only [col,dif_neg h,Nat.zero_ne_add_one,false_iff]
      exact fun hx => h ⟨j,hx⟩
  let assign : NestedRowRooks (watersNestedRow D 1) (g+1) := by
    refine ⟨⟨col,?_⟩,?_⟩
    · intro i j he
      by_cases h : col i=0
      · exact ((hzero i).mp h).trans ((hzero j).mp (he ▸ h)).symm
      · let a := col i-1
        have hv : col i=a+1 := by dsimp [a]; omega
        have hi := (geometric i a).mp hv
        have hj := (geometric j a).mp (he ▸ hv)
        exact hr (congrArg Prod.fst (R.property.2.2.2 hi hj rfl))
    · intro i
      by_cases h : col i=0
      · apply mem_range.mpr
        change col i < i.val+1+(if i.val∈D then 1 else 0)
        omega
      · let a := col i-1
        have ha : col i=a+1 := by dsimp [a]; omega
        have hpos := (geometric i a).mp ha
        have hb := mem_range.mp ((rim_row_cells hD i a).mp (R.property.1 hpos))
        change a < i.val+0+(if i.val∈D then 1 else 0) at hb
        apply mem_range.mpr
        change col i < i.val+1+(if i.val∈D then 1 else 0)
        omega
  let f : WatersOmittedRow D (g+1) := ⟨assign,i₀,(hzero i₀).mpr rfl⟩
  refine ⟨f,Subtype.ext ?_⟩
  change physicalRooks f = R.val
  ext ⟨a,b⟩
  by_cases ha : a≤g
  · let i : Fin (g+1) := ⟨g-a,by omega⟩
    have hi : g-i.val=a := by dsimp [i]; omega
    rw [← hi,mem_physicalRooks]
    exact geometric i b
  · constructor
    · intro hx
      have hh := rim_row_bound ((decodeRimRooks hD f).property.1 hx)
      exact (ha hh).elim
    · intro hx
      exact (ha (rim_row_bound (R.property.1 hx))).elim

/-- A diagram with s optional diagonal cells carries 2^s placements, except
that the complete rim carries 2^s-1. The identity avoids subtraction. -/
theorem second_moment_rooks_per_board (g : ℕ) (D : Finset ℕ) (hD : D⊆range (g+1)) :
    Nat.card (BoardPlacement (watersRimBoard g D) g) + (if D=range (g+1) then 1 else 0) = 2^D.card := by
  let e := Equiv.ofBijective (decodeRimRooks hD) ⟨decodeRimRooks_injective hD,decodeRimRooks_surjective hD⟩
  have hfilter : (range (g+1)).filter (·∈D)=D := by
    ext i
    exact ⟨fun hi => (mem_filter.mp hi).2,fun hi => mem_filter.mpr ⟨hD hi,hi⟩⟩
  have he : range (g+1) ⊆ D ↔ D=range (g+1) := ⟨fun h => Subset.antisymm hD h,fun h => h ▸ Subset.rfl⟩
  rw [← Nat.card_congr e]
  simpa only [he,hfilter] using card_watersOmittedRow D (g+1)

/-- The optional antidiagonal parametrizes the entire support without
multiplicity. The parameter of a rim cell is its column. -/
theorem watersBoards_by_rim (g : ℕ) :
    watersBoards (g+1) g = ((range (g+1)).powerset).image (watersRimBoard g) := by
  let L := (rookStaircase g).cells
  let D := (rookStaircase (g+1)).cells \ L
  let atRim (j : ℕ) := (g-j,j)
  have hrim (p : ℕ×ℕ) : p∈D ↔ p.1+p.2=g := by
    constructor
    · intro hp
      obtain ⟨hu,hl⟩ := mem_sdiff.mp hp
      have h₁ := mem_rookStaircase.mp hu
      have h₂ : ¬p.1+p.2<g := fun h => hl (mem_rookStaircase.mpr h)
      omega
    · intro he
      exact mem_sdiff.mpr ⟨mem_rookStaircase.mpr (by omega),fun h => (mem_rookStaircase.mp h).ne he⟩
  rw [watersBoards_next]
  ext B
  rw [mem_image,mem_image]
  constructor
  · rintro ⟨T,hT,rfl⟩
    have ht : T⊆D := mem_powerset.mp hT
    have hD : T.image Prod.snd ⊆ range (g+1) := by
      rintro y hy
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hy
      have := (hrim p).mp (ht hp)
      exact mem_range.mpr (by omega)
    refine ⟨T.image Prod.snd,mem_powerset.mpr hD,?_⟩
    change L∪(T.image Prod.snd).image atRim = L∪T
    congr 1
    ext p
    constructor
    · intro hp
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hp
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hy
      have he := (hrim q).mp (ht hq)
      have hr : atRim q.2=q := Prod.ext (by dsimp [atRim]; omega) rfl
      exact hr.symm ▸ hq
    · intro hp
      have he := (hrim p).mp (ht hp)
      exact mem_image.mpr ⟨p.2,mem_image.mpr ⟨p,hp,rfl⟩,Prod.ext (by dsimp [atRim]; omega) rfl⟩
  · rintro ⟨T,hT,rfl⟩
    refine ⟨T.image atRim,mem_powerset.mpr ?_,rfl⟩
    intro p hp
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hp
    have := mem_range.mp (mem_powerset.mp hT hy)
    exact (hrim _).mpr (by dsimp [atRim]; omega)

private theorem rim_injective (g : ℕ) :
    Set.InjOn (watersRimBoard g) (↑(range (g+1)).powerset : Set (Finset ℕ)) := by
  intro D hD T hT he
  have diag (A : Finset ℕ) (hA : A⊆range (g+1)) (i : Fin (g+1)) :
      (g-i.val,i.val)∈watersRimBoard g A ↔ i.val∈A := by
    rw [rim_row_cells hA,watersNestedRow,mem_range]
    by_cases hi : i.val∈A <;> simp [hi]
  ext y
  by_cases hy : y<g+1
  · let i : Fin (g+1) := ⟨y,hy⟩
    change i.val∈D ↔ i.val∈T
    rw [← diag D (mem_powerset.mp hD) i,he,diag T (mem_powerset.mp hT) i]
  · exact iff_of_false (fun hd => hy (mem_range.mp (mem_powerset.mp hD hd)))
      (fun ht => hy (mem_range.mp (mem_powerset.mp hT ht)))

/-- The coefficient of inverse Poissonization degree g in moment 2(g+2)
of Waters' formula (16) is exactly 3^(g+1)-1, counting each rook set. -/
theorem waters_second_moment_coefficient (g : ℕ) :
    (∑ B ∈ watersBoards (g+1) g, Nat.card (BoardPlacement B g)) + 1 = 3^(g+1) := by
  rw [watersBoards_by_rim,sum_image (rim_injective g)]
  have he (D : Finset ℕ) (hD : D∈(range (g+1)).powerset) :
      Nat.card (BoardPlacement (watersRimBoard g D) g)=Nat.card (WatersOmittedRow D (g+1)) :=
    (Nat.card_congr (Equiv.ofBijective (decodeRimRooks (mem_powerset.mp hD))
      ⟨decodeRimRooks_injective _,decodeRimRooks_surjective _⟩)).symm
  rw [sum_congr rfl he]
  exact waters_second_placement_sum (g+1)

private theorem watersRimBoard_card {g : ℕ} {D : Finset ℕ} (hD : D⊆range (g+1)) :
    (watersRimBoard g D).card = (g+1).choose 2+D.card := by
  let f (j : ℕ) := (g-j,j)
  have dis : Disjoint (rookStaircase g).cells (D.image f) := by
    apply disjoint_left.mpr
    intro p hp h
    obtain ⟨j,hj,rfl⟩ := mem_image.mp h
    have hsmall := mem_rookStaircase.mp hp
    change g-j+j < g at hsmall
    have := mem_range.mp (hD hj)
    omega
  change ((rookStaircase g).cells∪D.image f).card=_
  rw [card_union_of_disjoint dis,rookStaircase_card,
    card_image_of_injective _ (fun _ _ he => congrArg Prod.snd he)]

/-- Area-refined second rook coefficient. At excess area j the coefficient
is the binomial count of rims times the binary placement count, with one
missing placement exactly at the largest possible area. -/
theorem waters_second_coefficient_by_area (g j : ℕ) :
    (∑ B ∈ (watersBoards (g+1) g).filter (fun B => B.card=(g+1).choose 2+j),
      Nat.card (BoardPlacement B g)) + (if j=g+1 then 1 else 0) =
        (g+1).choose j*2^j := by
  let U := range (g+1)
  let P := U.powersetCard j
  have hull (D : Finset ℕ) (hd : D∈P) : D⊆U ∧ D.card=j := mem_powersetCard.mp hd
  have hs : (watersBoards (g+1) g).filter (fun B => B.card=(g+1).choose 2+j) =
      P.image (watersRimBoard g) := by
    ext B
    rw [mem_filter,watersBoards_by_rim,mem_image,mem_image]
    constructor
    · rintro ⟨⟨D,hd,rfl⟩,hc⟩
      have hD := mem_powerset.mp hd
      rw [watersRimBoard_card hD] at hc
      exact ⟨D,mem_powersetCard.mpr ⟨hD,by omega⟩,rfl⟩
    · rintro ⟨D,hd,rfl⟩
      obtain ⟨hD,hc⟩ := hull D hd
      exact ⟨⟨D,mem_powerset.mpr hD,rfl⟩,by rw [watersRimBoard_card hD,hc]⟩
  have hinj : Set.InjOn (watersRimBoard g) (P : Set (Finset ℕ)) :=
    fun _ ha _ hb => rim_injective g (mem_powerset.mpr (hull _ ha).1) (mem_powerset.mpr (hull _ hb).1)
  have corr : (∑ D ∈ P, if D=U then 1 else 0) = (if j=g+1 then 1 else 0) := by
    by_cases he : j=g+1 <;> simp [P,mem_powersetCard,U,he,eq_comm]
  rw [hs,sum_image hinj,← corr,← sum_add_distrib]
  calc
    _ = ∑ D ∈ P, 2^j := sum_congr rfl fun D hd => by
      obtain ⟨hD,hj⟩ := hull D hd
      simpa only [hj] using second_moment_rooks_per_board g D hD
    _ = _ := by simp only [P,U,sum_const,card_powersetCard,card_range,nsmul_eq_mul,Nat.cast_id]

#print axioms waters_second_coefficient_by_area

#print axioms second_moment_rooks_per_board
#print axioms watersBoards_by_rim
#print axioms waters_second_moment_coefficient
end
end GaloisForLFunctions.StaircasePacking
