import GaloisForLFunctions.HTGeometry.ApartmentLinkTransport

/-!
# Frames of a lattice element and the apartments they span

An apartment of a building is the subcomplex spanned by a frame: an independent family of atoms
whose join is the element the building belongs to.  Its vertices are the joins of the proper nonempty
subfamilies, and independence makes that assignment strictly monotone, which is exactly what the
Solomon--Tits descent needs of an apartment.

Working with frames of a lattice element rather than with bases of a vector space keeps the whole
induction inside one lattice: the frame of a coatom is a subfamily of a frame of the element above
it, so passing to the link of an apartment removes one atom and nothing has to be transported.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u

/-- **A frame of an element of a complete lattice**: an independent family of atoms whose join is
that element. -/
structure LatticeFrame (L : Type u) [CompleteLattice L] (ι : Type u) (T : L) where
  /-- The atoms of the frame. -/
  atom : ι → L
  isAtom : ∀ i, IsAtom (atom i)
  indep : iSupIndep atom
  sup_eq : ⨆ i, atom i = T

namespace LatticeFrame

variable {L : Type u} [CompleteLattice L] {ι : Type u} {T : L} (F : LatticeFrame L ι T)

/-- The element spanned by a subfamily of a frame. -/
def span (S : Set ι) : L := ⨆ i ∈ S, F.atom i

theorem span_mono : Monotone F.span := fun _ _ h => biSup_mono h

theorem span_univ : F.span Set.univ = T := by
  have h : F.span Set.univ = ⨆ i, F.atom i := iSup_congr fun i => by simp
  rw [h, F.sup_eq]

theorem atom_le_span {i : ι} {S : Set ι} (h : i ∈ S) : F.atom i ≤ F.span S := le_biSup _ h

theorem span_le (T' : L) (h : ∀ i ∈ S, F.atom i ≤ T') : F.span S ≤ T' := by
  exact iSup₂_le h

theorem span_le_top' (S : Set ι) : F.span S ≤ T := by
  have h := F.span_mono (Set.subset_univ S)
  rwa [F.span_univ] at h

/-- **An atom outside a subfamily is not below its join.**  This is the whole content of
independence. -/
theorem atom_not_le_span {i : ι} {S : Set ι} (h : i ∉ S) : ¬ F.atom i ≤ F.span S := fun hle =>
  (F.isAtom i).1 (disjoint_self.1 ((F.indep.disjoint_biSup h).mono_right hle))

/-- **The join of a subfamily determines the subfamily.** -/
theorem span_strictMono : StrictMono F.span := by
  intro S S' h
  refine lt_of_le_of_ne (F.span_mono (le_of_lt h)) fun hcon => ?_
  obtain ⟨j, hjS', hjS⟩ : ∃ j, j ∈ S' ∧ j ∉ S := by
    by_contra hc
    push Not at hc
    exact absurd (Set.Subset.antisymm (le_of_lt h) fun x hx => hc x hx) (ne_of_lt h)
  exact F.atom_not_le_span hjS (hcon ▸ F.atom_le_span hjS')

theorem span_lt (h : S ≠ Set.univ) : F.span S < T := by
  have h2 := F.span_strictMono (lt_of_le_of_ne (Set.subset_univ S) h)
  rwa [F.span_univ] at h2

theorem bot_lt_span (h : S.Nonempty) : ⊥ < F.span S := by
  obtain ⟨i, hi⟩ := h
  exact lt_of_lt_of_le (bot_lt_iff_ne_bot.2 (F.isAtom i).1) (F.atom_le_span hi)

/-- The join of a subfamily with an atom outside it is the join of the enlarged subfamily. -/
theorem span_sup_atom (i : ι) (S : Set ι) : F.span S ⊔ F.atom i = F.span (insert i S) := by
  refine le_antisymm (sup_le (F.span_mono (Set.subset_insert i S))
    (F.atom_le_span (Set.mem_insert i S))) ?_
  refine iSup₂_le fun j hj => ?_
  rcases hj with hj | hj
  · exact hj ▸ le_sup_right
  · exact le_sup_of_le_left (F.atom_le_span hj)

theorem span_congr {T' : L} {F' : LatticeFrame L ι T'} (h : ∀ i, F.atom i = F'.atom i)
    (S : Set ι) : F.span S = F'.span S :=
  iSup_congr fun i => iSup_congr fun _ => h i

theorem atom_le_top (i : ι) : F.atom i ≤ T := by
  have h := le_iSup (fun j => F.atom j) i
  rwa [F.sup_eq] at h

theorem le_of_atom_le {X : L} (h : ∀ i, F.atom i ≤ X) : T ≤ X := by
  have h2 := iSup_le h
  rwa [F.sup_eq] at h2

/-- **The restriction of a frame to a subfamily** is a frame of its join. -/
def restrict (S : Set ι) : LatticeFrame L ↥S (F.span S) where
  atom j := F.atom (j : ι)
  isAtom j := F.isAtom _
  indep := F.indep.comp Subtype.val_injective
  sup_eq := by
    show (⨆ j : ↥S, F.atom (j : ι)) = ⨆ i ∈ S, F.atom i
    exact (iSup_subtype' (p := fun i => i ∈ S) (f := fun i _ => F.atom i)).symm

@[simp] theorem restrict_span (S : Set ι) (T : Set ↥S) :
    (F.restrict S).span T = F.span (Subtype.val '' T) := by
  show (⨆ j ∈ T, F.atom (j : ι)) = ⨆ i ∈ Subtype.val '' T, F.atom i
  refine le_antisymm (iSup₂_le fun j hj => le_biSup _ ⟨j, hj, rfl⟩) (iSup₂_le fun i hi => ?_)
  obtain ⟨j, hj, rfl⟩ := hi
  exact le_biSup (fun j : ↥S => F.atom (j : ι)) hj

end LatticeFrame

/-! ## The apartment of a frame inside a family of interval buildings -/

/-- **A frame of one component of a family of interval buildings.** -/
structure FrameDatum {L : Type u} [CompleteLattice L] {κ : Type u} (W : κ → L) (ι : Type u) where
  /-- The component of the family. -/
  comp : κ
  /-- The frame of that component. -/
  frame : LatticeFrame L ι (W comp)

namespace FrameDatum

variable {L : Type u} [CompleteLattice L] {κ : Type u} {W : κ → L} {ι : Type u}
variable (Q : FrameDatum W ι)

theorem span_lt_top (S : properPart (Set ι)) : Q.frame.span S < ⊤ :=
  lt_of_lt_of_le (Q.frame.span_lt (Set.ssubset_univ_iff.1 S.2.2)) (le_top : W Q.comp ≤ ⊤)

theorem bot_lt_span (S : properPart (Set ι)) : ⊥ < Q.frame.span S :=
  Q.frame.bot_lt_span (Set.nonempty_iff_ne_empty.2 (ne_of_gt S.2.1))

/-- A vertex of the apartment of a pointed frame. -/
def vertex (S : properPart (Set ι)) : famBuilding W :=
  ⟨(Q.comp, ⟨Q.frame.span S, Q.bot_lt_span S, Q.span_lt_top S⟩),
    Q.frame.span_lt (Set.ssubset_univ_iff.1 S.2.2)⟩

@[simp] theorem vertex_snd (S : properPart (Set ι)) :
    ((Subtype.val (Q.vertex S)).2 : L) = Q.frame.span S := rfl

/-- **The apartment of a pointed frame**, as a monotone map into the disjoint union. -/
def vertices : properPart (Set ι) →o famBuilding W where
  toFun := Q.vertex
  monotone' _ _ h := ⟨rfl, Q.frame.span_mono h⟩

@[simp] theorem vertices_apply (S : properPart (Set ι)) : Q.vertices S = Q.vertex S := rfl

theorem vertices_congr {Q' : FrameDatum W ι} (hcomp : Q.comp = Q'.comp)
    (hspan : ∀ S : Set ι, Q.frame.span S = Q'.frame.span S) : Q.vertices = Q'.vertices := by
  refine OrderHom.ext _ _ (funext fun S => ?_)
  exact Subtype.ext (Prod.ext hcomp (Subtype.ext (hspan S)))

/-- **The apartment of a frame is strictly monotone.** -/
theorem strictMono_vertices : StrictMono Q.vertices := by
  intro S S' h
  refine lt_of_le_of_ne (Q.vertices.monotone (le_of_lt h)) fun hcon => ?_
  refine absurd (Q.frame.span_strictMono h) (not_lt_of_ge (le_of_eq ?_))
  exact (congrArg (fun q : famBuilding W => ((Subtype.val q).2 : L)) hcon).symm

end FrameDatum

/-- **A frame of a component of a family that contains the chosen atom of that component.**  The
Solomon--Tits descent needs exactly these: an apartment whose frame contains the atom the cover is
taken with. -/
structure PointedFrame {L : Type u} [CompleteLattice L] {κ : Type u} (W p : κ → L)
    (ι : Type u) extends FrameDatum W ι where
  /-- The place of the chosen atom. -/
  idx : ι
  atom_eq : frame.atom idx = p comp

namespace PointedFrame

variable {L : Type u} [CompleteLattice L] {κ : Type u} {W p : κ → L} {ι : Type u}
variable (Q : PointedFrame W p ι)

theorem insert_idx_eq_univ_iff {U : Set ι} (hU : U ≠ Set.univ) :
    insert Q.idx U = Set.univ ↔ U = Set.univ \ {Q.idx} := by
  constructor
  · intro h
    by_cases hidx : Q.idx ∈ U
    · exact absurd (Set.Subset.antisymm (Set.subset_univ U) fun x _ => by
        have hx : x ∈ insert Q.idx U := by rw [h]; trivial
        rcases hx with hx | hx
        · exact hx ▸ hidx
        · exact hx) hU
    · refine Set.Subset.antisymm (fun x hx => ⟨Set.mem_univ x, fun hcon => hidx (hcon ▸ hx)⟩)
        fun x hx => ?_
      have hxi : x ∈ insert Q.idx U := by rw [h]; trivial
      exact hxi.resolve_left fun hcon => hx.2 hcon
  · intro h
    subst h
    refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x = Q.idx
    · exact Set.mem_insert_iff.2 (Or.inl hx)
    · exact Set.mem_insert_iff.2 (Or.inr ⟨Set.mem_univ x, hx⟩)

/-- **Every vertex of the apartment other than the coatom opposite the chosen atom lies in the base
of the cover.** -/
theorem vertex_mem_famCoverBase (U : properPart (Set ι))
    (h : (U : Set ι) ≠ Set.univ \ {Q.idx}) : Q.toFrameDatum.vertices U ∈ famCoverBase W p := by
  show Q.frame.span U < W Q.comp ∧ Q.frame.span U ⊔ p Q.comp ≠ W Q.comp
  refine ⟨Q.frame.span_lt (Set.ssubset_univ_iff.1 U.2.2), fun hcon => ?_⟩
  rw [show p Q.comp = Q.frame.atom Q.idx from Q.atom_eq.symm, Q.frame.span_sup_atom] at hcon
  refine absurd hcon (ne_of_lt (Q.frame.span_lt fun hins => ?_))
  exact h ((Q.insert_idx_eq_univ_iff (Set.ssubset_univ_iff.1 U.2.2)).1 hins)

variable [Finite ι] {n : ℕ}

/-- **The piece of the cover the apartment meets**: the coatom opposite the chosen atom. -/
def coverIndex (hN : Nat.card ι = n + 3) : famCoverIndex W p :=
  ⟨(Q.comp, (Subtype.val (Q.toFrameDatum.vertex (apartmentCoatom hN Q.idx))).2), by
    refine ⟨Q.frame.span_lt (Set.ssubset_univ_iff.1 (apartmentCoatom hN Q.idx).2.2), ?_⟩
    show Q.frame.span (Set.univ \ {Q.idx}) ⊔ p Q.comp = W Q.comp
    rw [show p Q.comp = Q.frame.atom Q.idx from Q.atom_eq.symm, Q.frame.span_sup_atom,
      show insert Q.idx (Set.univ \ {Q.idx} : Set ι) = Set.univ from
        (Q.insert_idx_eq_univ_iff (fun hcon => by
          have : Q.idx ∈ (Set.univ \ {Q.idx} : Set ι) := by rw [hcon]; trivial
          exact this.2 rfl)).2 rfl,
      Q.frame.span_univ]⟩

omit [Finite ι] in
/-- **The coatom opposite the chosen atom is the centre of that piece.** -/
theorem vertices_apartmentCoatom (hN : Nat.card ι = n + 3) :
    Q.toFrameDatum.vertices (apartmentCoatom hN Q.idx)
      = famCoverCentre W p (Q.coverIndex hN) := rfl

end PointedFrame

/-! ## Extending a frame of a coatom by an atom -/

section Extend

variable {L : Type u} [CompleteLattice L] [IsModularLattice L] {ι : Type u} {i₀ : ι}
variable {c T : L}

namespace LatticeFrame

variable (G : LatticeFrame L ↥(Set.univ \ {i₀} : Set ι) c) (a : L)
variable (ha : IsAtom a) (hlt : c < T) (hspan : c ⊔ a = T)

theorem mem_univ_diff_singleton {j : ι} (h : j ≠ i₀) :
    j ∈ (Set.univ \ {i₀} : Set ι) := ⟨Set.mem_univ j, h⟩

open scoped Classical in
/-- The family of atoms of the extended frame. -/
noncomputable def extendAtom (i : ι) : L :=
  if h : i = i₀ then a else G.atom ⟨i, mem_univ_diff_singleton h⟩

omit [IsModularLattice L] in
@[simp] theorem extendAtom_self : extendAtom G a i₀ = a := dif_pos rfl

omit [IsModularLattice L] in
theorem extendAtom_of_ne {i : ι} (h : i ≠ i₀) :
    extendAtom G a i = G.atom ⟨i, mem_univ_diff_singleton h⟩ := dif_neg h

omit [IsModularLattice L] in
theorem extendAtom_coe (j : ↥(Set.univ \ {i₀} : Set ι)) :
    extendAtom G a (j : ι) = G.atom j := by
  rw [extendAtom_of_ne G a j.2.2]

omit [IsModularLattice L] in
/-- The atoms other than the new one span the coatom. -/
theorem iSup_extendAtom_ne : (⨆ j, ⨆ (_ : j ≠ i₀), extendAtom G a j) = c := by
  refine le_antisymm (iSup₂_le fun j hj => ?_) (G.le_of_atom_le fun j' => ?_)
  · rw [extendAtom_of_ne G a hj]
    exact G.atom_le_top _
  · refine le_trans (le_of_eq (extendAtom_coe G a j').symm) ?_
    exact le_iSup₂ (f := fun j (_ : j ≠ i₀) => extendAtom G a j) (j' : ι) j'.2.2

omit [IsModularLattice L] in
theorem disjoint_of_isAtom_of_lt {a' c' T' : L} (ha' : IsAtom a') (hlt' : c' < T')
    (hspan' : c' ⊔ a' = T') : Disjoint a' c' := by
  refine disjoint_iff.2 ?_
  rcases (IsAtom.le_iff ha' (x := a' ⊓ c')).1 inf_le_left with h | h
  · exact h
  · refine absurd (le_antisymm (le_of_lt hlt') ?_) (ne_of_lt hlt')
    rw [← hspan']
    exact sup_le le_rfl (h ▸ inf_le_right)

include ha hlt hspan in
/-- **A frame of a coatom, extended by an atom that spans with it, is a frame of the whole.** -/
noncomputable def extend : LatticeFrame L ι T where
  atom := extendAtom G a
  isAtom i := by
    by_cases h : i = i₀
    · rw [h, extendAtom_self]
      exact ha
    · rw [extendAtom_of_ne G a h]
      exact G.isAtom _
  indep := by
    refine iSupIndep_def.2 fun i => ?_
    by_cases h : i = i₀
    · subst h
      rw [extendAtom_self, iSup_extendAtom_ne]
      exact disjoint_of_isAtom_of_lt ha hlt hspan
    · set i' : ↥(Set.univ \ {i₀} : Set ι) := ⟨i, mem_univ_diff_singleton h⟩ with hi'def
      rw [show extendAtom G a i = G.atom i' from extendAtom_of_ne G a h]
      have hb : (⨆ j, ⨆ (_ : j ≠ i), extendAtom G a j)
          ≤ (⨆ j', ⨆ (_ : j' ≠ i'), G.atom j') ⊔ a := by
        refine iSup₂_le fun j hj => ?_
        by_cases hj₀ : j = i₀
        · rw [hj₀, extendAtom_self]
          exact le_sup_right
        · refine le_sup_of_le_left ?_
          rw [extendAtom_of_ne G a hj₀]
          refine le_iSup₂ (f := fun j' (_ : j' ≠ i') => G.atom j')
            (⟨j, mem_univ_diff_singleton hj₀⟩ : ↥(Set.univ \ {i₀} : Set ι)) fun hcon => ?_
          exact hj (congrArg Subtype.val hcon)
      refine Disjoint.mono_right hb ?_
      have hbc : (⨆ j', ⨆ (_ : j' ≠ i'), G.atom j') ≤ c :=
        iSup₂_le fun j' _ => G.atom_le_top j'
      have hac : (⨆ j', ⨆ (_ : j' ≠ i'), G.atom j') ⊔ a ⊓ c
          = ((⨆ j', ⨆ (_ : j' ≠ i'), G.atom j') ⊔ a) ⊓ c := (sup_inf_assoc_of_le a hbc).symm
      rw [disjoint_iff.1 (disjoint_of_isAtom_of_lt ha hlt hspan), sup_bot_eq] at hac
      refine disjoint_iff.2 ?_
      have hGle : G.atom i' ≤ c := G.atom_le_top i'
      have hstep : G.atom i' ⊓ ((⨆ j', ⨆ (_ : j' ≠ i'), G.atom j') ⊔ a)
          = G.atom i' ⊓ (((⨆ j', ⨆ (_ : j' ≠ i'), G.atom j') ⊔ a) ⊓ c) := by
        rw [← inf_assoc, inf_right_comm, inf_eq_left.2 hGle]
      rw [hstep, ← hac]
      exact disjoint_iff.1 (iSupIndep_def.1 G.indep i')
  sup_eq := by
    refine le_antisymm (iSup_le fun i => ?_) ?_
    · by_cases h : i = i₀
      · rw [h, extendAtom_self, ← hspan]
        exact le_sup_right
      · rw [extendAtom_of_ne G a h, ← hspan]
        exact le_sup_of_le_left (G.atom_le_top _)
    · rw [← hspan]
      refine sup_le ?_ ?_
      · exact le_trans (le_of_eq (iSup_extendAtom_ne G a).symm)
          (iSup₂_le fun j _ => le_iSup (fun j => extendAtom G a j) j)
      · exact le_of_eq_of_le (extendAtom_self G a).symm (le_iSup (fun j => extendAtom G a j) i₀)

@[simp] theorem extend_atom_coe (j : ↥(Set.univ \ {i₀} : Set ι)) :
    (extend G a ha hlt hspan).atom (j : ι) = G.atom j := extendAtom_coe G a j

@[simp] theorem extend_atom_self : (extend G a ha hlt hspan).atom i₀ = a := extendAtom_self G a

end LatticeFrame

end Extend

/-! ## Every frame of a coatom is the link of a frame above it -/

section Surjective

variable {L : Type u} [CompleteLattice L] [IsModularLattice L] {κ : Type u} {W p : κ → L}
variable {ι : Type u} [Finite ι] {n : ℕ} {i₀ : ι}

omit [Finite ι] in
theorem LatticeFrame.extend_span_compl
    (G : LatticeFrame L ↥(Set.univ \ {i₀} : Set ι) c) (a : L) (ha : IsAtom a) (hlt : c < T)
    (hspan : c ⊔ a = T) :
    (LatticeFrame.extend G a ha hlt hspan).span (Set.univ \ {i₀}) = c := by
  refine le_antisymm (iSup₂_le fun j hj => ?_) (G.le_of_atom_le fun j' => ?_)
  · rw [show (LatticeFrame.extend G a ha hlt hspan).atom j = G.atom ⟨j, hj⟩ from
      LatticeFrame.extendAtom_of_ne G a hj.2]
    exact G.atom_le_top _
  · refine le_trans (le_of_eq (LatticeFrame.extend_atom_coe G a ha hlt hspan j').symm) ?_
    exact le_biSup (fun j => (LatticeFrame.extend G a ha hlt hspan).atom j) j'.2

omit [Finite ι] in
/-- **Every frame of a coatom extends to a pointed frame above it**, by adding the atom the cover is
taken with: the link of the extended apartment is the given one. -/
theorem exists_frameDatum_extend (hN : Nat.card ι = n + 3) (hp : ∀ a, IsAtom (p a))
    (c : famCoverIndex W p)
    (G : LatticeFrame L ↥(Set.univ \ {i₀} : Set ι) (famCoverTop c)) :
    ∃ (D : FrameDatum W ι) (h : D.frame.atom i₀ = p D.comp),
      (⟨D, i₀, h⟩ : PointedFrame W p ι).coverIndex hN = c
        ∧ ∀ j : ↥(Set.univ \ {i₀} : Set ι), D.frame.atom (j : ι) = G.atom j := by
  refine ⟨⟨(Subtype.val c).1, LatticeFrame.extend G (p (Subtype.val c).1) (hp _) c.2.1 c.2.2⟩,
    LatticeFrame.extend_atom_self G (p (Subtype.val c).1) (hp _) c.2.1 c.2.2, ?_,
    fun j => LatticeFrame.extend_atom_coe G (p (Subtype.val c).1) (hp _) c.2.1 c.2.2 j⟩
  refine Subtype.ext (Prod.ext rfl (Subtype.ext ?_))
  exact LatticeFrame.extend_span_compl G (p (Subtype.val c).1) (hp _) c.2.1 c.2.2

end Surjective

/-! ## The link of the apartment of a pointed frame -/

section Link

variable {L : Type u} [CompleteLattice L] [IsModularLattice L] {κ : Type u} {W p : κ → L}
variable {ι : Type u} [Finite ι] {n : ℕ} (Q : PointedFrame W p ι) (hN : Nat.card ι = n + 3)

omit [IsModularLattice L] [Finite ι] in
/-- **The link of the apartment of a pointed frame is the apartment of the frame with the chosen
atom removed**, inside the building below the coatom. -/
theorem linkOrderHom_eq_vertices :
    linkOrderHom Q.toFrameDatum.vertices (Q.coverIndex hN) Q.toFrameDatum.strictMono_vertices
        (Q.vertices_apartmentCoatom hN)
      = (FrameDatum.mk (W := fun c' : famCoverIndex W p => famCoverTop c') (Q.coverIndex hN)
          (Q.frame.restrict (Set.univ \ {Q.idx}))).vertices := by
  refine OrderHom.ext _ _ (funext fun T => ?_)
  refine Subtype.ext (Prod.ext rfl (Subtype.ext ?_))
  show Q.frame.span ((Subtype.val '' (T : Set ↥(Set.univ \ {Q.idx} : Set ι))))
    = (Q.frame.restrict (Set.univ \ {Q.idx})).span T
  rw [LatticeFrame.restrict_span]

end Link

end GaloisForLFunctions.HTGeometry
