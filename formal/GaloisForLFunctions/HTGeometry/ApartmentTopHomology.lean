import GaloisForLFunctions.HTGeometry.BooleanIntervalCover

/-!
# The apartment of a frame is a sphere: its top homology is one copy of the coefficients

The order complex of the proper part of a Boolean interval is the Coxeter sphere of the frame.  Its
cover by the star of a coatom has exactly one piece, so the Mayer--Vietoris descent goes down one
element at a time with no branching, and at the bottom — an interval with three elements — the first
homology is the kernel of the map from the two components of the intersection to the single component
of the star.  That kernel is one copy of the coefficients, and the descent carries it up.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u c

section Combinatorics

variable {ι : Type u} {S : Set ι} {a : ι}

/-- A nonzero proper subset of a two-element set is one of its two points. -/
theorem eq_singleton_of_lt_pair {x y : ι} {U : Set ι} (hne : U.Nonempty)
    (hlt : U < ({x, y} : Set ι)) : U = {x} ∨ U = {y} := by
  obtain ⟨z, hz⟩ := hne
  have hsub : U ⊆ ({x, y} : Set ι) := le_of_lt hlt
  have hnot : ¬(x ∈ U ∧ y ∈ U) := by
    rintro ⟨hx, hy⟩
    refine absurd (Set.Subset.antisymm hsub ?_) (ne_of_lt hlt)
    rintro w (rfl | rfl)
    · exact hx
    · exact hy
  rcases hsub hz with rfl | rfl
  · refine Or.inl (Set.Subset.antisymm (fun w hw => ?_) (Set.singleton_subset_iff.2 hz))
    rcases hsub hw with rfl | rfl
    · rfl
    · exact absurd ⟨hz, hw⟩ hnot
  · refine Or.inr (Set.Subset.antisymm (fun w hw => ?_) (Set.singleton_subset_iff.2 hz))
    rcases hsub hw with rfl | rfl
    · exact absurd ⟨hw, hz⟩ hnot
    · rfl

/-- The vertex of the disjoint union attached to a subset strictly inside the interval. -/
def boolElt (S : Set ι) (U : Set ι) (h1 : (⊥ : Set ι) < U) (h2 : U < ⊤) (h3 : U < S) :
    famBuilding (fun _ : PUnit.{u + 1} => S) := ⟨(PUnit.unit, ⟨U, h1, h2⟩), h3⟩

/-- **The intersection of the base with the single piece is the interval below the coatom.** -/
theorem mem_boolInter_iff (ha : a ∈ S) (h2 : 2 ≤ S.ncard)
    (q : famBuilding (fun _ : PUnit.{u + 1} => S)) :
    q ∈ famCoverBase (fun _ : PUnit.{u + 1} => S) (fun _ => {a})
        ∩ generalStar (famCoverCentre (fun _ : PUnit.{u + 1} => S) (fun _ => {a})
          (boolCoverElt ha h2))
      ↔ ((Subtype.val q).2 : Set ι) < S \ {a} := by
  rw [famCoverBase_inter_piece (fun _ => Set.isAtom_singleton a) (boolCoverElt ha h2)]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

end Combinatorics

section BaseCase

variable {C : Type c} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]
variable {ι : Type u} {S : Set ι} {a : ι}

/-- The pieces of the cover of a Boolean interval form a connected complex: there is one of them,
and it is a star. -/
theorem isPreconnected_boolPieces (ha : a ∈ S) (h2 : 2 ≤ S.ncard) :
    SSet.IsPreconnected (famSSet (famCoverPieceSub (W := fun _ : PUnit.{u + 1} => S)
      (p := fun _ => ({a} : Set ι)))) := by
  haveI := uniqueBoolCoverIndex ha h2
  refine isPreconnected_famSSet_of_subsingleton _ fun c => ?_
  exact isPreconnected_nerveSubcomplex_of_cone (Or.inl le_rfl) fun q hq => hq

/-- The vertex of the intersection attached to an element of the interval below the coatom. -/
def boolInterVertex (ha : a ∈ S) (h2 : 2 ≤ S.ncard)
    (q : famBuilding (fun _ : PUnit.{u + 1} => S))
    (hq : ((Subtype.val q).2 : Set ι) < S \ {a}) :
    (((famCoverBaseSub (W := fun _ : PUnit.{u + 1} => S) (p := fun _ => ({a} : Set ι))
        ⊓ famCoverPieceSub (boolCoverElt ha h2)) : (nerve (famBuilding
          (fun _ : PUnit.{u + 1} => S))).Subcomplex) : SSet.{u}) _⦋0⦌ :=
  ⟨ComposableArrows.mk₀ q,
    ⟨fun _ => ((mem_boolInter_iff ha h2 q).2 hq).1, fun _ => ((mem_boolInter_iff ha h2 q).2 hq).2⟩⟩

/-- **The first homology of a three-element Boolean interval is one copy of the coefficients.**
The cover has one piece, whose intersection with the base is the two-point antichain below the
coatom, so the Mayer--Vietoris kernel is the coproduct over one index. -/
theorem nonempty_homology_iso_bool_three (R : C) (ha : a ∈ S) (h3 : S.ncard = 3) :
    Nonempty ((nerve (famBuilding (fun _ : PUnit.{u + 1} => S))).homology R 1 ≅ R) := by
  classical
  have h2 : 2 ≤ S.ncard := by omega
  haveI huniq := uniqueBoolCoverIndex ha h2
  haveI hne' : Nonempty (famCoverIndex (fun _ : PUnit.{u + 1} => S) (fun _ => ({a} : Set ι))) :=
    ⟨boolCoverElt ha h2⟩
  haveI := isPreconnected_boolPieces ha h2
  have hcard : (S \ {a}).ncard = 2 := by rw [Set.ncard_sdiff_singleton_of_mem ha, h3]
  obtain ⟨x, y, hxy, hpair⟩ := Set.ncard_eq_two.1 hcard
  have hxmem : x ∈ S \ {a} := by rw [hpair]; exact Or.inl rfl
  have hymem : y ∈ S \ {a} := by rw [hpair]; exact Or.inr rfl
  have hxa : x ≠ a := fun h => hxmem.2 (Set.mem_singleton_iff.2 h)
  have hya : y ≠ a := fun h => hymem.2 (Set.mem_singleton_iff.2 h)
  -- the two vertices of the intersection
  have hbot : ∀ z : ι, (⊥ : Set ι) < {z} := fun z => Set.empty_ssubset.2 ⟨z, rfl⟩
  have htop : ∀ z : ι, z ≠ a → ({z} : Set ι) < ⊤ := fun z hz =>
    Set.ssubset_univ_iff.2 fun hcon => hz (Set.mem_singleton_iff.1 (hcon ▸ Set.mem_univ a)).symm
  have hltS : ∀ z : ι, z ∈ S \ {a} → ({z} : Set ι) < S := fun z hz =>
    lt_of_le_of_ne (Set.singleton_subset_iff.2 hz.1) fun hcon =>
      hz.2 (Set.mem_singleton_iff.2 (by
        have : a ∈ ({z} : Set ι) := by rw [hcon]; exact ha
        exact (Set.mem_singleton_iff.1 this).symm))
  have hltpair : ∀ z w : ι, z ≠ w → ({z} : Set ι) < S \ {a} → True := fun _ _ _ _ => trivial
  have hx_lt : ({x} : Set ι) < S \ {a} := by
    rw [hpair]
    refine lt_of_le_of_ne (Set.singleton_subset_iff.2 (Or.inl rfl)) fun hcon => ?_
    have : y ∈ ({x} : Set ι) := by rw [hcon]; exact Or.inr rfl
    exact hxy (Set.mem_singleton_iff.1 this).symm
  have hy_lt : ({y} : Set ι) < S \ {a} := by
    rw [hpair]
    refine lt_of_le_of_ne (Set.singleton_subset_iff.2 (Or.inr rfl)) fun hcon => ?_
    have : x ∈ ({y} : Set ι) := by rw [hcon]; exact Or.inl rfl
    exact hxy (Set.mem_singleton_iff.1 this)
  set qx : famBuilding (fun _ : PUnit.{u + 1} => S) :=
    boolElt S {x} (hbot x) (htop x hxa) (hltS x hxmem) with hqx_def
  set qy : famBuilding (fun _ : PUnit.{u + 1} => S) :=
    boolElt S {y} (hbot y) (htop y hya) (hltS y hymem) with hqy_def
  -- the classification of the intersection
  have hclass : ∀ w : (((famCoverBaseSub (W := fun _ : PUnit.{u + 1} => S)
        (p := fun _ => ({a} : Set ι)) ⊓ famCoverPieceSub (boolCoverElt ha h2)) :
        (nerve (famBuilding (fun _ : PUnit.{u + 1} => S))).Subcomplex) : SSet.{u}) _⦋0⦌,
      (w.1).obj 0 = qx ∨ (w.1).obj 0 = qy := by
    intro w
    have hmem : ((w.1).obj 0) ∈ famCoverBase (fun _ : PUnit.{u + 1} => S) (fun _ => ({a} : Set ι))
        ∩ generalStar (famCoverCentre (fun _ : PUnit.{u + 1} => S) (fun _ => ({a} : Set ι))
          (boolCoverElt ha h2)) := ⟨w.2.1 0, w.2.2 0⟩
    have hlt := (mem_boolInter_iff ha h2 _).1 hmem
    rw [hpair] at hlt
    rcases eq_singleton_of_lt_pair (Set.empty_ssubset.1 ((Subtype.val ((w.1).obj 0)).2).2.1) hlt
      with h | h
    · exact Or.inl (Subtype.ext (Prod.ext (Subsingleton.elim _ _) (Subtype.ext h)))
    · exact Or.inr (Subtype.ext (Prod.ext (Subsingleton.elim _ _) (Subtype.ext h)))
  -- the two components exhaust
  have hall : ∀ z : SSet.π₀ (famSSet fun c => famCoverBaseSub (W := fun _ : PUnit.{u + 1} => S)
      (p := fun _ => ({a} : Set ι)) ⊓ famCoverPieceSub c),
      z = SSet.π₀.mk (⟨boolCoverElt ha h2, boolInterVertex ha h2 qx hx_lt⟩ :
        (famSSet fun c => famCoverBaseSub (W := fun _ : PUnit.{u + 1} => S)
          (p := fun _ => ({a} : Set ι)) ⊓ famCoverPieceSub c) _⦋0⦌)
      ∨ z = SSet.π₀.mk (⟨boolCoverElt ha h2, boolInterVertex ha h2 qy hy_lt⟩ :
        (famSSet fun c => famCoverBaseSub (W := fun _ : PUnit.{u + 1} => S)
          (p := fun _ => ({a} : Set ι)) ⊓ famCoverPieceSub c) _⦋0⦌) := by
    intro z
    obtain ⟨v, rfl⟩ := z.mk_surjective
    obtain ⟨c, w⟩ := v
    obtain rfl : c = boolCoverElt ha h2 := boolCoverIndex_eq ha h2 c
    rcases hclass w with h | h
    · refine Or.inl (congrArg SSet.π₀.mk (congrArg (Sigma.mk (boolCoverElt ha h2))
        (Subtype.ext ?_)))
      show w.1 = ComposableArrows.mk₀ qx
      exact (ComposableArrows.ext₀ rfl : w.1 = ComposableArrows.mk₀ ((w.1).obj 0)).trans
        (congrArg ComposableArrows.mk₀ h)
    · refine Or.inr (congrArg SSet.π₀.mk (congrArg (Sigma.mk (boolCoverElt ha h2))
        (Subtype.ext ?_)))
      show w.1 = ComposableArrows.mk₀ qy
      exact (ComposableArrows.ext₀ rfl : w.1 = ComposableArrows.mk₀ ((w.1).obj 0)).trans
        (congrArg ComposableArrows.mk₀ h)
  -- the two components are distinct
  have hanti : ∀ w₀ w₁ : (((famCoverBaseSub (W := fun _ : PUnit.{u + 1} => S)
        (p := fun _ => ({a} : Set ι)) ⊓ famCoverPieceSub (boolCoverElt ha h2)) :
        (nerve (famBuilding (fun _ : PUnit.{u + 1} => S))).Subcomplex) : SSet.{u}) _⦋0⦌,
      (w₀.1).obj 0 ≤ (w₁.1).obj 0 → (w₀.1).obj 0 = (w₁.1).obj 0 := by
    intro w₀ w₁ hle
    rcases hclass w₀ with h0 | h0 <;> rcases hclass w₁ with h1 | h1 <;> rw [h0, h1] at hle ⊢
    · exfalso
      have hsub : ({x} : Set ι) ≤ {y} := by
        have hle2 := (famPoset_le_iff.1 hle).2
        rw [hqx_def, hqy_def] at hle2
        exact hle2
      exact hxy (Set.mem_singleton_iff.1 (hsub (Set.mem_singleton x)))
    · exfalso
      have hsub : ({y} : Set ι) ≤ {x} := by
        have hle2 := (famPoset_le_iff.1 hle).2
        rw [hqx_def, hqy_def] at hle2
        exact hle2
      exact hxy (Set.mem_singleton_iff.1 (hsub (Set.mem_singleton y))).symm
  have hnepi : SSet.π₀.mk (X := famSSet fun c => famCoverBaseSub
        (W := fun _ : PUnit.{u + 1} => S) (p := fun _ => ({a} : Set ι)) ⊓ famCoverPieceSub c)
        ⟨boolCoverElt ha h2, boolInterVertex ha h2 qx hx_lt⟩
      ≠ SSet.π₀.mk (X := famSSet fun c => famCoverBaseSub
        (W := fun _ : PUnit.{u + 1} => S) (p := fun _ => ({a} : Set ι)) ⊓ famCoverPieceSub c)
        ⟨boolCoverElt ha h2, boolInterVertex ha h2 qy hy_lt⟩ := by
    intro hcon
    have hsig := congrArg (famSSetPi0 _) hcon
    rw [famSSetPi0_mk, famSSetPi0_mk] at hsig
    have hcomp : SSet.π₀.mk (boolInterVertex ha h2 qx hx_lt)
        = SSet.π₀.mk (boolInterVertex ha h2 qy hy_lt) := eq_of_heq (Sigma.mk.inj hsig).2
    have hq := congrArg (nerveSubAntichainPi0 hanti) hcomp
    rw [nerveSubAntichainPi0_mk, nerveSubAntichainPi0_mk] at hq
    have hq' : qx = qy := hq
    rw [hqx_def, hqy_def] at hq'
    have hset : ({x} : Set ι) = {y} :=
      congrArg (fun q : famBuilding (fun _ : PUnit.{u + 1} => S) => ((Subtype.val q).2 : Set ι)) hq'
    exact hxy (Set.mem_singleton_iff.1 (hset ▸ Set.mem_singleton x))
  -- assemble
  obtain ⟨huk⟩ := nonempty_unique_sigmaKerIndex
    (SSet.mapπ₀ (famInterPieceHom (nerve (famBuilding (fun _ : PUnit.{u + 1} => S)))
      (famCoverBaseSub (W := fun _ : PUnit.{u + 1} => S) (p := fun _ => ({a} : Set ι)))
      (famCoverPieceSub (W := fun _ : PUnit.{u + 1} => S) (p := fun _ => ({a} : Set ι)))))
    hnepi hall
  haveI := huk
  have hp : ∀ _ : PUnit.{u + 1}, IsAtom ({a} : Set ι) := fun _ => Set.isAtom_singleton a
  have hpW : ∀ _ : PUnit.{u + 1}, ({a} : Set ι) ≤ S := fun _ => Set.singleton_subset_iff.2 ha
  refine ⟨famSupHomologyIso (W := fun _ : PUnit.{u + 1} => S) (p := fun _ => ({a} : Set ι)) R 1
    ≪≫ homologyOneIsoSigmaKerIndex (nerve (famBuilding (fun _ : PUnit.{u + 1} => S))) R
      (famCoverBaseSub (W := fun _ : PUnit.{u + 1} => S) (p := fun _ => ({a} : Set ι)))
      (famCoverPieceSub (W := fun _ : PUnit.{u + 1} => S) (p := fun _ => ({a} : Set ι)))
      (fun c c' hcc => famCoverPieceSub_inter_le hp c c' hcc)
      (isZero_homology_famCoverBase hp hpW R 1 le_rfl)
      (isZero_homology_famSSet_generalStar (famCoverCentre (fun _ : PUnit.{u + 1} => S)
        (fun _ => ({a} : Set ι))) R 1 le_rfl)
      (famCoverBaseComponent hp hpW) (famCoverBaseComponent_apply hp hpW)
    ≪≫ sigmaUniqueIso R⟩

end BaseCase

section Induction

variable {C : Type c} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- **The order complex of a Boolean interval is a sphere.**  Its homology in the top degree is one
copy of the coefficients: the cover has a single piece, so the descent removes one element at a time
and ends at the three-element interval. -/
theorem nonempty_homology_iso_boolInterval (R : C) :
    ∀ (n : ℕ), 3 ≤ n → ∀ (ι : Type u) (S : Set ι), S.ncard = n →
      Nonempty ((nerve (famBuilding (fun _ : PUnit.{u + 1} => S))).homology R (n - 2) ≅ R) := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by omega)
  | succ m ih =>
      intro h3 ι S hcard
      obtain ⟨a, ha⟩ : S.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
      rcases Nat.lt_or_ge m 3 with hm | hm
      · obtain rfl : m = 2 := by omega
        exact nonempty_homology_iso_bool_three R ha hcard
      · have h2 : 2 ≤ S.ncard := by omega
        haveI := uniqueBoolCoverIndex ha h2
        have hp : ∀ _ : PUnit.{u + 1}, IsAtom ({a} : Set ι) := fun _ => Set.isAtom_singleton a
        have hpW : ∀ _ : PUnit.{u + 1}, ({a} : Set ι) ≤ S := fun _ => Set.singleton_subset_iff.2 ha
        have hrel : (ComplexShape.down ℕ).Rel (m - 1) (m - 2) := by
          show m - 2 + 1 = m - 1
          omega
        have hiso := isIso_famTopEmbedding (W := fun _ : PUnit.{u + 1} => S)
          (p := fun _ => ({a} : Set ι)) hp hpW R (m - 1) (m - 2) hrel (by omega) (by omega)
        obtain ⟨e⟩ := ih (by omega) ι (S \ {a})
          (by rw [Set.ncard_sdiff_singleton_of_mem ha, hcard]; omega)
        have hT : famCoverTop (default : famCoverIndex (fun _ : PUnit.{u + 1} => S)
            (fun _ => ({a} : Set ι))) = S \ {a} := by
          rw [boolCoverIndex_eq ha h2 default]
          exact famCoverTop_boolCoverElt ha h2
        exact ⟨@asIso _ _ _ _ _ hiso
          ≪≫ (SSet.homologyFunctor R (m - 2)).mapIso (orderIsoNerveIso
            (famBuildingUniqueOrderIso (fun c : famCoverIndex (fun _ : PUnit.{u + 1} => S)
              (fun _ => ({a} : Set ι)) => famCoverTop c) (S \ {a}) hT))
          ≪≫ e⟩

/-- **The apartment of a projective observer frame is a sphere.**  The top homology of the order
complex of the proper part of the Boolean lattice on `N` elements is one copy of the coefficients —
the fundamental class of the Coxeter sphere `S^(N-2)`. -/
theorem nonempty_homology_iso_apartment (R : C) (ι : Type u) (h3 : 3 ≤ Nat.card ι) :
    Nonempty ((nerve (properPart (Set ι))).homology R (Nat.card ι - 2) ≅ R) := by
  obtain ⟨e⟩ := nonempty_homology_iso_boolInterval R (Nat.card ι) h3 ι Set.univ (Set.ncard_univ ι)
  exact ⟨(SSet.homologyFunctor R (Nat.card ι - 2)).mapIso
    (orderIsoNerveIso (famBuildingPUnitOrderIso (L := Set ι))).symm ≪≫ e⟩

end Induction

end GaloisForLFunctions.HTGeometry
