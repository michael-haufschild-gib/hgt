import GaloisForLFunctions.HTGeometry.FamilyBuildingFree
import GaloisForLFunctions.HTGeometry.PiZeroNerve
import GaloisForLFunctions.HTGeometry.BuildingVanishingSubmodule
import GaloisForLFunctions.HTGeometry.BuildingAutomorphismAction

/-!
# The Steinberg module is not zero

The freeness of the top homology of a building says nothing on its own: the empty coproduct is free.
What makes the Steinberg module a genuine representation is that its index set is inhabited, and that
comes from two facts about subspaces that a general modular lattice does not have.  A line inside a
subspace of dimension at least three has a complement there which is neither zero nor everything, so
the Solomon--Tits cover always has a piece; and a plane contains two distinct lines, so at the bottom
of the descent the intersection of the base with a piece is disconnected — which is exactly what
makes the Mayer--Vietoris kernel nonzero.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite Module

universe v u

section Lattice

variable {L : Type u} [Lattice L] [BoundedOrder L] [IsModularLattice L] [ComplementedLattice L]

/-- **Relative complements**: inside a modular complemented lattice every element of an interval has
a complement in that interval. -/
theorem exists_relative_compl {p W : L} (h : p ≤ W) : ∃ U, U ≤ W ∧ p ⊔ U = W ∧ p ⊓ U = ⊥ := by
  haveI := IsModularLattice.complementedLattice_Iic (a := W)
  obtain ⟨U, hU⟩ := exists_isCompl (⟨p, h⟩ : Set.Iic W)
  refine ⟨(U : L), U.2, ?_, ?_⟩
  · have hsup := hU.sup_eq_top
    exact congrArg Subtype.val hsup
  · have hinf := hU.inf_eq_bot
    exact congrArg Subtype.val hinf

end Lattice

section Submodule

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
/-- **A line in a subspace of dimension at least three spans it with a proper nonzero
complement.** -/
theorem exists_spanning_of_finrank {W p : Submodule K V} (hp : IsAtom p) (hpW : p ≤ W)
    (hrank : 3 ≤ finrank K W) : ∃ U : Submodule K V, ⊥ < U ∧ U < W ∧ U ⊔ p = W := by
  obtain ⟨U, hUW, hsup, hinf⟩ := exists_relative_compl hpW
  have hUbot : ⊥ < U := by
    refine lt_of_le_of_ne bot_le fun hcon => ?_
    rw [← hcon, sup_bot_eq] at hsup
    rw [← hsup, Submodule.isAtom_iff_finrank_eq_one.1 hp] at hrank
    omega
  refine ⟨U, hUbot, lt_of_le_of_ne hUW fun hcon => ?_, by rw [sup_comm]; exact hsup⟩
  rw [hcon, inf_eq_left.2 hpW] at hinf
  exact absurd hinf hp.1

omit [FiniteDimensional K V] in
/-- **A plane contains two distinct lines.** -/
theorem exists_two_atoms_of_finrank_two {X : Submodule K V} (hX : finrank K X = 2) :
    ∃ q q' : Submodule K V, IsAtom q ∧ IsAtom q' ∧ q ≠ q' ∧ q ≤ X ∧ q' ≤ X := by
  have hXbot : ⊥ < X := by
    refine lt_of_le_of_ne bot_le fun hcon => ?_
    rw [← hcon, finrank_bot] at hX
    omega
  obtain ⟨q, hq, hqX⟩ := (eq_bot_or_exists_atom_le X).resolve_left (ne_of_gt hXbot)
  obtain ⟨U, hUX, hsup, hinf⟩ := exists_relative_compl hqX
  have hUbot : ⊥ < U := by
    refine lt_of_le_of_ne bot_le fun hcon => ?_
    rw [← hcon, sup_bot_eq] at hsup
    rw [← hsup, Submodule.isAtom_iff_finrank_eq_one.1 hq] at hX
    omega
  obtain ⟨q', hq', hq'U⟩ := (eq_bot_or_exists_atom_le U).resolve_left (ne_of_gt hUbot)
  refine ⟨q, q', hq, hq', fun hcon => ?_, hqX, le_trans hq'U hUX⟩
  rw [hcon, inf_eq_left.2 hq'U] at hinf
  exact absurd hinf hq'.1

/-- **An element strictly inside a plane is a line.** -/
theorem isAtom_of_lt_finrank_two {X Y : Submodule K V} (hX : finrank K X = 2) (hbot : ⊥ < Y)
    (hlt : Y < X) : IsAtom Y := by
  refine Submodule.isAtom_iff_finrank_eq_one.2 ?_
  have h1 : finrank K Y < finrank K X := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : 0 < finrank K Y := by
    refine Nat.pos_of_ne_zero fun hcon => ?_
    have : Y = ⊥ := Submodule.finrank_eq_zero.1 hcon
    exact absurd this (ne_of_gt hbot)
  omega

end Submodule

section Cover

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {ι : Type u} {W p : ι → Submodule K V}

omit [FiniteDimensional K V] in
/-- **The cover of a family of buildings of rank at least three always has a piece.** -/
theorem nonempty_famCoverIndex_of_finrank [Nonempty ι] (hp : ∀ a, IsAtom (p a))
    (hpW : ∀ a, p a ≤ W a) (hrank : ∀ a, 3 ≤ finrank K (W a)) : Nonempty (famCoverIndex W p) := by
  obtain ⟨a⟩ := ‹Nonempty ι›
  obtain ⟨U, hUbot, hUW, hsup⟩ := exists_spanning_of_finrank (hp a) (hpW a) (hrank a)
  exact ⟨⟨(a, ⟨U, hUbot, lt_of_lt_of_le hUW le_top⟩), hUW, hsup⟩⟩

/-- The coatom of a rank-three interval is a plane. -/
theorem finrank_famCoverTop (hp : ∀ a, IsAtom (p a)) (hrank : ∀ a, finrank K (W a) = 3)
    (c : famCoverIndex W p) : finrank K (famCoverTop c : Submodule K V) = 2 := by
  have h := finrank_of_covBy (covBy_famCoverTop hp c)
  rw [hrank] at h
  omega

/-- The vertex of the intersection attached to an element strictly below the coatom of its piece. -/
def coverInterVertex (hp : ∀ a, IsAtom (p a)) (c : famCoverIndex W p) (q : famBuilding W)
    (hidx : (Subtype.val q).1 = (Subtype.val c).1)
    (hlt : ((Subtype.val q).2 : Submodule K V) < famCoverTop c) :
    (((famCoverBaseSub (W := W) (p := p) ⊓ famCoverPieceSub c) :
      (nerve (famBuilding W)).Subcomplex) : SSet.{u}) _⦋0⦌ :=
  ⟨ComposableArrows.mk₀ q, by
    have hmem : q ∈ famCoverBase W p ∩ generalStar (famCoverCentre W p c) := by
      rw [famCoverBase_inter_piece hp c]
      exact ⟨hidx, hlt⟩
    exact ⟨fun _ => hmem.1, fun _ => hmem.2⟩⟩

omit [FiniteDimensional K V] in
/-- The elements of the intersection lie strictly below the coatom of the piece. -/
theorem coverInter_lt (hp : ∀ a, IsAtom (p a)) (c : famCoverIndex W p)
    (w : (((famCoverBaseSub (W := W) (p := p) ⊓ famCoverPieceSub c) :
      (nerve (famBuilding W)).Subcomplex) : SSet.{u}) _⦋0⦌) :
    (Subtype.val ((w.1).obj 0)).1 = (Subtype.val c).1
      ∧ ((Subtype.val ((w.1).obj 0)).2 : Submodule K V) < famCoverTop c := by
  have hmem : ((w.1).obj 0) ∈ famCoverBase W p ∩ generalStar (famCoverCentre W p c) :=
    ⟨w.2.1 0, w.2.2 0⟩
  rw [famCoverBase_inter_piece hp c] at hmem
  exact hmem

/-- **At the bottom of the descent the intersection is disconnected.**  A plane contains two
distinct lines, and they lie in the same star, so the two components of the intersection they carry
have the same image in the pieces. -/
theorem exists_two_pi0_of_finrank_three (hp : ∀ a, IsAtom (p a)) (hrank : ∀ a, finrank K (W a) = 3)
    (c : famCoverIndex W p) :
    ∃ z z' : SSet.π₀ (famSSet fun d : famCoverIndex W p =>
        famCoverBaseSub (W := W) (p := p) ⊓ famCoverPieceSub d),
      z ≠ z' ∧ SSet.mapπ₀ (famInterPieceHom (nerve (famBuilding W))
          (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p))) z
        = SSet.mapπ₀ (famInterPieceHom (nerve (famBuilding W))
          (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p))) z' := by
  have h2 := finrank_famCoverTop hp hrank c
  obtain ⟨q, q', hq, hq', hqq', hqX, hq'X⟩ := exists_two_atoms_of_finrank_two h2
  -- the two lines, as elements of the disjoint union
  have hlt : ∀ {x : Submodule K V}, IsAtom x → x ≤ famCoverTop c → x < famCoverTop c := by
    intro x hx hxle
    refine lt_of_le_of_ne hxle fun hcon => ?_
    rw [← hcon, Submodule.isAtom_iff_finrank_eq_one.1 hx] at h2
    omega
  have htop : ∀ {x : Submodule K V}, x < famCoverTop c → x < ⊤ :=
    fun hx => lt_of_lt_of_le (lt_trans hx (famCoverTop_lt c)) le_top
  have hbelow : ∀ {x : Submodule K V}, x < famCoverTop c → x < W (Subtype.val c).1 :=
    fun hx => lt_trans hx (famCoverTop_lt c)
  refine ⟨SSet.π₀.mk (X := famSSet fun d : famCoverIndex W p =>
      famCoverBaseSub (W := W) (p := p) ⊓ famCoverPieceSub d)
      ⟨c, coverInterVertex hp c ⟨((Subtype.val c).1, ⟨q, hq.1.bot_lt, htop (hlt hq hqX)⟩),
        hbelow (hlt hq hqX)⟩ rfl (hlt hq hqX)⟩,
    SSet.π₀.mk (X := famSSet fun d : famCoverIndex W p =>
      famCoverBaseSub (W := W) (p := p) ⊓ famCoverPieceSub d)
      ⟨c, coverInterVertex hp c ⟨((Subtype.val c).1, ⟨q', hq'.1.bot_lt, htop (hlt hq' hq'X)⟩),
        hbelow (hlt hq' hq'X)⟩ rfl (hlt hq' hq'X)⟩, ?_, ?_⟩
  · -- distinct
    intro hcon
    have hanti : ∀ w₀ w₁ : (((famCoverBaseSub (W := W) (p := p) ⊓ famCoverPieceSub c) :
        (nerve (famBuilding W)).Subcomplex) : SSet.{u}) _⦋0⦌,
        (w₀.1).obj 0 ≤ (w₁.1).obj 0 → (w₀.1).obj 0 = (w₁.1).obj 0 := by
      intro w₀ w₁ hle
      obtain ⟨hidx₀, hlt₀⟩ := coverInter_lt hp c w₀
      obtain ⟨hidx₁, hlt₁⟩ := coverInter_lt hp c w₁
      have ha₀ : IsAtom ((Subtype.val ((w₀.1).obj 0)).2 : Submodule K V) :=
        isAtom_of_lt_finrank_two h2 (Subtype.val ((w₀.1).obj 0)).2.2.1 hlt₀
      have ha₁ : IsAtom ((Subtype.val ((w₁.1).obj 0)).2 : Submodule K V) :=
        isAtom_of_lt_finrank_two h2 (Subtype.val ((w₁.1).obj 0)).2.2.1 hlt₁
      refine Subtype.ext (Prod.ext (hidx₀.trans hidx₁.symm) (Subtype.ext ?_))
      have hle' : ((Subtype.val ((w₀.1).obj 0)).2 : Submodule K V)
          ≤ ((Subtype.val ((w₁.1).obj 0)).2 : Submodule K V) := (famPoset_le_iff.1 hle).2
      exact (ha₁.le_iff.1 hle').resolve_left ha₀.1
    have hsig := congrArg (famSSetPi0 _) hcon
    rw [famSSetPi0_mk, famSSetPi0_mk] at hsig
    have hcomp := eq_of_heq (Sigma.mk.inj hsig).2
    have hval := congrArg (nerveSubAntichainPi0 hanti) hcomp
    rw [nerveSubAntichainPi0_mk, nerveSubAntichainPi0_mk] at hval
    exact hqq' (congrArg (fun x : famBuilding W => ((Subtype.val x).2 : Submodule K V)) hval)
  · -- same image
    haveI : SSet.IsPreconnected ((famCoverPieceSub (W := W) (p := p) c :
        (nerve (famBuilding W)).Subcomplex) : SSet.{u}) :=
      isPreconnected_nerveSubcomplex_of_cone (Or.inl le_rfl) fun _ hq => hq
    have key : ∀ y y' : ((famCoverPieceSub (W := W) (p := p) c :
        (nerve (famBuilding W)).Subcomplex) : SSet.{u}) _⦋0⦌,
        SSet.π₀.mk (X := famSSet (famCoverPieceSub (W := W) (p := p))) ⟨c, y⟩
          = SSet.π₀.mk (X := famSSet (famCoverPieceSub (W := W) (p := p))) ⟨c, y'⟩ := by
      intro y y'
      rw [← mapπ₀_famSSetIncl (famCoverPieceSub (W := W) (p := p)) c y,
        ← mapπ₀_famSSetIncl (famCoverPieceSub (W := W) (p := p)) c y']
      exact congrArg _ (Subsingleton.elim _ _)
    exact key _ _

end Cover

section Induction

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- **The homology of a family of buildings of rank `i + 2` is free on a nonempty index.**  The
descent removes one rank per degree, and at the bottom the intersection of the base with a piece has
two components, so the Mayer--Vietoris kernel is a coproduct over a nonempty set. -/
theorem exists_nonempty_index_homology_famBuilding (R : C) :
    ∀ (i : ℕ), 1 ≤ i → ∀ (ι : Type u) (W : ι → Submodule K V), Nonempty ι →
      (∀ a, finrank K (W a) = i + 2) →
      ∃ B : Type u, Nonempty B ∧
        Nonempty ((nerve (famBuilding W)).homology R i ≅ ∐ fun _ : B => R) := by
  classical
  intro i
  induction i with
  | zero => intro h; exact absurd h (by omega)
  | succ n ih =>
      intro _ ι W hne hrank
      have hbot : ∀ a, ⊥ < W a := by
        intro a
        refine lt_of_le_of_ne bot_le fun hcon => ?_
        have hr := hrank a
        rw [← hcon, finrank_bot] at hr
        omega
      choose p hp hpW using fun a =>
        (eq_bot_or_exists_atom_le (W a)).resolve_left (ne_of_gt (hbot a))
      haveI hne' : Nonempty (famCoverIndex W p) :=
        nonempty_famCoverIndex_of_finrank hp hpW fun a => by have := hrank a; omega
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have c : famCoverIndex W p := hne'.some
        obtain ⟨z, z', hzz', himg⟩ :=
          exists_two_pi0_of_finrank_three hp (fun a => by have := hrank a; omega) c
        refine ⟨sigmaKerIndex (SSet.mapπ₀ (famInterPieceHom (nerve (famBuilding W))
            (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p)))),
          nonempty_sigmaKerIndex_of_ne _ hzz' himg, ⟨?_⟩⟩
        exact famSupHomologyIso (W := W) (p := p) R 1
          ≪≫ homologyOneIsoSigmaKerIndex (nerve (famBuilding W)) R
            (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p))
            (fun c c' hcc => famCoverPieceSub_inter_le hp c c' hcc)
            (isZero_homology_famCoverBase hp hpW R 1 le_rfl)
            (isZero_homology_famSSet_generalStar (famCoverCentre W p) R 1 le_rfl)
            (famCoverBaseComponent hp hpW) (famCoverBaseComponent_apply hp hpW)
      · obtain ⟨B, hB, ⟨e⟩⟩ := ih (by omega) (famCoverIndex W p)
          (fun c : famCoverIndex W p => famCoverTop c) hne' fun c => by
            have h1 := finrank_of_covBy (covBy_famCoverTop hp c)
            have h2 := hrank (Subtype.val c).1
            omega
        haveI := isIso_famTopEmbedding (W := W) (p := p) hp hpW R (n + 1) n rfl (by omega) hn
        exact ⟨B, hB, ⟨asIso (famTopEmbedding (W := W) (p := p) hp R (n + 1) n rfl) ≪≫ e⟩⟩

/-- **The Steinberg module is a coproduct over a nonempty index set.** -/
theorem exists_nonempty_index_steinbergModule (R : C) (h3 : 3 ≤ finrank K V) :
    ∃ B : Type u, Nonempty B ∧ Nonempty (steinbergModule K V R ≅ ∐ fun _ : B => R) := by
  obtain ⟨B, hB, ⟨e⟩⟩ := exists_nonempty_index_homology_famBuilding R (finrank K V - 2)
    (by omega) PUnit.{u + 1} (fun _ => (⊤ : Submodule K V)) ⟨PUnit.unit⟩ (fun _ => by
      rw [finrank_top]
      omega)
  exact ⟨B, hB, ⟨(SSet.homologyFunctor R (finrank K V - 2)).mapIso
    (orderIsoNerveIso (famBuildingPUnitOrderIso (L := Submodule K V))).symm ≪≫ e⟩⟩

/-- **The Steinberg module is not zero.**  For a space of dimension at least three the building
carries a nonzero top homology class, with any nonzero coefficients: it is not contractible. -/
theorem not_isZero_steinbergModule (R : C) (hR : ¬ Limits.IsZero R) (h3 : 3 ≤ finrank K V) :
    ¬ Limits.IsZero (steinbergModule K V R) := by
  intro hzero
  obtain ⟨B, ⟨b⟩, ⟨e⟩⟩ := exists_nonempty_index_steinbergModule R h3
  refine hR ?_
  have hsigma : Limits.IsZero (∐ fun _ : B => R) := Limits.IsZero.of_iso hzero e.symm
  rw [Limits.IsZero.iff_id_eq_zero]
  have hsplit : Sigma.ι (fun _ : B => R) b ≫ Sigma.desc (fun _ => 𝟙 R) = 𝟙 R := Sigma.ι_desc _ _
  rw [← hsplit, hsigma.eq_zero_of_tgt (Sigma.ι (fun _ : B => R) b), Limits.zero_comp]

end Induction

end GaloisForLFunctions.HTGeometry
