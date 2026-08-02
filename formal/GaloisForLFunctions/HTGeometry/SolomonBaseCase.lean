import GaloisForLFunctions.HTGeometry.PairFrame
import GaloisForLFunctions.HTGeometry.SolomonFrameRank
import GaloisForLFunctions.HTGeometry.FamilyBuildingFree
import GaloisForLFunctions.HTGeometry.SolomonInduction

/-!
# Solomon's theorem in the smallest rank

In the smallest rank the Solomon--Tits descent lands in degree zero, where the base and the pieces
still have homology, so the connecting map is only injective.  What replaces invertibility is
exactness: the connecting map identifies the first homology of the union with the kernel of the map
induced in degree zero by the inclusion of the intersections into the pieces, and that kernel is a
coproduct of copies of the coefficients on the differences of a component with its chosen
representative.

Those differences are apartment classes: the buildings below the coatoms are, in this rank,
antichains of atoms, so a difference of two of them is the class of the apartment of the two-atom
frame they form, and that frame extends to a frame above.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite Module

universe v u

section Atoms

variable {K V : Type u} [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **A nonzero proper subspace of a plane is a line.** -/
theorem isAtom_of_lt_of_finrank_two {x T : Submodule K V} (hbot : ⊥ < x) (hlt : x < T)
    (hT : finrank K ↥T = 2) : IsAtom x := by
  refine Submodule.isAtom_iff_finrank_eq_one.2 ?_
  have h1 : 0 < finrank K ↥x := by
    rcases Nat.eq_zero_or_pos (finrank K ↥x) with h | h
    · exact absurd (Submodule.finrank_eq_zero.1 h) (ne_of_gt hbot)
    · exact h
  have h2 : finrank K ↥x < finrank K ↥T := Submodule.finrank_lt_finrank_of_lt hlt
  omega

/-- **Two distinct lines of a plane are disjoint and span it.** -/
theorem pair_of_atoms_of_finrank_two {x y T : Submodule K V} (hx : IsAtom x) (hy : IsAtom y)
    (hne : x ≠ y) (hxT : x ≤ T) (hyT : y ≤ T) (hT : finrank K ↥T = 2) :
    Disjoint x y ∧ x ⊔ y = T := by
  have hdisj : Disjoint x y := by
    refine disjoint_iff.2 ?_
    rcases (IsAtom.le_iff hx (x := x ⊓ y)).1 inf_le_left with h | h
    · exact h
    · have hxy : x ≤ y := h ▸ inf_le_right
      rcases (IsAtom.le_iff hy (x := x)).1 hxy with h0 | h0
      · exact absurd h0 hx.1
      · exact absurd h0 hne
  refine ⟨hdisj, ?_⟩
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq x y
  rw [disjoint_iff.1 hdisj, finrank_bot, add_zero,
    Submodule.isAtom_iff_finrank_eq_one.1 hx, Submodule.isAtom_iff_finrank_eq_one.1 hy] at hsum
  exact Submodule.eq_of_le_of_finrank_eq (sup_le hxT hyT) (by rw [hsum, hT])

end Atoms

/-! ## Components of the intersections -/

section General

variable {X : SSet.{u}} {ιx : Type u} (A₀ : X.Subcomplex) (A : ιx → X.Subcomplex)

/-- **Two intersection vertices in the same component of the pieces lie over the same piece.** -/
theorem famInter_index_eq_of_pi0_eq {v v' : (famSSet (fun a => A₀ ⊓ A a)) _⦋0⦌}
    (h : SSet.mapπ₀ (famInterPieceHom X A₀ A) (SSet.π₀.mk v)
      = SSet.mapπ₀ (famInterPieceHom X A₀ A) (SSet.π₀.mk v')) : v.1 = v'.1 := by
  have h2 := congrArg (famSSetPi0 A) h
  rw [SSet.mapπ₀_mk, SSet.mapπ₀_mk, famSSetPi0_mk, famSSetPi0_mk] at h2
  have h3 := congrArg (fun z : Σ a, SSet.π₀ (A a : SSet.{u}) => z.1) h2
  exact h3

end General

/-! ## The base case -/

section Base

variable {K V : Type u} [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {κ : Type u} {W p : κ → Submodule K V} {ι : Type u} [Finite ι]
variable {C : Type u} [Category.{v} C] [Abelian C] [Limits.HasCoproducts.{u} C]

omit [FiniteDimensional K V] in
/-- The two vertices of an intersection simplex, as elements of the disjoint union. -/
theorem inter_vertex_lt (hp : ∀ a, IsAtom (p a))
    (v : (famSSet (fun c : famCoverIndex W p => famCoverBaseSub (W := W) (p := p)
      ⊓ famCoverPieceSub (W := W) (p := p) c)) _⦋0⦌) :
    (Subtype.val (((v.2 : (nerve (famBuilding W)) _⦋0⦌)).obj 0)).2.1 < famCoverTop v.1 := by
  have hmem : ((v.2 : (nerve (famBuilding W)) _⦋0⦌)).obj 0
      ∈ famCoverBase W p ∩ generalStar (famCoverCentre W p v.1) := ⟨v.2.2.1 0, v.2.2.2 0⟩
  exact ((mem_famCoverInter hp).1 hmem).2

omit [FiniteDimensional K V] in
/-- A zero-simplex of an intersection is determined by its vertex. -/
theorem inter_simplex_ext
    {v v' : (famSSet (fun c : famCoverIndex W p => famCoverBaseSub (W := W) (p := p)
      ⊓ famCoverPieceSub (W := W) (p := p) c)) _⦋0⦌} (hidx : v.1 = v'.1)
    (hobj : ((v.2 : (nerve (famBuilding W)) _⦋0⦌)).obj 0
      = ((v'.2 : (nerve (famBuilding W)) _⦋0⦌)).obj 0) : v = v' := by
  obtain ⟨c, χ⟩ := v
  obtain ⟨c', χ'⟩ := v'
  simp only at hidx hobj
  subst hidx
  refine congrArg (Sigma.mk c) (Subtype.ext (nerve_simplex_ext fun j => ?_))
  have hj : j = 0 := Fin.ext (by
    have h1 : ((unop (op ⦋0⦌)).len) = 0 := rfl
    have h2 := j.isLt
    omega)
  rw [hj]
  exact hobj

set_option maxHeartbeats 4000000 in
/-- **Solomon's theorem in the smallest rank**, for the frames containing the chosen atom. -/
theorem epi_pointedFrame_classes_base (hN : Nat.card ι = 0 + 3) (e₀ : Fin (0 + 3) ≃ ι)
    (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a) [Nonempty (famCoverIndex W p)]
    (hrank : ∀ a, finrank K ↥(W a) = 0 + 3) (R : C) :
    Epi (Limits.Sigma.desc (fun Q : PointedFrameAt W p ι (e₀ (Fin.last (0 + 2))) =>
      apartmentClassIn e₀ (apartmentSupMap (W := W) (p := p) Q.1.vertices) R)) := by
  classical
  have hRel : (ComplexShape.down ℕ).Rel 1 0 := by simp
  have hS := mvFamChainShortExact (nerve (famBuilding W)) R (famCoverBaseSub (W := W) (p := p))
    (famCoverPieceSub (W := W) (p := p)) (fun c c' hcc => famCoverPieceSub_inter_le hp c c' hcc)
  have hmid : Limits.IsZero
      (((((famCoverBaseSub (W := W) (p := p) :
          (nerve (famBuilding W)).Subcomplex) : SSet.{u}).chainComplex R)
        ⊞ ((famSSet (famCoverPieceSub (W := W) (p := p))).chainComplex R)).homology 1) :=
    isZero_homology_biprod _ _ 1 (isZero_homology_famCoverBase hp hpW R 1 le_rfl)
      (isZero_homology_famSSet_generalStar (famCoverCentre W p) R 1 le_rfl)
  haveI hmono : Mono (hS.δ 1 0 hRel) :=
    (hS.homology_exact₃ 1 0 hRel).mono_g (hmid.eq_zero_of_src _)
  have hker := (hS.homology_exact₁ 1 0 hRel).fIsKernel
  haveI := mono_famBiprodSection (nerve (famBuilding W)) R (famCoverBaseSub (W := W) (p := p))
    (famCoverPieceSub (W := W) (p := p)) (famCoverBaseComponent hp hpW)
  have hker2 := isKernelOfCompMono
    (SSet.homologyMap (famInterPieceHom (nerve (famBuilding W))
      (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p))) R 0)
    (famBiprodSection (nerve (famBuilding W)) R (famCoverBaseSub (W := W) (p := p))
      (famCoverPieceSub (W := W) (p := p)) (famCoverBaseComponent hp hpW))
    (mvFamChainFst_homology_zero_eq (nerve (famBuilding W)) R (famCoverBaseSub (W := W) (p := p))
      (famCoverPieceSub (W := W) (p := p)) (famCoverBaseComponent hp hpW)
      (famCoverBaseComponent_apply hp hpW)) hker
  have hw : hS.δ 1 0 hRel ≫ SSet.homologyMap (famInterPieceHom (nerve (famBuilding W))
      (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p))) R 0 = 0 :=
    zero_of_comp_mono (famBiprodSection (nerve (famBuilding W)) R
      (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p))
      (famCoverBaseComponent hp hpW))
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => hS.δ 1 0 hRel ≫ t)
          (mvFamChainFst_homology_zero_eq (nerve (famBuilding W)) R
            (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p))
            (famCoverBaseComponent hp hpW) (famCoverBaseComponent_apply hp hpW))).trans
          (hS.δ_comp 1 0 hRel)))
  have hkerδ : IsLimit (KernelFork.ofι (hS.δ 1 0 hRel) hw) := hker2
  refine epi_sigmaDesc_of_epi_of_exists _
    (fun k : sigmaKerIndex (SSet.mapπ₀ (famInterPieceHom (nerve (famBuilding W))
      (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p)))) =>
      Limits.Sigma.ι (fun _ => R) k)
    (kernelIsoSigmaKerIndexHomologyZero R (famInterPieceHom (nerve (famBuilding W))
      (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p)))
      (hS.δ 1 0 hRel) hw hkerδ).hom
    (Iso.isIso_hom _) 1 (by norm_num) (fun k => ?_) ?_
  · obtain ⟨v, hv⟩ := (k : SSet.π₀ (famSSet (fun c : famCoverIndex W p =>
      famCoverBaseSub (W := W) (p := p) ⊓ famCoverPieceSub (W := W) (p := p) c))).mk_surjective
    obtain ⟨v', hv'⟩ := (sigmaSection (SSet.mapπ₀ (famInterPieceHom (nerve (famBuilding W))
      (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p))))
        (k : SSet.π₀ _)).mk_surjective
    have hidx : v'.1 = v.1 :=
      famInter_index_eq_of_pi0_eq _ _ (by rw [hv, hv']; exact u_sigmaSection _)
    -- the two vertices of the intersections, and their properties
    have hrank2 : finrank K ↥(famCoverTop v.1) = 2 := by
      have h := finrank_famCoverTop_succ hp v.1
      rw [hrank (Subtype.val v.1).1] at h
      omega
    have hqlt := inter_vertex_lt hp v
    have hq'lt := lt_of_lt_of_eq (inter_vertex_lt hp v') (congrArg famCoverTop hidx)
    have hx : IsAtom ((Subtype.val ((v.2 : (nerve (famBuilding W)) _⦋0⦌).obj 0)).2 :
        properPart (Submodule K V)).1 :=
      isAtom_of_lt_of_finrank_two
        ((Subtype.val ((v.2 : (nerve (famBuilding W)) _⦋0⦌).obj 0)).2).2.1 hqlt hrank2
    have hy : IsAtom ((Subtype.val ((v'.2 : (nerve (famBuilding W)) _⦋0⦌).obj 0)).2 :
        properPart (Submodule K V)).1 :=
      isAtom_of_lt_of_finrank_two
        ((Subtype.val ((v'.2 : (nerve (famBuilding W)) _⦋0⦌).obj 0)).2).2.1 hq'lt hrank2
    have hvne : ((Subtype.val ((v.2 : (nerve (famBuilding W)) _⦋0⦌).obj 0)).2 :
          properPart (Submodule K V)).1
        ≠ ((Subtype.val ((v'.2 : (nerve (famBuilding W)) _⦋0⦌).obj 0)).2 :
          properPart (Submodule K V)).1 := by
      intro hcon
      have hidxq : (Subtype.val ((v.2 : (nerve (famBuilding W)) _⦋0⦌).obj 0)).1
          = (Subtype.val ((v'.2 : (nerve (famBuilding W)) _⦋0⦌).obj 0)).1 := by
        have h1 := (mem_generalStar_famCoverCentre.1 (v.2.2.2 0)).1
        have h2 := (mem_generalStar_famCoverCentre.1 (v'.2.2.2 0)).1
        rw [h1, h2, hidx]
      have hobj : ((v.2 : (nerve (famBuilding W)) _⦋0⦌).obj 0)
          = ((v'.2 : (nerve (famBuilding W)) _⦋0⦌).obj 0) :=
        Subtype.ext (Prod.ext hidxq (Subtype.ext hcon))
      have hvv : v = v' := inter_simplex_ext hidx.symm hobj
      refine k.2 ?_
      rw [← hv', ← hv, hvv]
    obtain ⟨hxy, hsup⟩ := pair_of_atoms_of_finrank_two hx hy hvne (le_of_lt hqlt) (le_of_lt hq'lt)
      hrank2
    obtain ⟨D, hD, hcover, hatom⟩ := exists_frameDatum_extend
      (W := W) (p := p) (i₀ := e₀ (Fin.last (0 + 2))) hN hp v.1
      (LatticeFrame.pair (restrictOrdering (rfl : e₀ (Fin.last (0 + 2)) = e₀ (Fin.last (0 + 2))))
        hx hy hxy hsup)
    refine ⟨⟨D, hD⟩, ?_⟩
    have hclass := apartmentClassIn_comp_delta D.vertices
      ((⟨D, e₀ (Fin.last (0 + 2)), hD⟩ : PointedFrame W p ι).coverIndex hN) e₀ R hp rfl
      (fun U hU => PointedFrame.vertex_mem_famCoverBase ⟨D, e₀ (Fin.last (0 + 2)), hD⟩ U hU)
      (PointedFrame.vertices_apartmentCoatom ⟨D, e₀ (Fin.last (0 + 2)), hD⟩ hN)
    have hcomp : D.comp = (Subtype.val ((v.2 : (nerve (famBuilding W)) _⦋0⦌).obj 0)).1 := by
      have h1 : D.comp = (Subtype.val v.1).1 :=
        congrArg (fun c : famCoverIndex W p => (Subtype.val c).1) hcover
      rw [h1, (mem_generalStar_famCoverCentre.1 (v.2.2.2 0)).1]
    have hcomp' : D.comp = (Subtype.val ((v'.2 : (nerve (famBuilding W)) _⦋0⦌).obj 0)).1 := by
      have h1 : D.comp = (Subtype.val v.1).1 :=
        congrArg (fun c : famCoverIndex W p => (Subtype.val c).1) hcover
      rw [h1, (mem_generalStar_famCoverCentre.1 (v'.2.2.2 0)).1, hidx]
    have hspan0 : D.frame.span (Subtype.val ''
          ((chainOfOrdering (restrictOrdering
            (rfl : e₀ (Fin.last (0 + 2)) = e₀ (Fin.last (0 + 2)))) 0 :
              properPart (Set ↥(Set.univ \ {e₀ (Fin.last (0 + 2))} : Set ι))) :
            Set ↥(Set.univ \ {e₀ (Fin.last (0 + 2))} : Set ι)))
        = ((Subtype.val ((v.2 : (nerve (famBuilding W)) _⦋0⦌).obj 0)).2 :
            properPart (Submodule K V)).1 := by
      rw [show ((chainOfOrdering (restrictOrdering
          (rfl : e₀ (Fin.last (0 + 2)) = e₀ (Fin.last (0 + 2)))) 0 :
            properPart (Set ↥(Set.univ \ {e₀ (Fin.last (0 + 2))} : Set ι))) :
          Set ↥(Set.univ \ {e₀ (Fin.last (0 + 2))} : Set ι))
        = {restrictOrdering (rfl : e₀ (Fin.last (0 + 2)) = e₀ (Fin.last (0 + 2))) 0} from
          initialSegSet_zero _, Set.image_singleton, LatticeFrame.span_singleton,
        hatom (restrictOrdering (rfl : e₀ (Fin.last (0 + 2)) = e₀ (Fin.last (0 + 2))) 0),
        LatticeFrame.pair_atom, pairAtom_zero]
    have hspan1 : D.frame.span (Subtype.val ''
          ((chainOfOrdering ((Equiv.swap 0 1).trans (restrictOrdering
            (rfl : e₀ (Fin.last (0 + 2)) = e₀ (Fin.last (0 + 2))))) 0 :
              properPart (Set ↥(Set.univ \ {e₀ (Fin.last (0 + 2))} : Set ι))) :
            Set ↥(Set.univ \ {e₀ (Fin.last (0 + 2))} : Set ι)))
        = ((Subtype.val ((v'.2 : (nerve (famBuilding W)) _⦋0⦌).obj 0)).2 :
            properPart (Submodule K V)).1 := by
      rw [show ((chainOfOrdering ((Equiv.swap 0 1).trans (restrictOrdering
          (rfl : e₀ (Fin.last (0 + 2)) = e₀ (Fin.last (0 + 2))))) 0 :
            properPart (Set ↥(Set.univ \ {e₀ (Fin.last (0 + 2))} : Set ι))) :
          Set ↥(Set.univ \ {e₀ (Fin.last (0 + 2))} : Set ι))
        = {((Equiv.swap 0 1).trans (restrictOrdering
            (rfl : e₀ (Fin.last (0 + 2)) = e₀ (Fin.last (0 + 2))))) 0} from initialSegSet_zero _,
        show ((Equiv.swap 0 1).trans (restrictOrdering
            (rfl : e₀ (Fin.last (0 + 2)) = e₀ (Fin.last (0 + 2))))) 0
          = restrictOrdering (rfl : e₀ (Fin.last (0 + 2)) = e₀ (Fin.last (0 + 2))) 1 from by
          rw [Equiv.trans_apply, Equiv.swap_apply_left],
        Set.image_singleton, LatticeFrame.span_singleton,
        hatom (restrictOrdering (rfl : e₀ (Fin.last (0 + 2)) = e₀ (Fin.last (0 + 2))) 1),
        LatticeFrame.pair_atom, pairAtom_one _ _ _ (by decide)]
    have hvert0 : (linkInterMap D.vertices
          ((⟨D, e₀ (Fin.last (0 + 2)), hD⟩ : PointedFrame W p ι).coverIndex hN)
          (fun U hU => PointedFrame.vertex_mem_famCoverBase ⟨D, e₀ (Fin.last (0 + 2)), hD⟩ U hU)
          (PointedFrame.vertices_apartmentCoatom ⟨D, e₀ (Fin.last (0 + 2)), hD⟩ hN)
        ≫ famSSetIncl (fun c' => famCoverBaseSub (W := W) (p := p)
            ⊓ famCoverPieceSub (W := W) (p := p) c')
          ((⟨D, e₀ (Fin.last (0 + 2)), hD⟩ : PointedFrame W p ι).coverIndex hN)).app (op ⦋0⦌)
        (apartmentChainSimplex (restrictOrdering
          (rfl : e₀ (Fin.last (0 + 2)) = e₀ (Fin.last (0 + 2))))) = v :=
      inter_simplex_ext hcover (Subtype.ext (Prod.ext hcomp (Subtype.ext hspan0)))
    have hvert1 : (linkInterMap D.vertices
          ((⟨D, e₀ (Fin.last (0 + 2)), hD⟩ : PointedFrame W p ι).coverIndex hN)
          (fun U hU => PointedFrame.vertex_mem_famCoverBase ⟨D, e₀ (Fin.last (0 + 2)), hD⟩ U hU)
          (PointedFrame.vertices_apartmentCoatom ⟨D, e₀ (Fin.last (0 + 2)), hD⟩ hN)
        ≫ famSSetIncl (fun c' => famCoverBaseSub (W := W) (p := p)
            ⊓ famCoverPieceSub (W := W) (p := p) c')
          ((⟨D, e₀ (Fin.last (0 + 2)), hD⟩ : PointedFrame W p ι).coverIndex hN)).app (op ⦋0⦌)
        (apartmentChainSimplex ((Equiv.swap 0 1).trans (restrictOrdering
          (rfl : e₀ (Fin.last (0 + 2)) = e₀ (Fin.last (0 + 2)))))) = v' :=
      inter_simplex_ext (hcover.trans hidx.symm)
        (Subtype.ext (Prod.ext hcomp' (Subtype.ext hspan1)))
    have hstep := kernelIsoSigmaKerIndexHomologyZero_inv_comp R
      (famInterPieceHom (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
        (famCoverPieceSub (W := W) (p := p))) _ _ hkerδ
    rw [one_smul, ← Iso.eq_comp_inv]
    refine Fork.IsLimit.hom_ext hkerδ ?_
    rw [Limits.KernelFork.ι_ofι]
    refine hclass.trans ?_
    refine (cancel_mono ((famSSet (fun c' => famCoverBaseSub (W := W) (p := p)
      ⊓ famCoverPieceSub (W := W) (p := p) c')).homology₀Iso R).hom).1 ?_
    simp only [show ((-1 : ℤ) ^ (0 + 2)) = 1 from by norm_num, one_smul]
    rw [apartmentClassIn_zero_comp_homology₀Iso, hvert0, hvert1, hv, hv']
    dsimp only [mvFamChainShortComplex]
    rw [← ι_sigmaKerIncl _ R k, Category.assoc]
    exact (congrArg (fun t => Limits.Sigma.ι
      (fun _ : sigmaKerIndex (SSet.mapπ₀ (famInterPieceHom (nerve (famBuilding W))
        (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p)))) => R) k ≫ t)
      hstep.symm).trans (Category.assoc _ _ _).symm
  · have hid : Limits.Sigma.desc (fun k : sigmaKerIndex (SSet.mapπ₀
        (famInterPieceHom (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
          (famCoverPieceSub (W := W) (p := p)))) => Limits.Sigma.ι (fun _ => R) k) = 𝟙 _ :=
      Limits.Sigma.hom_ext _ _ (fun k => by rw [Limits.Sigma.ι_desc, Category.comp_id])
    rw [hid]
    infer_instance

/-- **Solomon's theorem in the smallest rank**, in the form the induction starts from. -/
theorem solomonBase : SolomonBase.{v} K V C := by
  intro κ hκ W ι hι hN e₀ hrank R
  classical
  haveI := hι
  haveI := hκ
  have hframe : ∀ a : κ, Nonempty (LatticeFrame (Submodule K V) ι (W a)) := fun a =>
    nonempty_frame_of_finrank (by rw [hN, hrank a])
  set p : κ → Submodule K V := fun a => (hframe a).some.atom (e₀ (Fin.last (0 + 2))) with hpdef
  have hp : ∀ a, IsAtom (p a) := fun a => (hframe a).some.isAtom _
  have hpW : ∀ a, p a ≤ W a := fun a => (hframe a).some.atom_le_top _
  haveI : Nonempty (famCoverIndex W p) := by
    obtain ⟨a⟩ := hκ
    exact ⟨(⟨⟨a, (hframe a).some⟩, e₀ (Fin.last (0 + 2)), rfl⟩ :
      PointedFrame W p ι).coverIndex hN⟩
  exact epi_frameDatum_classes_of_epi_pointed e₀ R
    (epi_pointedFrame_classes_base hN e₀ hp hpW hrank R)

/-- **Solomon's theorem**: for a family of subspaces of one dimension, the apartment classes of the
frames of the components generate the homology of the disjoint union of their buildings, in the
degree that dimension gives.  Unconditional. -/
theorem epi_frameDatum_classes_solomon (m : ℕ) (κ : Type u) (hκ : Nonempty κ)
    (W : κ → Submodule K V) (ι : Type u) (hι : Finite ι) (hN : Nat.card ι = m + 3)
    (e₀ : Fin (m + 3) ≃ ι) (hrank : ∀ a, finrank K ↥(W a) = m + 3) (R : C) :
    Epi (Limits.Sigma.desc (fun D : FrameDatum W ι =>
      apartmentClassIn e₀ (orderHomNerveMap D.vertices) R)) :=
  epi_frameDatum_classes solomonBase m κ hκ W ι hι hN e₀ hrank R

end Base

end GaloisForLFunctions.HTGeometry
