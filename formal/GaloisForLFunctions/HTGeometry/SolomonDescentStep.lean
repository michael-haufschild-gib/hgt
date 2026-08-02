import GaloisForLFunctions.HTGeometry.LatticeFrame

/-!
# The induction step of Solomon's theorem

The connecting map of the Solomon--Tits cover is invertible above degree zero and carries the class
of an apartment whose frame contains the chosen atom to the class of its link, the apartment of the
frame with that atom removed.  Every frame of a coatom extends to such a frame, so every apartment
class one rank down is hit.

Therefore, if the apartment classes generate the homology of the family of buildings below the
coatoms, the classes of the apartments whose frame contains the chosen atom generate the homology of
the family above.  That is the induction step of Solomon's theorem: generation descends the rank.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u

section Step

variable {L : Type u} [CompleteLattice L] [IsModularLattice L] {κ : Type u} {W p : κ → L}
variable {ι : Type u} [Finite ι] {n : ℕ}
variable {C : Type u} [Category.{v} C] [Abelian C] [Limits.HasCoproducts.{u} C]

/-- The frames of the components of a family whose atom at a given place is the chosen atom of that
component. -/
def PointedFrameAt (W p : κ → L) (ι : Type u) (i₀ : ι) : Type u :=
  {Q : FrameDatum W ι // Q.frame.atom i₀ = p Q.comp}

/-- Such a frame is a pointed frame. -/
def PointedFrameAt.toPointedFrame {i₀ : ι} (Q : PointedFrameAt W p ι i₀) : PointedFrame W p ι :=
  ⟨Q.1, i₀, Q.2⟩

omit [IsModularLattice L] [Finite ι] in
@[simp] theorem PointedFrameAt.toPointedFrame_toFrameDatum {i₀ : ι}
    (Q : PointedFrameAt W p ι i₀) : Q.toPointedFrame.toFrameDatum = Q.1 := rfl

omit [IsModularLattice L] [Finite ι] in
@[simp] theorem PointedFrameAt.toPointedFrame_idx {i₀ : ι} (Q : PointedFrameAt W p ι i₀) :
    Q.toPointedFrame.idx = i₀ := rfl

/-- **The induction step**: if the apartment classes of the family of buildings below the coatoms
generate its homology, the classes of the apartments whose frame contains the chosen atom generate
the homology of the family above. -/
theorem epi_pointedFrame_classes_of_epi (hN : Nat.card ι = n + 3) (e₀ : Fin (n + 3) ≃ ι)
    (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a) [Nonempty (famCoverIndex W p)] (R : C)
    (hn : 1 ≤ n)
    (hIH : Epi (Limits.Sigma.desc (fun Q' : FrameDatum
        (fun c : famCoverIndex W p => famCoverTop c)
        ↥(Set.univ \ {e₀ (Fin.last (n + 2))} : Set ι) =>
      apartmentClassIn (restrictOrdering (rfl : e₀ (Fin.last (n + 2)) = e₀ (Fin.last (n + 2))))
        (orderHomNerveMap Q'.vertices) R))) :
    Epi (Limits.Sigma.desc (fun Q : PointedFrameAt W p ι (e₀ (Fin.last (n + 2))) =>
      apartmentClassIn e₀ (apartmentSupMap (W := W) (p := p) Q.1.vertices) R)) := by
  classical
  have hRel : (ComplexShape.down ℕ).Rel (n + 1) n := by simp
  haveI hδ := isIso_mvDelta (W := W) (p := p) R hp hpW (n + 1) n hRel (by omega) hn
  haveI hψ : IsIso (SSet.homologyMap (interToSmallerNerve (W := W) (p := p) hp) R n) := by
    haveI hii := isIso_interToSmallerNerve (W := W) (p := p) hp
    refine ⟨SSet.homologyMap (inv (interToSmallerNerve (W := W) (p := p) hp)) R n, ?_, ?_⟩
    · rw [← SSet.homologyMap_comp, IsIso.hom_inv_id, SSet.homologyMap_id]
    · rw [← SSet.homologyMap_comp, IsIso.inv_hom_id, SSet.homologyMap_id]
  haveI hcomp : IsIso ((mvFamChainShortExact (nerve (famBuilding W)) R
      (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p))
      (fun c c' hcc => famCoverPieceSub_inter_le hp c c' hcc)).δ (n + 1) n hRel
    ≫ SSet.homologyMap (interToSmallerNerve (W := W) (p := p) hp) R n) := by
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hδ hψ
  refine epi_sigmaDesc_of_epi_of_exists _ _
    ((mvFamChainShortExact (nerve (famBuilding W)) R (famCoverBaseSub (W := W) (p := p))
        (famCoverPieceSub (W := W) (p := p))
        (fun c c' hcc => famCoverPieceSub_inter_le hp c c' hcc)).δ (n + 1) n hRel
      ≫ SSet.homologyMap (interToSmallerNerve (W := W) (p := p) hp) R n) hcomp
    ((-1) ^ (n + 2) : ℤ)
    (by rw [← pow_add, show (n + 2) + (n + 2) = 2 * (n + 2) by ring, pow_mul]; norm_num)
    (fun Q' => ?_) hIH
  obtain ⟨D, hD, hcover, hatom⟩ :=
    exists_frameDatum_extend (W := W) (p := p) (i₀ := e₀ (Fin.last (n + 2))) hN hp Q'.comp Q'.frame
  refine ⟨⟨D, hD⟩, ?_⟩
  have hQ : (⟨D, e₀ (Fin.last (n + 2)), hD⟩ : PointedFrame W p ι).toFrameDatum = D := rfl
  have hclass := apartmentClassIn_comp_delta_comp D.vertices
    ((⟨D, e₀ (Fin.last (n + 2)), hD⟩ : PointedFrame W p ι).coverIndex hN) e₀ R hp
    D.strictMono_vertices rfl
    (fun U hU => PointedFrame.vertex_mem_famCoverBase ⟨D, e₀ (Fin.last (n + 2)), hD⟩ U hU)
    (PointedFrame.vertices_apartmentCoatom ⟨D, e₀ (Fin.last (n + 2)), hD⟩ hN)
  refine hclass.trans ?_
  refine congrArg (fun t => ((-1) ^ (n + 2) : ℤ) • t) ?_
  refine congrArg (fun g => apartmentClassIn
    (restrictOrdering (rfl : e₀ (Fin.last (n + 2)) = e₀ (Fin.last (n + 2)))) g R) ?_
  refine congrArg orderHomNerveMap ?_
  rw [linkOrderHom_eq_vertices ⟨D, e₀ (Fin.last (n + 2)), hD⟩ hN]
  refine FrameDatum.vertices_congr _ hcover (fun S => ?_)
  exact LatticeFrame.span_congr _ (fun j => hatom j) S

omit [IsModularLattice L] in
/-- The union of the cover is the whole order complex, so its inclusion is invertible. -/
theorem isIso_ι_famCoverSup :
    IsIso (SSet.Subcomplex.ι (famCoverSup (W := W) (p := p))) := by
  have h : famCoverSup (W := W) (p := p) = ⊤ := famCoverBaseSub_sup_iSup
  rw [h]
  exact inferInstanceAs (IsIso (SSet.Subcomplex.topIso (nerve (famBuilding W))).hom)

/-- **The induction step, in the shape the induction consumes**: the same statement about the family
below the coatoms gives the statement about the family above. -/
theorem epi_frameDatum_classes_of_epi (hN : Nat.card ι = n + 3) (e₀ : Fin (n + 3) ≃ ι)
    (hp : ∀ a, IsAtom (p a)) (hpW : ∀ a, p a ≤ W a) [Nonempty (famCoverIndex W p)] (R : C)
    (hn : 1 ≤ n)
    (hIH : Epi (Limits.Sigma.desc (fun Q' : FrameDatum
        (fun c : famCoverIndex W p => famCoverTop c)
        ↥(Set.univ \ {e₀ (Fin.last (n + 2))} : Set ι) =>
      apartmentClassIn (restrictOrdering (rfl : e₀ (Fin.last (n + 2)) = e₀ (Fin.last (n + 2))))
        (orderHomNerveMap Q'.vertices) R))) :
    Epi (Limits.Sigma.desc (fun D : FrameDatum W ι =>
      apartmentClassIn e₀ (orderHomNerveMap D.vertices) R)) := by
  haveI hi := isIso_ι_famCoverSup (W := W) (p := p)
  have hiso : IsIso (SSet.homologyMap
      (SSet.Subcomplex.ι (famCoverSup (W := W) (p := p))) R (n + 1)) := by
    refine ⟨SSet.homologyMap (inv (SSet.Subcomplex.ι (famCoverSup (W := W) (p := p)))) R (n + 1),
      ?_, ?_⟩
    · rw [← SSet.homologyMap_comp, IsIso.hom_inv_id, SSet.homologyMap_id]
    · rw [← SSet.homologyMap_comp, IsIso.inv_hom_id, SSet.homologyMap_id]
  have hpt : (fun D : FrameDatum W ι => apartmentClassIn e₀ (orderHomNerveMap D.vertices) R)
      = fun D : FrameDatum W ι => apartmentClassIn e₀ (apartmentSupMap (W := W) (p := p) D.vertices) R
        ≫ SSet.homologyMap (SSet.Subcomplex.ι (famCoverSup (W := W) (p := p))) R (n + 1) := by
    refine funext fun D => ?_
    rw [apartmentClassIn_comp_homologyMap]
    rfl
  rw [hpt]
  refine epi_sigmaDesc_comp_iso _ _ hiso ?_
  exact epi_sigmaDesc_of_epi_comp _
    (fun Q : PointedFrameAt W p ι (e₀ (Fin.last (n + 2))) => Q.1)
    (epi_pointedFrame_classes_of_epi hN e₀ hp hpW R hn hIH)

end Step

end GaloisForLFunctions.HTGeometry
