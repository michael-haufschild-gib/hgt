import GaloisForLFunctions.RHTower.Deninger.DeningerSectionHasse
import GaloisForLFunctions.RHTower.Deninger.DeningerCellFiltration

/-!
# Hasse quotients for Deninger cell filtrations

When the initial stage and graded pieces are acyclic, every graded section is realized by a section
of the next filtration stage, uniquely modulo a section of the previous stage.  Thus the filtration
on global sections has the same successive quotients as the sheaf filtration.  A specialization
records the relative free-cell attachment on a punctured complex character stage.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite TopCat

noncomputable section

universe w u

variable {X : TopCat.{u}} [CategoryTheory.HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]
  {F G : ℕ → TopCat.Sheaf AddCommGrpCat.{u} X} {f : ∀ i, F i ⟶ F (i + 1)}
  {g : ∀ i, F (i + 1) ⟶ G i} {hzero : ∀ i, f i ≫ g i = 0}

/-- Each graded piece is the next-stage section group modulo previous-stage sections. -/
noncomputable def deningerFiltrationSectionsHasseQuotientEquiv
    (hSE : ∀ i, (deningerFiltrationStep f g hzero i).ShortExact) (U : Opens X)
    (h0 : DeningerAcyclicOn.{w} (F 0) U) (hgr : ∀ i, DeningerAcyclicOn.{w} (G i) U)
    (i : ℕ) :
    (ToType ((F (i + 1)).1.obj (op U)) ⧸ (deningerSectionAddHom (f i) U).range) ≃+
      ToType ((G i).1.obj (op U)) :=
  deningerAcyclicSectionsHasseQuotientEquiv (hSE i) U
    (deningerAcyclicOn_of_filtration hSE U h0 hgr i)

/-- The filtration Hasse equivalence is induced by projection to the graded piece. -/
@[simp] theorem deningerFiltrationSectionsHasseQuotientEquiv_mk
    (hSE : ∀ i, (deningerFiltrationStep f g hzero i).ShortExact) (U : Opens X)
    (h0 : DeningerAcyclicOn.{w} (F 0) U) (hgr : ∀ i, DeningerAcyclicOn.{w} (G i) U)
    (i : ℕ) (x : ToType ((F (i + 1)).1.obj (op U))) :
    deningerFiltrationSectionsHasseQuotientEquiv hSE U h0 hgr i
      (QuotientAddGroup.mk x) = deningerSectionAddHom (g i) U x := by
  simpa only [deningerFiltrationSectionsHasseQuotientEquiv] using
    deningerAcyclicSectionsHasseQuotientEquiv_mk (hSE i) U
      (deningerAcyclicOn_of_filtration hSE U h0 hgr i) x

omit [CategoryTheory.HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)] in
/-- Stage sections determine the same graded section exactly when their difference comes from the
previous stage. -/
theorem deningerFiltrationSections_congr_hasse_iff
    (hSE : ∀ i, (deningerFiltrationStep f g hzero i).ShortExact) (U : Opens X)
    (i : ℕ) (x y : ToType ((F (i + 1)).1.obj (op U))) :
    x - y ∈ (deningerSectionAddHom (f i) U).range ↔
      deningerSectionAddHom (g i) U x = deningerSectionAddHom (g i) U y :=
  deningerSections_congr_hasse_iff (hSE i) U x y

/-- Every graded section has a next-stage representative, unique modulo previous-stage sections. -/
theorem deningerFiltrationSections_exists_unique_mod_previous
    (hSE : ∀ i, (deningerFiltrationStep f g hzero i).ShortExact) (U : Opens X)
    (h0 : DeningerAcyclicOn.{w} (F 0) U) (hgr : ∀ i, DeningerAcyclicOn.{w} (G i) U)
    (i : ℕ) (z : ToType ((G i).1.obj (op U))) :
    ∃ x : ToType ((F (i + 1)).1.obj (op U)), deningerSectionAddHom (g i) U x = z ∧
      ∀ y, deningerSectionAddHom (g i) U y = z ↔
        y - x ∈ (deningerSectionAddHom (f i) U).range :=
  deningerAcyclicSections_exists_unique_mod_kernel (hSE i) U
    (deningerAcyclicOn_of_filtration hSE U h0 hgr i) z

section CharacterStage

open Complex

variable {n : ℕ}
  [CategoryTheory.HasExt.{w}
    (TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace (deningerPunctured n)))]
  {F : ℕ → TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace (deningerPunctured n))}
  {J : ℕ → Type} [∀ i, Fintype (J i)]
  {f : ∀ i, F i ⟶ F (i + 1)}
  {g : ∀ i, F (i + 1) ⟶ deningerFreeHolomorphicSheaf (deningerPunctured n) (J i)}
  {hzero : ∀ i, f i ≫ g i = 0}

/-- On a punctured complex character stage, each attached free cell is the quotient of successive
global-section stages. -/
noncomputable def deningerFreeCellFiltrationSectionsHasseQuotientEquiv
    (hSE : ∀ i, (deningerFiltrationStep f g hzero i).ShortExact)
    (J₀ : Type) [Fintype J₀]
    (e : F 0 ≅ deningerFreeHolomorphicSheaf (deningerPunctured n) J₀) (i : ℕ) :
    (ToType ((F (i + 1)).1.obj (op (⊤ : Opens (deningerSpace (deningerPunctured n))))) ⧸
      (deningerSectionAddHom (f i) ⊤).range) ≃+
      ToType ((deningerFreeHolomorphicSheaf (deningerPunctured n) (J i)).1.obj (op ⊤)) :=
  deningerAcyclicSectionsHasseQuotientEquiv (hSE i) ⊤
    (deningerFreeCellFiltration_acyclic hSE J₀ e i)

/-- Every free-cell section has a global next-stage representative, unique modulo the previous
stage. -/
theorem deningerFreeCellFiltrationSections_exists_unique_mod_previous
    (hSE : ∀ i, (deningerFiltrationStep f g hzero i).ShortExact)
    (J₀ : Type) [Fintype J₀]
    (e : F 0 ≅ deningerFreeHolomorphicSheaf (deningerPunctured n) J₀) (i : ℕ)
    (z : ToType ((deningerFreeHolomorphicSheaf (deningerPunctured n) (J i)).1.obj (op ⊤))) :
    ∃ x : ToType ((F (i + 1)).1.obj
        (op (⊤ : Opens (deningerSpace (deningerPunctured n))))),
      deningerSectionAddHom (g i) ⊤ x = z ∧
      ∀ y, deningerSectionAddHom (g i) ⊤ y = z ↔
        y - x ∈ (deningerSectionAddHom (f i) ⊤).range :=
  deningerAcyclicSections_exists_unique_mod_kernel (hSE i) ⊤
    (deningerFreeCellFiltration_acyclic hSE J₀ e i) z

end CharacterStage

end

end RHTower
