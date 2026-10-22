import GaloisForLFunctions.HTGeometry.HasseExactSequence
import GaloisForLFunctions.RHTower.Deninger.DeningerAcyclicResolution
import GaloisForLFunctions.RHTower.Deninger.DeningerFineSurjective

/-!
# Hasse descent for sheaf sections

For a short exact sequence of sheaves, sections are left exact.  If the kernel is acyclic on an
open set, or fine globally with partitions of unity, the quotient section map is also surjective.
Consequently quotient-sheaf sections are middle-sheaf sections modulo kernel sections.  This is the
sheaf-cohomological local--global principle: the connecting class in `H¹` is the obstruction, and
acyclicity or fineness kills it.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat
open GaloisForLFunctions.HTGeometry

noncomputable section

universe w u

variable {X : TopCat.{u}}

/-- Map on sections induced by a sheaf morphism. -/
abbrev deningerSectionAddHom {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (φ : F ⟶ G)
    (U : Opens X) : ToType (F.1.obj (op U)) →+ ToType (G.1.obj (op U)) :=
  (φ.1.app (op U)).hom

/-- Sections of a short exact sheaf sequence are exact at the middle term. -/
theorem deningerSections_functionExact
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (U : Opens X) :
    Function.Exact (deningerSectionAddHom S.f U) (deningerSectionAddHom S.g U) := by
  intro b
  constructor
  · exact deningerSections_exact hS U b
  · rintro ⟨a, rfl⟩
    have hzero : S.f.1.app (op U) ≫ S.g.1.app (op U) = 0 := by
      exact congrArg (fun q : S.X₁ ⟶ S.X₃ => q.1.app (op U)) S.zero
    have h := congrArg (fun q => q.hom a) hzero
    simpa [deningerSectionAddHom] using h

/-- Two middle-sheaf sections have the same quotient section exactly when their difference comes
from a kernel-sheaf section. -/
theorem deningerSections_congr_hasse_iff
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (U : Opens X)
    (x y : ToType (S.X₂.1.obj (op U))) :
    x - y ∈ (deningerSectionAddHom S.f U).range ↔
      deningerSectionAddHom S.g U x = deningerSectionAddHom S.g U y :=
  addHasse_congr_iff (deningerSectionAddHom S.f U) (deningerSectionAddHom S.g U)
    (deningerSections_functionExact hS U) x y

section Acyclic

variable [CategoryTheory.HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]

/-- With acyclic kernel, quotient sections are middle sections modulo kernel sections. -/
noncomputable def deningerAcyclicSectionsHasseQuotientEquiv
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (U : Opens X) (h1 : DeningerAcyclicOn.{w} S.X₁ U) :
    (ToType (S.X₂.1.obj (op U)) ⧸ (deningerSectionAddHom S.f U).range) ≃+
      ToType (S.X₃.1.obj (op U)) :=
  addHasseQuotientEquiv (deningerSectionAddHom S.f U) (deningerSectionAddHom S.g U)
    (deningerSections_functionExact hS U) (deningerSections_surjective_of_acyclic hS U h1)

/-- Acyclic section Hasse equivalence is induced by the quotient sheaf map. -/
@[simp] theorem deningerAcyclicSectionsHasseQuotientEquiv_mk
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (U : Opens X) (h1 : DeningerAcyclicOn.{w} S.X₁ U)
    (x : ToType (S.X₂.1.obj (op U))) :
    deningerAcyclicSectionsHasseQuotientEquiv hS U h1 (QuotientAddGroup.mk x) =
      deningerSectionAddHom S.g U x := by
  simp [deningerAcyclicSectionsHasseQuotientEquiv]

/-- Every quotient section over an acyclic kernel has a middle-section lift, unique modulo kernel
sections. -/
theorem deningerAcyclicSections_exists_unique_mod_kernel
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (U : Opens X) (h1 : DeningerAcyclicOn.{w} S.X₁ U)
    (z : ToType (S.X₃.1.obj (op U))) :
    ∃ x : ToType (S.X₂.1.obj (op U)), deningerSectionAddHom S.g U x = z ∧
      ∀ y, deningerSectionAddHom S.g U y = z ↔
        y - x ∈ (deningerSectionAddHom S.f U).range :=
  addHasse_exists_unique_mod_global
    (deningerSectionAddHom S.f U) (deningerSectionAddHom S.g U)
    (deningerSections_functionExact hS U)
    (deningerSections_surjective_of_acyclic hS U h1) z

end Acyclic

section Fine

/-- With fine kernel and partitions of unity, global quotient sections are global middle sections
modulo global kernel sections. -/
noncomputable def deningerFineSectionsHasseQuotientEquiv
    {R : AddSubgroup C(X, ℝ)}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (A : DeningerFineAction S.X₁ R) (hpu : DeningerHasPartitions R) :
    (ToType (S.X₂.1.obj (op (⊤ : Opens X))) ⧸
      (deningerSectionAddHom S.f (⊤ : Opens X)).range) ≃+
      ToType (S.X₃.1.obj (op (⊤ : Opens X))) :=
  addHasseQuotientEquiv
    (deningerSectionAddHom S.f (⊤ : Opens X))
    (deningerSectionAddHom S.g (⊤ : Opens X))
    (deningerSections_functionExact hS ⊤) (deningerFine_sections_surjective hS A hpu)

/-- Fine section Hasse equivalence is induced by the quotient sheaf map. -/
@[simp] theorem deningerFineSectionsHasseQuotientEquiv_mk
    {R : AddSubgroup C(X, ℝ)}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (A : DeningerFineAction S.X₁ R) (hpu : DeningerHasPartitions R)
    (x : ToType (S.X₂.1.obj (op (⊤ : Opens X)))) :
    deningerFineSectionsHasseQuotientEquiv hS A hpu (QuotientAddGroup.mk x) =
      deningerSectionAddHom S.g (⊤ : Opens X) x := by
  simp [deningerFineSectionsHasseQuotientEquiv]

/-- Every global quotient section with fine kernel has a global middle-section lift, unique modulo
global kernel sections. -/
theorem deningerFineSections_exists_unique_mod_kernel
    {R : AddSubgroup C(X, ℝ)}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (A : DeningerFineAction S.X₁ R) (hpu : DeningerHasPartitions R)
    (z : ToType (S.X₃.1.obj (op (⊤ : Opens X)))) :
    ∃ x : ToType (S.X₂.1.obj (op (⊤ : Opens X))),
      deningerSectionAddHom S.g (⊤ : Opens X) x = z ∧
      ∀ y, deningerSectionAddHom S.g (⊤ : Opens X) y = z ↔
        y - x ∈ (deningerSectionAddHom S.f (⊤ : Opens X)).range :=
  addHasse_exists_unique_mod_global
    (deningerSectionAddHom S.f (⊤ : Opens X))
    (deningerSectionAddHom S.g (⊤ : Opens X))
    (deningerSections_functionExact hS ⊤) (deningerFine_sections_surjective hS A hpu) z

end Fine

end


end RHTower
