import GaloisForLFunctions.RHTower.DeningerResidueStalk
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# The one prime residue sheaf is a skyscraper

For a single prime the residue sheaf is the skyscraper sheaf at that prime's closed point: the
morphism attached to evaluation on the stalk is an isomorphism, because at the prime both stalks
are `ℤ` and away from it both stalks vanish, the closed point being closed.

* `deningerResidueToSkyscraper` : the comparison morphism.
* `deningerResidueSkyscraperIso` : it is an isomorphism.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat
open StalkSkyscraperPresheafAdjunctionAuxs

attribute [local instance] Classical.propDecidable

variable (p : Nat.Primes)

/-- The comparison morphism from the one prime residue sheaf to the skyscraper sheaf. -/
noncomputable def deningerResidueToSkyscraper :
    deningerResidueAddPresheaf {p} ℤ ⟶
      skyscraperPresheaf (deningerClosedPt p) (AddCommGrpCat.of ℤ) :=
  toSkyscraperPresheaf _ (deningerResidueStalkDesc {p} (Finset.mem_singleton_self p))

/-- Specialization to a point of the arithmetic curve from a closed point forces equality. -/
theorem deningerClosedPt_specializes_iff {z : deningerArithBase} :
    deningerClosedPt p ⤳ z ↔ z = deningerClosedPt p := by
  constructor
  · intro h
    have hz : z ∈ closure ({deningerClosedPt p} : Set deningerArithBase) := h.mem_closure
    rwa [(deningerClosedPt_isClosed p).closure_eq, Set.mem_singleton_iff] at hz
  · rintro rfl
    exact specializes_refl _

set_option backward.isDefEq.respectTransparency false in
/-- On the stalk at the prime, the comparison morphism is evaluation. -/
theorem deningerResidueToSkyscraper_stalk_at :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} (deningerClosedPt p)).map
        (deningerResidueToSkyscraper p) ≫
      (skyscraperPresheafStalkOfSpecializes (deningerClosedPt p) (AddCommGrpCat.of ℤ)
        (specializes_refl _)).hom =
      deningerResidueStalkDesc {p} (Finset.mem_singleton_self p) := by
  have h1 : deningerResidueStalkDesc {p} (Finset.mem_singleton_self p) =
      fromStalk (deningerClosedPt p) (deningerResidueToSkyscraper p) :=
    (fromStalk_to_skyscraper _ _).symm
  rw [h1]
  refine TopCat.Presheaf.stalk_hom_ext _ (fun U hU => ?_)
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The comparison morphism is a stalkwise isomorphism. -/
theorem deningerResidueToSkyscraper_stalk_isIso (z : deningerArithBase) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} z).map
      (deningerResidueToSkyscraper p)) := by
  classical
  by_cases hz : z = deningerClosedPt p
  · subst hz
    haveI : IsIso (deningerResidueStalkDesc {p} (Finset.mem_singleton_self p)) :=
      (ConcreteCategory.isIso_iff_bijective _).2
        (deningerResidueStalk_bijective {p} (Finset.mem_singleton_self p))
    haveI hcomp : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0}
        (deningerClosedPt p)).map (deningerResidueToSkyscraper p) ≫
        (skyscraperPresheafStalkOfSpecializes (deningerClosedPt p) (AddCommGrpCat.of ℤ)
          (specializes_refl _)).hom) := by
      rw [deningerResidueToSkyscraper_stalk_at p]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (skyscraperPresheafStalkOfSpecializes (deningerClosedPt p) (AddCommGrpCat.of ℤ)
        (specializes_refl _)).hom
  · have hns : ¬ (deningerClosedPt p ⤳ z) :=
      fun h => hz ((deningerClosedPt_specializes_iff p).1 h)
    have hzero₁ : IsZero (TopCat.Presheaf.stalk (deningerResidueAddPresheaf {p} ℤ) z) := by
      refine deningerResidueStalk_isZero {p} z (fun q hq => ?_)
      rw [Finset.mem_singleton] at hq
      rw [hq]
      exact hz
    have hterm := skyscraperPresheafStalkOfNotSpecializesIsTerminal
      (deningerClosedPt p) (AddCommGrpCat.of ℤ) hns
    have hzero₂ : IsZero (TopCat.Presheaf.stalk
        (skyscraperPresheaf (deningerClosedPt p) (AddCommGrpCat.of ℤ)) z) :=
      IsZero.of_iso (isZero_zero AddCommGrpCat.{0})
        (hterm.uniqueUpToIso (isZero_zero AddCommGrpCat.{0}).isTerminal)
    have heq : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} z).map
        (deningerResidueToSkyscraper p) = (hzero₁.iso hzero₂).hom :=
      hzero₁.eq_of_src _ _
    rw [heq]
    infer_instance

/-- **The one prime residue sheaf is the skyscraper sheaf at that prime.** -/
theorem deningerResidueToSkyscraper_isIso : IsIso (deningerResidueToSkyscraper p) := by
  classical
  haveI : ∀ z : deningerArithBase, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} z).map
      (deningerResidueToSkyscraper p)) := deningerResidueToSkyscraper_stalk_isIso p
  have hiso : IsIso ((TopCat.Sheaf.forget AddCommGrpCat.{0} deningerArithBase).map
      (⟨deningerResidueToSkyscraper p⟩ :
        (⟨deningerResidueAddPresheaf {p} ℤ, deningerResidueAddPresheaf_isSheaf {p} ℤ⟩ :
          TopCat.Sheaf AddCommGrpCat.{0} deningerArithBase) ⟶
        ⟨skyscraperPresheaf (deningerClosedPt p) (AddCommGrpCat.of ℤ),
          skyscraperPresheaf_isSheaf _ _⟩)) := by
    haveI := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
      (F := (⟨deningerResidueAddPresheaf {p} ℤ, deningerResidueAddPresheaf_isSheaf {p} ℤ⟩ :
        TopCat.Sheaf AddCommGrpCat.{0} deningerArithBase))
      (G := ⟨skyscraperPresheaf (deningerClosedPt p) (AddCommGrpCat.of ℤ),
        skyscraperPresheaf_isSheaf _ _⟩)
      ⟨deningerResidueToSkyscraper p⟩
    infer_instance
  exact hiso

/-- **The one prime residue sheaf is isomorphic to the skyscraper sheaf.** -/
noncomputable def deningerResidueSkyscraperIso :
    deningerResidueAddPresheaf {p} ℤ ≅
      skyscraperPresheaf (deningerClosedPt p) (AddCommGrpCat.of ℤ) :=
  haveI := deningerResidueToSkyscraper_isIso p
  asIso (deningerResidueToSkyscraper p)

end RHTower
