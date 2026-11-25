import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.IntegralPELModuli
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELGroupPullbacks
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundleComposition
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundleChartPullback

/-! The integral PEL object maps have identities and compose over the base. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open Semi

variable {X Y Z : Scheme.{0}} {L M N : LB X}

theorem LBIso.symm (h : LBIso L M) : LBIso M L := by
  obtain ⟨t, ht⟩ := h
  exact ht.symm

theorem LBIso.trans (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB)
    (h : LBIso L M) (h' : LBIso M N) : LBIso L N := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h'
  exact ha.comp hb hL hM hN

theorem LBIso.pull (h : LBIso L M) (f : Y ⟶ X) :
    LBIso (L.pull f) (M.pull f) := by
  obtain ⟨t, ht⟩ := h
  exact (ChartPull.pull L f).exists_iso (ChartPull.pull M f) ht

theorem LBIso.pull_comp (hL : L.IsLB) (f : Z ⟶ Y) (g : Y ⟶ X) :
    LBIso ((L.pull g).pull f) (L.pull (f ≫ g)) :=
  ChartPull.iso_of_common ((ChartPull.pull (L.pull g) f).comp (ChartPull.pull L g))
    (ChartPull.pull L (f ≫ g)) hL

theorem LBIso.pull_id (hL : L.IsLB) : LBIso L (L.pull (𝟙 X)) :=
  ChartPull.iso_of_common (ChartPull.id L) (ChartPull.pull L (𝟙 X)) hL

end ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel.HT

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

/-- The identity on the group, polarization and level gives the identity object map. -/
def ObjMap.refl {S : Scheme.{0}} {s : S ⟶ Sp R} (a : Obj b N s) : ObjMap a a (𝟙 S) where
  φ := 𝟙 _
  φ₂ := 𝟙 _
  cart := IsGrpPullback.refl a.A
  sq := ⟨by simp, by simp⟩
  act _ := by simp
  pol := LBIso.pull_id a.isLB
  eta _ := by simp

/-- Composition preserves the cartesian group map, polarization and level structure. -/
def ObjMap.comp {S T U : Scheme.{0}} {s : S ⟶ Sp R} {t : T ⟶ Sp R} {u : U ⟶ Sp R}
    {a : Obj b N s} {a' : Obj b N t} {a'' : Obj b N u} {f : S ⟶ T} {g : T ⟶ U}
    (h : ObjMap a a' f) (h' : ObjMap a' a'' g) : ObjMap a a'' (f ≫ g) where
  φ := h.φ ≫ h'.φ
  φ₂ := h.φ₂ ≫ h'.φ₂
  cart := h.cart.comp h'.cart
  sq := h.sq.comp h'.sq
  act c := by rw [← Category.assoc, h.act, Category.assoc, h'.act, Category.assoc]
  pol := by
    have hM := a'.isLB.pull h.φ₂
    have hN := (a''.isLB.pull h'.φ₂).pull h.φ₂
    have hg := LBIso.trans a.isLB hM hN h.pol (h'.pol.pull h.φ₂)
    exact LBIso.trans a.isLB hN (a''.isLB.pull _) hg (LBIso.pull_comp a''.isLB h.φ₂ h'.φ₂)
  eta y := by
    let x : S ⟶ a.A.left := (a.eta y).left
    let x' : T ⟶ a'.A.left := (a'.eta y).left
    let x'' : U ⟶ a''.A.left := (a''.eta y).left
    have h₁ : x ≫ h.φ = f ≫ x' := h.eta y
    have h₂ : x' ≫ h'.φ = g ≫ x'' := h'.eta y
    calc
      _ = (x ≫ h.φ) ≫ h'.φ := (Category.assoc _ _ _).symm
      _ = (f ≫ x') ≫ h'.φ := congrArg (· ≫ h'.φ) h₁
      _ = f ≫ (x' ≫ h'.φ) := Category.assoc _ _ _
      _ = f ≫ (g ≫ x'') := congrArg (f ≫ ·) h₂
      _ = _ := (Category.assoc _ _ _).symm

end GlobalTheory.UPel.HT
