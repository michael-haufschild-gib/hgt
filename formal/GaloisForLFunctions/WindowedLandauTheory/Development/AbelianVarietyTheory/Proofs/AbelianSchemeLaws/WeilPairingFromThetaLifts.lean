import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ThetaCommutatorScalar
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.ThetaCommutatorPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.IntegralPELObjectMaps

/-! A theta commutator of global lifts gives the Weil pairing. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CommPairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ}

/-- Global lifts give a valid Weil pairing scalar on an arbitrary test scheme. -/
theorem weilIs_of_commIsOf (hA : IsAbelianScheme A) (hL : L.IsLB)
    {x y : ThetaGrp A L k T} {c : Γ(T.left, ⊤)ˣ}
    (hc : CommIsOf A L k x y c) : WeilIs A L k x.pt y.pt c := by
  haveI := hA.comm
  intro z
  let V : T.left.Opens := ⊤
  let τ : (overRes (T := T) V).left ⟶ T.left := V.ι
  haveI : IsIso τ := inferInstanceAs (IsIso T.left.topIso.hom)
  have hτ : τ ≫ T.hom = (overRes (T := T) V).hom ≫ 𝟙 S := (Category.comp_id _).symm
  let hp := IsGrpPullback.refl A
  obtain ⟨w, hw⟩ := LBIso.pull_id hL
  have hx : τ ≫ x.pt.left = (overResι V ≫ x.pt).left ≫ 𝟙 A.left := by
    rw [Category.comp_id]
    rfl
  have hy : τ ≫ y.pt.left = (overResι V ≫ y.pt).left ≫ 𝟙 A.left := by
    rw [Category.comp_id]
    rfl
  obtain ⟨x', ex, mx⟩ := WeilPull.exists_rel_down hp τ hτ hL hL w hw (overResι V ≫ x.pt) x hx
  obtain ⟨y', ey, my⟩ := WeilPull.exists_rel_down hp τ hτ hL hL w hw (overResι V ≫ y.pt) y hy
  have xu : τ ≫ x.pt.left = x'.pt.left ≫ 𝟙 A.left := by rw [ex]; exact hx
  have yu : τ ≫ y.pt.left = y'.pt.left ≫ 𝟙 A.left := by rw [ey]; exact hy
  have hc' : CommIsOf A L k x' y' (unitRes V c) :=
    (WeilPull.commIsOf_iff_of_rel hp τ hτ hL hL w (mul_comm x'.pt y'.pt) xu yu mx my c
      (unitRes V c) (fun Z r z => (gm_pull r τ z ⊤ trivial c).symm)).2 hc
  exact ⟨V, trivial, ⟨x', y', ex, ey⟩, fun u v hu hv =>
    commIsOf_of_same_points hA hL (hu.trans ex.symm) (hv.trans ey.symm) hc'⟩

theorem exists_weilIs_of_global_lifts (hA : IsAbelianScheme A) (hL : L.IsLB)
    (x y : ThetaGrp A L k T) : ∃ c, WeilIs A L k x.pt y.pt c := by
  obtain ⟨c, hc⟩ := exists_commIsOf hA hL x y
  exact ⟨c, weilIs_of_commIsOf hA hL hc⟩

end GlobalTheory.CommPairing
