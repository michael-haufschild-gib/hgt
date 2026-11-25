import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.ThetaTranslationPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELGeneratorValues

/-! The theta commutator is an equality of products of unit germs. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CommPairing

theorem val_constGen {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left) {T : Over S} (c : Γ(T.left, ⊤)ˣ)
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    val (constGen A L c) r z J = gm (r ≫ (fst T A).left) z ⊤ c := by
  show gm r z _ (res le_top (pullU (fst T A).left ⊤ c)) = _
  exact (gm_res r z _ (Set.mem_iInter.2 fun k => k.elim) _).trans (gm_pull r _ z ⊤ trivial c)

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

def tval {T : Over S} (θ : ThetaGrp A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : (Z.presheaf.stalk z)ˣ :=
  val (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ r z J

theorem commIsOf_iff (hL : L.IsLB) {T : Over S} (θx θy : ThetaGrp A L k T) (c : Γ(T.left, ⊤)ˣ) :
    CommIsOf A L k θx θy c ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval θx r z J * tval θy (r ≫ (translT A θx.pt).left) z J =
        tval θy r z J * tval θx (r ≫ (translT A θy.pt).left) z J * gm (r ≫ (fst T A).left) z ⊤ c := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J → ∀ θ θ' : ThetaGrp A L k T,
      val (LB.mulGen L _ _ _ _ θ.φ (LB.pullGen L _ _ θ'.φ (translT A θ.pt).left)) r z J =
        tval θ r z J * tval θ' (r ≫ (translT A θ.pt).left) z J := fun Z r z J hJ θ θ' =>
    (val_mul hJ _ _ _).trans (congrArg (tval θ r z J * ·) (val_pull hJ _ _ _))
  constructor
  · intro H Z r z J hJ
    exact (key Z r z J hJ θx θy).symm.trans ((val_corr hJ H r).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (key Z r z J hJ θy θx) (val_constGen L c r z J))))
  · intro H
    refine corr_of_val hL fun y J hJ => ?_
    exact (key _ _ y J hJ θx θy).trans ((H _ _ y J hJ).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (key _ _ y J hJ θy θx) (val_constGen L c _ y J))).symm)

end GlobalTheory.CommPairing
