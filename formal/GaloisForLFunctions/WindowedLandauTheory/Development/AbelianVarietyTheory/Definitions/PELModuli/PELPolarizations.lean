import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundles
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Over
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.RingTheory.MvPolynomial.Basic

/-! Relative ampleness in affine charts and the commutator pairing
from the theta group of a line bundle. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Semi

abbrev G2 {S : Scheme.{0}} (G : Over S) : Over S := G ⊗ G

end ReciprocityTheory.ChartRestriction.G.Semi

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

def powOver (L : LB A.left) (U : S.Opens) (N : ℕ) : LB (A.hom ⁻¹ᵁ U).toScheme :=
  LB.LinComb L (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1)

def nonzeroLocus {Y : Scheme.{0}} {M : LB Y} (s : LB.Sec M) : Y.Opens :=
  ⨆ k, Y.basicOpen (s.f k)

/-- Relative very ampleness of a positive tensor power on each affine base open. -/
def RelAmple (L : LB A.left) : Prop :=
  ∀ U : S.Opens, IsAffineOpen U →
    ∃ N : ℕ, 1 ≤ N ∧ ∃ M : ℕ, ∃ s : Fin (M + 1) → LB.Sec (powOver A L U N),
      (⨆ i, nonzeroLocus (s i) = ⊤) ∧
      ∀ i, IsAffineOpen (nonzeroLocus (s i)) ∧
        ∃ r : Fin (M + 1) → Γ((A.hom ⁻¹ᵁ U).toScheme, nonzeroLocus (s i)),
          (∀ j k, ((A.hom ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE (inf_le_right :
              nonzeroLocus (s i) ⊓ (powOver A L U N).U k ≤ (powOver A L U N).U k)).op).hom
                ((s j).f k) =
            ((A.hom ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE (inf_le_left :
              nonzeroLocus (s i) ⊓ (powOver A L U N).U k ≤ nonzeroLocus (s i))).op).hom (r j) *
            ((A.hom ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE (inf_le_right :
              nonzeroLocus (s i) ⊓ (powOver A L U N).U k ≤ (powOver A L U N).U k)).op).hom
                ((s i).f k)) ∧
          Function.Surjective (MvPolynomial.eval₂Hom
            ((A.hom ∣_ U).appLE ⊤ (nonzeroLocus (s i)) le_top).hom r)

def translPt {T : Over S} (x : T ⟶ A) : T ⊗ A ⟶ A := lift (fst T A ≫ x) (snd T A) ≫ μ[A]

def translT {T : Over S} (x : T ⟶ A) : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (translPt A x)

def thetaLB (L : LB A.left) (k : ℤ) {T : Over S} (x : T ⟶ A) : LB (T ⊗ A).left :=
  LB.LinComb L (K := Fin 2) ![(snd T A).left, (translPt A x).left] ![k, -k]

structure ThetaGrp (L : LB A.left) (k : ℤ) (T : Over S) where

  pt : T ⟶ A

  φ : LB.Gen (thetaLB A L k pt)

  isGen : φ.IsGen

def constGen (L : LB A.left) {T : Over S} (c : Γ(T.left, ⊤)ˣ) :
    LB.Gen (LB.LinComb L (Y := (T ⊗ A).left) (K := PEmpty) PEmpty.elim PEmpty.elim) where
  s := fun _ => res le_top (Units.map (fst T A).left.appTop.hom.toMonoidHom c)

/-- The lifted translations commute up to a scalar from the base. -/
def CommIsOf (L : LB A.left) (k : ℤ) {T : Over S} (θx θy : ThetaGrp A L k T)
    (c : Γ(T.left, ⊤)ˣ) : Prop :=
  LB.Gen.Corr L _ _ _ _
    (LB.mulGen L _ _ _ _ θx.φ (LB.pullGen L _ _ θy.φ (translT A θx.pt).left))
    (LB.mulGen L _ _ _ _
      (LB.mulGen L _ _ _ _ θy.φ (LB.pullGen L _ _ θx.φ (translT A θy.pt).left))
      (constGen A L c))

abbrev overRes {T : Over S} (V : T.left.Opens) : Over S := Over.mk (V.ι ≫ T.hom)

def overResι {T : Over S} (V : T.left.Opens) : overRes V ⟶ T := Over.homMk V.ι rfl

def unitRes {T : Over S} (V : T.left.Opens) (c : Γ(T.left, ⊤)ˣ) : Γ((overRes V).left, ⊤)ˣ :=
  Units.map V.ι.appTop.hom.toMonoidHom c

/-- The Weil pairing evaluated by the commutator of local lifts. -/
def WeilIs (L : LB A.left) (k : ℤ) {T : Over S} (x y : T ⟶ A) (c : Γ(T.left, ⊤)ˣ) : Prop :=
  ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
    (∃ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x ∧ θy.pt = overResι V ≫ y) ∧
    ∀ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x → θy.pt = overResι V ≫ y →
      CommIsOf A L k θx θy (unitRes V c)

end ReciprocityTheory.ChartRestriction.G.Out
