import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.GroupTangentPowers
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! Abelian schemes with an order action, and its eigenspaces on the Lie algebra. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Semi

variable {S : Scheme.{0}}

/-- A commutative smooth proper group scheme with geometrically connected fibres. -/
class IsAbelianScheme (A : Over S) [GrpObj A] : Prop where
  comm : IsCommMonObj A
  smooth : Smooth A.hom
  proper : IsProper A.hom
  geomConnected : GeometricallyConnected A.hom

end ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.UPel.HT

open GlobalTheory.GrpTangent

variable {S : Scheme.{0}}

/-- A left action of an order by group homomorphisms. -/
structure OActN (O : Type) [Ring O] (A : Over S) [GrpObj A] where
  act : O → (A ⟶ A)
  hom : ∀ b, IsMonHom (act b)
  one : act 1 = 𝟙 A
  mul : ∀ b c, act (b * c) = act c ≫ act b
  add : ∀ b c, act (b + c) = act b * act c

/-- The spectrum of the dual numbers above the specified base point. -/
abbrev epsPtR {R : Type} [CommRing R] (x : Sp R ⟶ S) : Over S :=
  (Over.map x).obj (epsR R)

/-- A tangent vector at the identity on which the order element acts by the given scalar. -/
def IsTanScal {O R : Type} [Ring O] [CommRing R] {G : Over S} [GrpObj G] (act : OActN O G)
    (x : Sp R ⟶ S) (b : O) (c : R) (v : epsPtR x ⟶ G) : Prop :=
  ((Over.map x).map (epsZero R) ≫ v).left = (1 : Over.mk x ⟶ G).left ∧
    v ≫ act.act b = (Over.map x).map (epsScale c) ≫ v

/-- Restriction of an order action along a ring homomorphism. -/
def OActN.restrict {O O' : Type} [Ring O] [Ring O'] {A : Over S} [GrpObj A]
    (act : OActN O A) (f : O' →+* O) : OActN O' A where
  act b := act.act (f b)
  hom b := act.hom (f b)
  one := by rw [map_one, act.one]
  mul b c := by rw [map_mul, act.mul]
  add b c := by rw [map_add, act.add]

/-- Multiplicity of a scalar character on the Lie algebra, expressed by
unique expansion in a basis of tangent vectors. -/
def LieMult {O k : Type} [Ring O] [Field k] {A : Over S} [GrpObj A] (act : OActN O A)
    (x : Sp k ⟶ S) (τ : O →+* k) (n : ℕ) : Prop :=
  ∃ v : Fin n → (epsPtR x ⟶ A), (∀ i b, IsTanScal act x b (τ b) (v i)) ∧
    ∀ w : epsPtR x ⟶ A, (∀ b, IsTanScal act x b (τ b) w) →
      ∃! c : Fin n → k,
        w = (List.ofFn fun i => (Over.map x).map (epsScale (c i)) ≫ v i).prod

end GlobalTheory.UPel.HT
