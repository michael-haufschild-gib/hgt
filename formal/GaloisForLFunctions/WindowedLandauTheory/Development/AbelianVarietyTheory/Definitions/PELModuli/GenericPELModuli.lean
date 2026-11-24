import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELOrderAction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELPolarizations
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.GlobalPELDatum
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! The generic PEL moduli problem with its compatible Tate level structures. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open Semi

abbrev Sp (R : Type) [CommRing R] : Scheme.{0} := Spec (CommRingCat.of R)

abbrev spMap {R R' : Type} [CommRing R] [CommRing R'] (β : R →+* R') : Sp R' ⟶ Sp R :=
  Spec.map (CommRingCat.ofHom β)

/-- A group scheme morphism exhibiting pullback along the map of base schemes. -/
def IsGrpPullback {S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S)
    (φ : G'.left ⟶ G.left) : Prop :=
  IsPullback φ G'.hom G.hom f ∧
    ∀ (T : Over S') (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G),
      x₀.left = x.left ≫ φ → y₀.left = y.left ≫ φ → (x₀ * y₀).left = (x * y).left ≫ φ

/-- The induced morphism on the fibre squares commutes with both projections. -/
def IsSquare {S' : Scheme.{0}} {G' : Over S'} {G : Over S} (φ : G'.left ⟶ G.left)
    (φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left) : Prop :=
  φ₂ ≫ (fst G G).left = (fst G' G').left ≫ φ ∧ φ₂ ≫ (snd G G).left = (snd G' G').left ≫ φ

def LBIso {X : Scheme.{0}} (L M : LB X) : Prop := ∃ w : LB.Iso L M, w.IsGen

def unitOn {R : Type} [CommRing R] (u : Rˣ) : Γ(Sp R, ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom u

end ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel.HT.Gen

open ReciprocityTheory.ChartRestriction.G
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {S : Scheme.{0}}

/-- Compatible identifications of the lattice quotients with geometric torsion
and their alternating pairings. -/
structure GTateIso (G : GDatum) (k : Type) [Field k] (Q : Type) [Group Q] (act : G.O → Q → Q)
    (e : ℕ → Q → Q → kˣ → Prop) where
  ζ : ℕ → kˣ
  ζ_prim : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n
  ζ_pow : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n
  ev : ℕ → G.La → Q
  add : ∀ n x y, ev n (x + y) = ev n x * ev n y
  lin : ∀ n (b : G.O) x, ev n (b • x) = act b (ev n x)
  ker : ∀ n, 0 < n → ∀ x, ev n x = 1 ↔ ∃ y, x = n • y
  onto : ∀ n, 0 < n → ∀ q, q ^ n = 1 ↔ ∃ x, ev n x = q
  tower : ∀ n m, 0 < n → 0 < m → ∀ x, ev (n * m) x ^ m = ev n x
  isom : ∀ n, 0 < n → ∀ x y, e n (ev n x) (ev n y) (ζ n ^ (2 * G.EF x y))

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

/-- An abelian scheme with order action, polarization, Lie type and full level structure. -/
structure GObj (b : GBase G R) (N : ℕ) (s : S ⟶ Sp R) where
  A : Over S
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  act : OActN G.O A
  P : LB (G2 A).left
  isLB : P.IsLB
  rig₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen
  rig₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen
  symm : LBIso P (P.pull (lift (snd A A) (fst A A)).left)
  ample : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left)
  rosati : ∀ c : G.O, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left)
    (P.pull (lift (fst A A) (snd A A ≫ act.act (G.star c).unop)).left)
  lie : ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β →
    ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 G.F) G.O G.ω) (β b.ρ) v →
      ∃ w : Fin G.a → (epsPtR x ⟶ A),
        (∀ i, ∀ c : 𝓞 G.F, IsTanScal act x (algebraMap (𝓞 G.F) G.O c) (β (b.t i c)) (w i)) ∧
        v = (List.ofFn w).prod
  lieRank : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β →
    ∀ i, LieMult (act.restrict (algebraMap (𝓞 G.F) G.O)) x (β.comp (b.t i)) G.m
  eta : G.La → (𝟙_ (Over S) ⟶ A)
  eta_add : ∀ x y, eta (x + y) = eta x * eta y
  eta_lin : ∀ (c : G.O) x, eta (c • x) = eta x ≫ act.act c
  eta_ker : ∀ x, eta (N • x) = 1
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β →
    ∃ I : GTateIso G k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c)
        (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ eta y = I.ev N y

attribute [instance] GObj.grp GObj.comm

structure GObjMap {b : GBase G R} {N : ℕ} {S' : Scheme.{0}} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R}
    (o' : GObj b N s') (o : GObj b N s) (f : S' ⟶ S) where
  φ : o'.A.left ⟶ o.A.left
  φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left
  cart : IsGrpPullback o'.A o.A f φ
  sq : IsSquare φ φ₂
  act : ∀ c, (o'.act.act c).left ≫ φ = φ ≫ (o.act.act c).left
  pol : LBIso o'.P (o.P.pull φ₂)
  eta : ∀ y, (o'.eta y).left ≫ φ = f ≫ (o.eta y).left

/-- A representing scheme for the generic PEL moduli problem. -/
structure GenModel (b : GBase G R) (N : ℕ) where
  X : Scheme.{0}
  s : X ⟶ Sp R
  univ : GObj b N s
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R) (o : GObj b N s'), ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (GObjMap o univ f)

end GlobalTheory.UPel.HT.Gen
