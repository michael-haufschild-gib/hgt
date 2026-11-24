import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.GenericPELModuli
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.IntegralPELDatum
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveCompactness

/-! The prime-to-p integral PEL moduli problem and its generic comparison map. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

/-- A quasi-compact immersion into projective space over the affine base. -/
def IsQProjOver {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) : Prop :=
  ∃ (N : ℕ) (i : X ⟶ UpperTheory.Cb.PSpace R N),
    IsImmersion i ∧ QuasiCompact i ∧ i ≫ UpperTheory.Cb.PSpace.str R N = f

end ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel.HT

open ReciprocityTheory.ChartRestriction.G
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {S : Scheme.{0}} (D : Datum p) {R : Type} [CommRing R]

/-- Compatible identifications of the prime-to-p torsion and their pairings. -/
structure TateIsoO (k : Type) [Field k] (Q : Type) [Group Q] (act : D.O → Q → Q)
    (e : ℕ → Q → Q → kˣ → Prop) where
  ζ : ℕ → kˣ
  ζ_prim : ∀ n, 0 < n → n.Coprime p → IsPrimitiveRoot (ζ n) n
  ζ_pow : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ζ (n * m) ^ m = ζ n
  ev : ℕ → D.La → Q
  add : ∀ n x y, ev n (x + y) = ev n x * ev n y
  lin : ∀ n (b : D.O) x, ev n (b • x) = act b (ev n x)
  ker : ∀ n, 0 < n → n.Coprime p → ∀ x, ev n x = 1 ↔ ∃ y, x = n • y
  onto : ∀ n, 0 < n → n.Coprime p → ∀ q, q ^ n = 1 ↔ ∃ x, ev n x = q
  tower : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ev (n * m) x ^ m = ev n x
  isom : ∀ n, 0 < n → n.Coprime p → ∀ x y, e n (ev n x) (ev n y) (ζ n ^ (2 * D.EF x y))

variable {D}

/-- An integral PEL object with a prime-to-p polarization and level structure. -/
structure Obj (b : Base D R) (N : ℕ) (s : S ⟶ Sp R) where
  A : Over S
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  act : OActN D.O A
  P : LB (G2 A).left
  isLB : P.IsLB
  rig₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen
  rig₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen
  symm : LBIso P (P.pull (lift (snd A A) (fst A A)).left)
  ample : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left)
  kerP : ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A),
    (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1
  rosati : ∀ c : D.O, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left)
    (P.pull (lift (fst A A) (snd A A ≫ act.act (D.star c).unop)).left)
  lie : ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β →
    ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v →
      ∃ w : Fin D.a → (epsPtR x ⟶ A),
        (∀ i, ∀ c : 𝓞 D.F, IsTanScal act x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧
        v = (List.ofFn w).prod
  lieRank : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β →
    ∀ i, LieMult (act.restrict (algebraMap (𝓞 D.F) D.O)) x (β.comp (b.t i)) D.m
  eta : D.La → (𝟙_ (Over S) ⟶ A)
  eta_add : ∀ x y, eta (x + y) = eta x * eta y
  eta_lin : ∀ (c : D.O) x, eta (c • x) = eta x ≫ act.act c
  eta_ker : ∀ x, eta (N • x) = 1
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β →
    ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c)
        (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ eta y = I.ev N y

attribute [instance] Obj.grp Obj.comm

structure ObjMap {b : Base D R} {N : ℕ} {S' : Scheme.{0}} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R}
    (o' : Obj b N s') (o : Obj b N s) (f : S' ⟶ S) where
  φ : o'.A.left ⟶ o.A.left
  φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left
  cart : IsGrpPullback o'.A o.A f φ
  sq : IsSquare φ φ₂
  act : ∀ c, (o'.act.act c).left ≫ φ = φ ≫ (o.act.act c).left
  pol : LBIso o'.P (o.P.pull φ₂)
  eta : ∀ y, (o'.eta y).left ≫ φ = f ≫ (o.eta y).left

/-- A smooth quasi-projective representing scheme for the integral moduli problem. -/
structure Model (b : Base D R) (N : ℕ) where
  X : Scheme.{0}
  s : X ⟶ Sp R
  qproj : IsQProjOver s
  smooth : SmoothOfRelativeDimension (D.a * (D.n - 1)) s
  univ : Obj b N s
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R) (o : Obj b N s'), ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (ObjMap o univ f)

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Gen

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R']
  {S S' : Scheme.{0}}

/-- Compatibility of the generic object with a base change of the integral object. -/
def IsGPull {b : Base D R} {gb : GBase D.toG R'} {N : ℕ} {s' : S' ⟶ Sp R'} {s : S ⟶ Sp R}
    (o' : GObj gb N s') (o : Obj b N s) (f : S' ⟶ S) : Prop :=
  ∃ (φA : o'.A.left ⟶ o.A.left) (φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left),
    IsGrpPullback o'.A o.A f φA ∧ IsSquare φA φ₂ ∧
    (∀ c : D.O, (o'.act.act c).left ≫ φA = φA ≫ (o.act.act c).left) ∧ LBIso o'.P (o.P.pull φ₂) ∧
    ∀ y : D.La, (o'.eta y).left ≫ φA = f ≫ (o.eta y).left

end GlobalTheory.UPel.HT.Gen
