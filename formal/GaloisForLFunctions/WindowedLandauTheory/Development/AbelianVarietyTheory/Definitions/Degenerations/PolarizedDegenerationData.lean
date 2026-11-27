import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeValueNormalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.WeilTorsionCharacters
import Mathlib.RingTheory.Localization.FractionRing

/-! Principal polarization and lattice data used to form the normalized powers
in an abelian degeneration. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.AbLaw.Cube
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

/-- A symmetric, rigidified relatively ample line bundle with trivial translation kernel. -/
structure PolAV (S : Scheme.{0}) where
  A : Over S
  [grp : GrpObj A]
  isAb : IsAbelianScheme A
  g : ℕ
  smoothDim : SmoothOfRelativeDimension g A.hom
  L : LB A.left
  isLB : L.IsLB
  rigid : ∃ t : (L.pull η[A].left).Gen, t.IsGen
  sym : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
    ∃ t : (LB.LinComb L ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι]
      ![1, -1]).Gen, t.IsGen
  ample : RelAmple A L
  ktriv : KTriv A L

attribute [instance] PolAV.grp

instance {S : Scheme.{0}} (P : PolAV S) : IsCommMonObj P.A := P.isAb.comm

variable {R : Type} [CommRing R] [IsDomain R]

/-- The generic point as a scheme over the original base. -/
abbrev fractionBase (R : Type) [CommRing R] [IsDomain R] : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))

/-- A polarization, a lattice of translating sections, and compatible
trivializations on the generic fibre. -/
structure DegPre (R : Type) [CommRing R] [IsDomain R] where
  P : PolAV (Spec (.of R))
  rig : (P.L.pull η[P.A].left).Gen
  rig_gen : rig.IsGen
  cub : (cubeBundle P.A P.L).Gen
  cub_gen : cub.IsGen
  cub_normalized : NormalizedCube cub
  sym : (LB.LinComb P.L ![(GrpObj.inv : P.A ⟶ P.A).left, 𝟙 P.A.left] ![1, -1]).Gen
  sym_gen : sym.IsGen
  sym_rig : LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ sym η[P.A].left) (LB.oneGen P.L)
  X : Type
  [addX : AddCommGroup X]
  [freeX : Module.Free ℤ X]
  [finX : Module.Finite ℤ X]
  c : X → (𝟙_ (Over (Spec (.of R))) ⟶ P.A)
  c_add : ∀ x y, c (x + y) = c x * c y
  psi : ∀ x : X, (LB.LinComb P.L (K := PUnit)
    (fun _ => (toUnit (fractionBase R) ≫ c x).left) (fun _ => -1)).Gen
  psi_gen : ∀ x, (psi x).IsGen

namespace DegPre

variable (D : DegPre R)

instance : AddCommGroup D.X := D.addX
instance : Module.Free ℤ D.X := D.freeX
instance : Module.Finite ℤ D.X := D.finX

/-- The two constant factors normalize the shifted power along the translating section and the identity. -/
def famφB (α : D.X) : Fin 4 → (D.P.A.left ⟶ D.P.A.left) :=
  ![𝟙 _, (((toUnit D.P.A ≫ D.c α) * 𝟙 D.P.A) : D.P.A ⟶ D.P.A).left,
    D.P.A.hom ≫ (D.c α).left, D.P.A.hom ≫ η[D.P.A].left]

def famε (j : ℕ) : Fin 4 → ℤ := ![(j : ℤ) - 1, 1, -1, 1]

abbrev SecB (j : ℕ) (α : D.X) := LB.Sec (LB.LinComb D.P.L (D.famφB α) (famε j))

end DegPre

end ReciprocityTheory.ChartRestriction.G.Out
