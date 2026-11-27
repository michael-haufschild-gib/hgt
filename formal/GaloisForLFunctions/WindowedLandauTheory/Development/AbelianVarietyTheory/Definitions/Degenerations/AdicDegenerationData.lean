import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.Degenerations.PolarizedDegenerationData
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeValueLaws

/-! Cubical compatibility and adic decay of the lattice trivializations
in degeneration data. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw.Cube

namespace ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] [IsDomain R]

namespace DegPre

variable (D : DegPre R)

abbrev rank := Module.finrank ℤ D.X

/-- The translating section restricted to the generic point. -/
abbrev genericSection (x : D.X) : fractionBase R ⟶ D.P.A :=
  toUnit (fractionBase R) ≫ D.c x

/-- The rigidification restricted to the generic point. -/
abbrev rigK :=
  LB.pullGen D.P.L _ _ D.rig (toUnit (fractionBase R)).left

/-- The polarization pairing obtained from the lattice trivialization. -/
def tau (a b : D.X) :=
  LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.psi (a + b)) (LB.invGen D.P.L _ _ (D.psi a)))
      (LB.invGen D.P.L _ _ (D.psi b)))
    (LB.invGen D.P.L _ _ D.rigK)

def PsiEven : Prop :=
  ∀ x : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (D.psi (-x)) (LB.pullGen D.P.L _ _ D.sym (D.genericSection x).left))
    (D.psi x)

def TauBimult : Prop :=
  ∀ a a' b : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (D.tau (a + a') b)
      (cubePull D.cub (D.genericSection a) (D.genericSection a') (D.genericSection b)))
    (LB.mulGen D.P.L _ _ _ _ (D.tau a b) (D.tau a' b))

private abbrev toOpen (V : (Spec (.of R)).Opens) : R →+* Γ(Spec (.of R), V) :=
  ((Spec (.of R)).presheaf.map (homOfLE le_top).op).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom

/-- The lattice trivialization has coordinates extending to sections in the given ideal. -/
def PsiIn (x : D.X) (J : Ideal R) : Prop :=
  ∀ (j : PUnit → D.P.L.ι) (V : (Spec (.of R)).Opens), IsAffineOpen V →
    V ≤ (D.c x).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) →
    ∀ h : (fractionBase R).hom ⁻¹ᵁ V ≤
      (LB.LinComb D.P.L (fun _ => (D.genericSection x).left) (fun _ => -1)).U j,
      ∃ r ∈ J.map (toOpen V), ((fractionBase R).hom.app V) r =
        ((fractionBase R).left.presheaf.map (homOfLE h).op) ((D.psi x).s j).val

end DegPre

/-- Positive lattice data whose trivializations tend to zero in the ideal-adic topology. -/
structure DegData (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) where
  toPre : DegPre R
  psi_even : toPre.PsiEven
  tau_bimult : toPre.TauBimult
  psi_pos : ∀ x : toPre.X, x ≠ 0 → toPre.PsiIn x I
  psi_tendsto : ∀ n : ℕ, {x : toPre.X | ¬ toPre.PsiIn x (I ^ n)}.Finite

end ReciprocityTheory.ChartRestriction.G.Out
