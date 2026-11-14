import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Pi
import GaloisForLFunctions.RepresentationLifting.TruncatedPolynomialAlgebra

/-!
# Modules defined by square-zero operators

A square-zero linear operator gives an actual module over the dual numbers,
with `(a + bε)x = ax + bD(x)`. Intertwining linear maps become module morphisms.
The map `k[t]/(t²) → k[ε]` sending the residue of `t` to `ε` places these modules
over the truncated polynomial algebra used by the periodic resolution.
-/

noncomputable section
open CategoryTheory
namespace GaloisForLFunctions.RepresentationLifting
universe u
variable {k V W : Type u} [CommRing k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- A square-zero operator defines a representation of the dual-number algebra. -/
def squareZeroDualNumberAction (D : Module.End k V) (hD : D * D = 0) :
    DualNumber k →ₐ[k] Module.End k V :=
  DualNumber.lift ⟨(Algebra.ofId k (Module.End k V), D), hD,
    fun a => (Algebra.commutes (R := k) a D).symm⟩

theorem squareZeroDualNumberAction_apply (D : Module.End k V) (hD : D * D = 0)
    (a : DualNumber k) (x : V) :
    squareZeroDualNumberAction D hD a x = a.fst • x + a.snd • D x := rfl

/-- The bundled dual-number module associated with a square-zero operator. -/
def squareZeroModule (D : Module.End k V) (hD : D * D = 0) : ModuleCat (DualNumber k) :=
  letI := Module.compHom V (squareZeroDualNumberAction D hD).toRingHom
  ModuleCat.of (DualNumber k) V

/-- The infinitesimal generator acts by the prescribed operator. -/
theorem squareZeroModule_eps_smul (D : Module.End k V) (hD : D * D = 0)
    (x : squareZeroModule D hD) : (DualNumber.eps : DualNumber k) • x = D x := by
  change squareZeroDualNumberAction D hD DualNumber.eps x = D x
  rw [squareZeroDualNumberAction_apply]
  simp only [DualNumber.fst_eps, DualNumber.snd_eps, zero_smul, one_smul, zero_add]

/-- Every intertwiner of square-zero operators is linear over the dual numbers. -/
def squareZeroModuleHom (D : Module.End k V) (E : Module.End k W)
    (hD : D * D = 0) (hE : E * E = 0) (f : V →ₗ[k] W) (hf : f.comp D = E.comp f) :
    squareZeroModule D hD ⟶ squareZeroModule E hE :=
  ConcreteCategory.ofHom (C := ModuleCat (DualNumber k))
    (show squareZeroModule D hD →ₗ[DualNumber k] squareZeroModule E hE from {
    toFun := f
    map_add' := f.map_add
    map_smul' a x := by
      change f (squareZeroDualNumberAction D hD a x) = squareZeroDualNumberAction E hE a (f x)
      rw [squareZeroDualNumberAction_apply, squareZeroDualNumberAction_apply,
        map_add, map_smul, map_smul]
      exact congrArg (fun y => a.fst • f x + a.snd • y) (LinearMap.congr_fun hf x) })

/-- The truncated variable is sent to the dual-number infinitesimal. -/
def truncatedToDualNumbers : TruncatedPolynomialAlgebra k 2 →ₐ[k] DualNumber k :=
  AdjoinRoot.liftAlgHom (Polynomial.X ^ 2 : Polynomial k) (Algebra.ofId k (DualNumber k))
    DualNumber.eps (by simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X, DualNumber.eps_pow_two])

theorem truncatedToDualNumbers_root :
    truncatedToDualNumbers (truncatedRoot k 2) = (DualNumber.eps : DualNumber k) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The same operator defines a module over the quadratic truncated polynomial algebra. -/
def truncatedSquareZeroModule (D : Module.End k V) (hD : D * D = 0) :
    ModuleCat (TruncatedPolynomialAlgebra k 2) :=
  letI := Module.compHom V
    ((squareZeroDualNumberAction D hD).comp truncatedToDualNumbers).toRingHom
  ModuleCat.of (TruncatedPolynomialAlgebra k 2) V

/-- The residue of the polynomial variable acts by the original square-zero operator. -/
theorem truncatedSquareZeroModule_root_smul (D : Module.End k V) (hD : D * D = 0)
    (x : truncatedSquareZeroModule D hD) : truncatedRoot k 2 • x = D x := by
  change squareZeroDualNumberAction D hD (truncatedToDualNumbers (truncatedRoot k 2)) x = D x
  rw [truncatedToDualNumbers_root, squareZeroDualNumberAction_apply]
  simp only [DualNumber.fst_eps, DualNumber.snd_eps, zero_smul, one_smul, zero_add]

/-- Intertwiners are also linear over the truncated polynomial algebra. -/
def truncatedSquareZeroModuleHom (D : Module.End k V) (E : Module.End k W)
    (hD : D * D = 0) (hE : E * E = 0) (f : V →ₗ[k] W) (hf : f.comp D = E.comp f) :
    truncatedSquareZeroModule D hD ⟶ truncatedSquareZeroModule E hE :=
  ConcreteCategory.ofHom (C := ModuleCat (TruncatedPolynomialAlgebra k 2))
    (show truncatedSquareZeroModule D hD →ₗ[TruncatedPolynomialAlgebra k 2]
      truncatedSquareZeroModule E hE from {
    toFun := f
    map_add' := f.map_add
    map_smul' a x := by
      change f (squareZeroDualNumberAction D hD (truncatedToDualNumbers a) x) =
        squareZeroDualNumberAction E hE (truncatedToDualNumbers a) (f x)
      rw [squareZeroDualNumberAction_apply, squareZeroDualNumberAction_apply,
        map_add, map_smul, map_smul]
      exact congrArg (fun y => (truncatedToDualNumbers a).fst • f x +
        (truncatedToDualNumbers a).snd • y) (LinearMap.congr_fun hf x) })

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.squareZeroModuleHom
#print axioms GaloisForLFunctions.RepresentationLifting.truncatedSquareZeroModule_root_smul
#print axioms GaloisForLFunctions.RepresentationLifting.truncatedSquareZeroModuleHom
