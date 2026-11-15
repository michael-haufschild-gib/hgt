import GaloisForLFunctions.HTGeometry.Homology.CyclicOneFunctor
import GaloisForLFunctions.HTGeometry.AlternatingChordLaw
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Cyclic degree one of a square-zero algebra

Projecting both tensor factors to the tangent space gives an exterior product
that kills Hochschild boundaries and signed rotations. Pure tangent tensors
provide its inverse: scalar factors vanish in the cyclic quotient. Thus the
full ordinary cyclic degree one is exactly the second exterior power, without
finite-dimensionality or a choice of tangent basis.
-/

noncomputable section
namespace GaloisForLFunctions.RHTower.SquareZeroCyclic
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The exterior product of two tangent vectors. -/
def tangentWedge (x y : V) : ⋀[ℂ]^2 V := exteriorPower.ιMulti ℂ 2 ![x,y]

@[simp] theorem tangentWedge_add_left (x y z : V) :
    tangentWedge (x+y) z = tangentWedge x z + tangentWedge y z :=
  HTGeometry.altPair_add_left (exteriorPower.ιMulti ℂ 2) x y z

@[simp] theorem tangentWedge_add_right (x y z : V) :
    tangentWedge x (y+z) = tangentWedge x y + tangentWedge x z :=
  HTGeometry.altPair_add_right (exteriorPower.ιMulti ℂ 2) x y z

@[simp] theorem tangentWedge_smul_left (c : ℂ) (x y : V) :
    tangentWedge (c • x) y = c • tangentWedge x y :=
  HTGeometry.altPair_smul_left (exteriorPower.ιMulti ℂ 2) c x y

@[simp] theorem tangentWedge_smul_right (c : ℂ) (x y : V) :
    tangentWedge x (c • y) = c • tangentWedge x y :=
  HTGeometry.altPair_smul_right (exteriorPower.ιMulti ℂ 2) c x y

@[simp] theorem tangentWedge_self (x : V) : tangentWedge x x = 0 :=
  HTGeometry.altPair_self (exteriorPower.ιMulti ℂ 2) x

theorem tangentWedge_swap (x y : V) : tangentWedge y x = -tangentWedge x y :=
  HTGeometry.altPair_swap (exteriorPower.ιMulti ℂ 2) x y

@[simp] theorem tangentWedge_zero_left (y : V) : tangentWedge 0 y = 0 :=
  (exteriorPower.ιMulti ℂ 2).map_coord_zero (0 : Fin 2) rfl

@[simp] theorem tangentWedge_zero_right (x : V) : tangentWedge x 0 = 0 :=
  (exteriorPower.ιMulti ℂ 2).map_coord_zero (1 : Fin 2) rfl

variable [Module ℂᵐᵒᵖ V] [IsCentralScalar ℂ V]

/-- Project both tensor factors to the tangent and take their exterior product. -/
def squareZeroWedgeChain : CyclicBarTensor ℂ (TrivSqZeroExt ℂ V) 1 →ₗ[ℂ] ⋀[ℂ]^2 V :=
  PiTensorProduct.lift ((exteriorPower.ιMulti ℂ 2).toMultilinearMap.compLinearMap
    (fun _ => TrivSqZeroExt.sndHom ℂ V))

@[simp] theorem squareZeroWedgeChain_pair (a b : TrivSqZeroExt ℂ V) :
    squareZeroWedgeChain (pair a b) = tangentWedge a.snd b.snd := by
  rw [squareZeroWedgeChain, pair, PiTensorProduct.lift.tprod]
  change exteriorPower.ιMulti ℂ 2 (fun i => (![a,b] i).snd) = _
  have h : (fun i => (![a,b] i).snd) = ![a.snd,b.snd] := by
    ext i; fin_cases i <;> rfl
  rw [h]
  rfl

private theorem squareZeroWedgeChain_boundary :
    (squareZeroWedgeChain (V := V)).comp boundaryTwo = 0 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change squareZeroWedgeChain (boundaryTwo (PiTensorProduct.tprod ℂ x)) = 0
  have hx : x = ![x 0, x 1, x 2] := by funext i; fin_cases i <;> rfl
  rw [hx]
  change squareZeroWedgeChain (boundaryTwo (triple _ _ _)) = 0
  rw [boundaryTwo_triple]
  simp only [map_add, map_sub, squareZeroWedgeChain_pair, TrivSqZeroExt.snd_mul,
    op_smul_eq_smul, tangentWedge_add_left, tangentWedge_add_right,
    tangentWedge_smul_left, tangentWedge_smul_right]
  rw [tangentWedge_swap (x 1).snd (x 2).snd, smul_neg]
  abel

private theorem squareZeroWedgeChain_rotation :
    (squareZeroWedgeChain (V := V)).comp
      (LinearMap.id + (cyclicBarRotate (R := ℂ) (A := TrivSqZeroExt ℂ V) 1).toLinearMap) = 0 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
  change squareZeroWedgeChain (PiTensorProduct.tprod ℂ x +
    cyclicBarRotate (R := ℂ) 1 (PiTensorProduct.tprod ℂ x)) = 0
  rw [hx]
  change squareZeroWedgeChain (pair _ _ + cyclicBarRotate (R := ℂ) 1 (pair _ _)) = 0
  rw [rotate_pair, map_add, squareZeroWedgeChain_pair, squareZeroWedgeChain_pair,
    tangentWedge_swap (x 0).snd (x 1).snd, add_neg_cancel]

/-- The exterior tangent moment on actual cyclic homology. -/
def squareZeroCyclicToExterior : CyclicOne (TrivSqZeroExt ℂ V) →ₗ[ℂ] ⋀[ℂ]^2 V :=
  (cyclicRelations (A := TrivSqZeroExt ℂ V)).liftQ squareZeroWedgeChain (by
    apply sup_le
    · rintro _ ⟨x, rfl⟩
      exact LinearMap.congr_fun (squareZeroWedgeChain_boundary (V := V)) x
    · rintro _ ⟨x, rfl⟩
      exact LinearMap.congr_fun (squareZeroWedgeChain_rotation (V := V)) x)

@[simp] theorem squareZeroCyclicToExterior_class (a b : TrivSqZeroExt ℂ V) :
    squareZeroCyclicToExterior (cyclicClass a b) = tangentWedge a.snd b.snd :=
  squareZeroWedgeChain_pair a b

/-- Pure tangent two-tensors define an alternating map to cyclic degree one. -/
def squareZeroCyclicAlternating : V [⋀^Fin 2]→ₗ[ℂ] CyclicOne (TrivSqZeroExt ℂ V) where
  toFun x := cyclicClass ((TrivSqZeroExt.inrHom ℂ V) (x 0))
    ((TrivSqZeroExt.inrHom ℂ V) (x 1))
  map_update_add' := by intro _ x i a b; fin_cases i <;> simp [Function.update]
  map_update_smul' := by intro _ x i c a; fin_cases i <;> simp [Function.update]
  map_eq_zero_of_eq' := by
    intro x i j h hne
    have h01 : x 0 = x 1 := by fin_cases i <;> fin_cases j <;> simp_all
    rw [h01]
    exact cyclicClass_self _

/-- Exterior tangent classes are represented by pure tangent two-tensors. -/
def squareZeroExteriorToCyclic : (⋀[ℂ]^2 V) →ₗ[ℂ] CyclicOne (TrivSqZeroExt ℂ V) :=
  exteriorPower.alternatingMapLinearEquiv squareZeroCyclicAlternating

@[simp] theorem squareZeroExteriorToCyclic_wedge (x y : V) :
    squareZeroExteriorToCyclic (tangentWedge x y) =
      cyclicClass (TrivSqZeroExt.inr x) (TrivSqZeroExt.inr y) := by
  rw [squareZeroExteriorToCyclic, tangentWedge,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- Scalar tensor factors disappear, leaving only the exterior tangent part. -/
theorem squareZero_cyclicClass_reduction (a b : TrivSqZeroExt ℂ V) :
    cyclicClass a b = cyclicClass (TrivSqZeroExt.inr a.snd) (TrivSqZeroExt.inr b.snd) := by
  have ha : a = a.fst • 1 + TrivSqZeroExt.inr a.snd := by
    apply TrivSqZeroExt.ext <;> simp
  have hb : b = b.fst • 1 + TrivSqZeroExt.inr b.snd := by
    apply TrivSqZeroExt.ext <;> simp
  calc
    cyclicClass a b = cyclicClass (a.fst • 1 + TrivSqZeroExt.inr a.snd)
        (b.fst • 1 + TrivSqZeroExt.inr b.snd) := congrArg₂ cyclicClass ha hb
    _ = _ := by simp

theorem squareZero_exterior_cyclic_inverse :
    (squareZeroCyclicToExterior (V := V)).comp squareZeroExteriorToCyclic = LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
  change squareZeroCyclicToExterior (squareZeroExteriorToCyclic (exteriorPower.ιMulti ℂ 2 x)) = _
  rw [hx]
  change squareZeroCyclicToExterior (squareZeroExteriorToCyclic (tangentWedge _ _)) = tangentWedge _ _
  rw [squareZeroExteriorToCyclic_wedge, squareZeroCyclicToExterior_class,
    TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_inr]

theorem squareZero_cyclic_exterior_inverse :
    (squareZeroExteriorToCyclic (V := V)).comp squareZeroCyclicToExterior = LinearMap.id := by
  apply cyclicOne_linearMap_ext
  intro a b
  change squareZeroExteriorToCyclic (squareZeroCyclicToExterior (cyclicClass a b)) = cyclicClass a b
  rw [squareZeroCyclicToExterior_class, squareZeroExteriorToCyclic_wedge]
  exact (squareZero_cyclicClass_reduction a b).symm

/-- Ordinary cyclic homology of a square-zero complex algebra is the full second exterior power. -/
def squareZeroCyclicEquiv : CyclicOne (TrivSqZeroExt ℂ V) ≃ₗ[ℂ] ⋀[ℂ]^2 V :=
  { squareZeroCyclicToExterior with
    invFun := squareZeroExteriorToCyclic
    left_inv := fun x => LinearMap.congr_fun squareZero_cyclic_exterior_inverse x
    right_inv := fun x => LinearMap.congr_fun squareZero_exterior_cyclic_inverse x }

@[simp] theorem squareZeroCyclicEquiv_class (a b : TrivSqZeroExt ℂ V) :
    squareZeroCyclicEquiv (cyclicClass a b) = tangentWedge a.snd b.snd :=
  squareZeroCyclicToExterior_class a b

#print axioms squareZeroCyclicEquiv
#print axioms squareZero_cyclicClass_reduction
end GaloisForLFunctions.RHTower.SquareZeroCyclic
