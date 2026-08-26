import GaloisForLFunctions.HTGeometry.CoLieBijective
import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra

/-!
# Co-Lie generators of an additive symmetric algebra

The universal degree-one generators of `SymmetricAlgebra k V` embed in its co-Lie module.  The
proof is functorial and does not choose polynomial coordinates: every linear functional on `V`
lifts to an algebra map into the dual numbers, hence to a point derivation at the identity.
-/

open Coalgebra Bialgebra

namespace GaloisForLFunctions.HTGeometry
namespace SymmetricAlgebraCoLie

noncomputable section

open AffineGroupScheme TrivSqZeroExt

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Scalar projection from the dual numbers. -/
def dualFstAlgHom : DualNumber k →ₐ[k] k where
  toFun z := z.fst
  map_one' := rfl
  map_mul' x y := by simp
  map_zero' := rfl
  map_add' x y := rfl
  commutes' c := rfl

/-- Dual-number point of the additive group determined by a linear functional. -/
noncomputable def dualLift (phi : V →ₗ[k] k) :
    SymmetricAlgebra k V →ₐ[k] DualNumber k :=
  SymmetricAlgebra.lift
    { toFun := fun v => TrivSqZeroExt.inr (phi v)
      map_add' := by intro x y; ext <;> simp
      map_smul' := by intro c x; ext <;> simp }

@[simp] theorem dualLift_ι_fst (phi : V →ₗ[k] k) (v : V) :
    (dualLift phi (SymmetricAlgebra.ι k V v)).fst = 0 := by
  simp [dualLift]

@[simp] theorem dualLift_ι_snd (phi : V →ₗ[k] k) (v : V) :
    (dualLift phi (SymmetricAlgebra.ι k V v)).snd = phi v := by
  simp [dualLift]

theorem dualLift_fst (phi : V →ₗ[k] k) (a : SymmetricAlgebra k V) :
    (dualLift phi a).fst = Coalgebra.counit (R := k) a := by
  have h : (dualFstAlgHom.comp (dualLift phi)) =
      Bialgebra.counitAlgHom k (SymmetricAlgebra k V) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro v
    simp [dualFstAlgHom, SymmetricAlgebra.algebraMapInv_ι]
  exact DFunLike.congr_fun h a

/-- Point derivation of the additive symmetric algebra with prescribed values on generators. -/
noncomputable def pointDerivation (phi : V →ₗ[k] k) :
    pointDerivations k (SymmetricAlgebra k V) :=
  (dualNumberEquiv).symm ⟨dualLift phi, dualLift_fst phi⟩

@[simp] theorem pointDerivation_ι (phi : V →ₗ[k] k) (v : V) :
    (pointDerivation phi : SymmetricAlgebra k V →ₗ[k] k)
      (SymmetricAlgebra.ι k V v) = phi v := by
  change (dualLift phi (SymmetricAlgebra.ι k V v)).snd = phi v
  exact dualLift_ι_snd phi v

/-- Functional induced on the co-Lie module. -/
noncomputable def coLieFunctional (phi : V →ₗ[k] k) :
    coLie k (SymmetricAlgebra k V) →ₗ[k] k :=
  pointDerivationEquiv (pointDerivation phi)

@[simp] theorem coLieFunctional_d_ι (phi : V →ₗ[k] k) (v : V) :
    coLieFunctional phi
      (d k (SymmetricAlgebra k V) (SymmetricAlgebra.ι k V v)) = phi v := by
  rw [coLieFunctional, pointDerivationEquiv_apply_d]
  exact pointDerivation_ι phi v

/-- Degree-one generators mapped into the co-Lie module. -/
noncomputable def generatorCoLieMap :
    V →ₗ[k] coLie k (SymmetricAlgebra k V) :=
  (d k (SymmetricAlgebra k V)).comp (SymmetricAlgebra.ι k V)

/-- The additive generators inject into the co-Lie module. -/
theorem generatorCoLieMap_injective :
    Function.Injective (generatorCoLieMap (k := k) (V := V)) := by
  intro x y hxy
  by_contra hne
  let B := Module.Free.chooseBasis k V
  have hre : B.repr (x - y) ≠ 0 := by
    intro h
    apply hne
    apply sub_eq_zero.mp
    exact B.repr.injective (by simpa using h)
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hre
  let phi : V →ₗ[k] k := B.coord j
  have hfun := congrArg (fun z => coLieFunctional phi z) hxy
  have hph : phi x = phi y := by
    calc
      phi x = coLieFunctional phi
          (d k (SymmetricAlgebra k V) (SymmetricAlgebra.ι k V x)) :=
        (coLieFunctional_d_ι phi x).symm
      _ = coLieFunctional phi
          (d k (SymmetricAlgebra k V) (SymmetricAlgebra.ι k V y)) := by
        exact hfun
      _ = phi y := coLieFunctional_d_ι phi y
  apply hj
  change phi (x - y) = 0
  rw [map_sub, hph, sub_self]

end
end SymmetricAlgebraCoLie
end GaloisForLFunctions.HTGeometry
