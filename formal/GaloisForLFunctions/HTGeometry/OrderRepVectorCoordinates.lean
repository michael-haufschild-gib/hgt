import GaloisForLFunctions.HTGeometry.OrderSchurRestriction
import GaloisForLFunctions.HTGeometry.NumberFieldOrderFormPrimitiveMinimum

/-!
# Regular-representation action on order-vector coordinates

The flattened regular representation acts on basis-coordinate vectors exactly as the original
matrix acts over the order.  For a number ring these coordinates are identified with the canonical
mixed-embedding coordinates used by the primitive-minimum theorem.  This closes the coordinate
transport needed to normalize its minimizing vector by a determinant-one basis change.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open NumberField
open scoped Classical NumberField

variable {n d : ℕ} {R : Type*} [CommRing R]

noncomputable def orderVectorCoordsZ (ω : Module.Basis (Fin d) ℤ R) (a : Fin n → R) :
    Fin (n * d) → ℤ :=
  fun p => ω.repr (a (Fin.divNat p)) (Fin.modNat p)

@[simp]
theorem orderVectorCoordsZ_apply (ω : Module.Basis (Fin d) ℤ R) (a : Fin n → R)
    (i : Fin n) (k : Fin d) :
    orderVectorCoordsZ ω a (finProdFinEquiv (i, k)) = ω.repr (a i) k := by
  rw [orderVectorCoordsZ, divNat_finProdFinEquiv, modNat_finProdFinEquiv]

theorem orderRep_mulVec_orderVectorCoordsZ (ω : Module.Basis (Fin d) ℤ R)
    (M : Matrix (Fin n) (Fin n) R) (a : Fin n → R) :
    orderRep ω M *ᵥ orderVectorCoordsZ ω a = orderVectorCoordsZ ω (M *ᵥ a) := by
  funext p
  rw [← finProdFinEquiv_divNat_modNat p]
  let i := Fin.divNat p
  let k := Fin.modNat p
  rw [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp (finProdFinEquiv (m := n) (n := d))
    (fun r : Fin (n * d) => orderRep ω M (finProdFinEquiv (i, k)) r *
      orderVectorCoordsZ ω a r)]
  rw [Fintype.sum_prod_type]
  simp only [orderRep, blockEmbed_apply, Matrix.map_apply, orderVectorCoordsZ_apply]
  change (∑ j : Fin n, ∑ l : Fin d,
      Algebra.leftMulMatrix ω (M i j) k l * ω.repr (a j) l) =
    ω.repr ((M *ᵥ a) i) k
  calc
    (∑ j : Fin n, ∑ l : Fin d,
        Algebra.leftMulMatrix ω (M i j) k l * ω.repr (a j) l) =
        ∑ j : Fin n, ω.repr (M i j * a j) k := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have h := LinearMap.toMatrix_mulVec_repr ω ω ((Algebra.lmul ℤ R) (M i j)) (a j)
      exact congrFun h k
    _ = ω.repr ((M *ᵥ a) i) k := by
      rw [Matrix.mulVec, dotProduct]
      simp

noncomputable def orderVectorCoordsR (ω : Module.Basis (Fin d) ℤ R) (a : Fin n → R) :
    Fin (n * d) → ℝ :=
  fun p => (orderVectorCoordsZ ω a p : ℝ)

@[simp]
theorem orderVectorCoordsR_apply (ω : Module.Basis (Fin d) ℤ R) (a : Fin n → R)
    (i : Fin n) (k : Fin d) :
    orderVectorCoordsR ω a (finProdFinEquiv (i, k)) = (ω.repr (a i) k : ℝ) := by
  rw [orderVectorCoordsR, orderVectorCoordsZ_apply]

theorem orderRepR_mulVec_orderVectorCoordsR (ω : Module.Basis (Fin d) ℤ R)
    (M : Matrix (Fin n) (Fin n) R) (a : Fin n → R) :
    orderRepR ω M *ᵥ orderVectorCoordsR ω a = orderVectorCoordsR ω (M *ᵥ a) := by
  have hz := orderRep_mulVec_orderVectorCoordsZ ω M a
  funext p
  have hp := congrFun hz p
  rw [Matrix.mulVec, dotProduct]
  change (∑ j, ((orderRep ω M p j : ℤ) : ℝ) * (orderVectorCoordsZ ω a j : ℝ)) =
    (orderVectorCoordsZ ω (M *ᵥ a) p : ℝ)
  exact_mod_cast hp

theorem numberField_orderVectorCoordsR_eq
    (K : Type*) [Field K] [NumberField K] {n : ℕ} (a : Fin n → 𝓞 K) :
    orderVectorCoordsR (numberFieldIntegerBasis K) a =
      numberFieldMixedVectorContinuousLinearEquiv K n
        (numberFieldIntegerVectorEmbedding K a) := by
  funext p
  rw [← finProdFinEquiv_divNat_modNat p]
  rw [orderVectorCoordsR_apply]
  rw [← numberFieldMixedVectorBasis_repr_integer K a]
  rfl

theorem numberField_orderRepR_mulVec_mixedCoordinates
    (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (𝓞 K)) (a : Fin n → 𝓞 K) :
    orderRepR (numberFieldIntegerBasis K) M *ᵥ
        numberFieldMixedVectorContinuousLinearEquiv K n
          (numberFieldIntegerVectorEmbedding K a) =
      numberFieldMixedVectorContinuousLinearEquiv K n
        (numberFieldIntegerVectorEmbedding K (M *ᵥ a)) := by
  rw [← numberField_orderVectorCoordsR_eq, ← numberField_orderVectorCoordsR_eq]
  exact orderRepR_mulVec_orderVectorCoordsR (numberFieldIntegerBasis K) M a

end GaloisForLFunctions.HTGeometry
