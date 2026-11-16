import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerConstantBaseChange
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.PolynomialNormalizationConstantBaseChange

/-!
# Constant tensors of Kummer normalizations

The function-field tensor isomorphism preserves the rational coordinate and
radical. It therefore respects the enlarged polynomial base. Smooth base
change identifies the actual affine normalization over the enlarged constants
with the literal constant tensor of the original normalization.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open scoped TensorProduct
attribute [local instance] Polynomial.algebra
variable (K E : Type*) [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
    (c : Kˣ) (b R n : ℕ)
local notation "L" => KummerBranchField c b R n
local notation "cE" => Units.map (RingHom.toMonoidHom (algebraMap K E)) c
local notation "LE" => KummerBranchField cE b R n

/-- The literal constant-tensor isomorphism preserves the radical generator. -/
theorem kummerConstantTensorEquiv_root :
    kummerConstantTensorEquiv K E c b R n
      ((1 : E) ⊗ₜ[K] AdjoinRoot.root (kummerBranchFieldPolynomial c b R n)) =
      AdjoinRoot.root (kummerBranchFieldPolynomial cE b R n) := by
  rw [kummerConstantTensorEquiv, AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_root,
    AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_root]

/-- The literal constant-tensor isomorphism preserves the rational coordinate. -/
theorem kummerConstantTensorEquiv_coordinate :
    kummerConstantTensorEquiv K E c b R n ((1 : E) ⊗ₜ[K] algebraMap K[X] L X) =
      algebraMap E[X] LE X := by
  rw [IsScalarTower.algebraMap_apply K[X] (FractionRing K[X]) L,
    AdjoinRoot.algebraMap_eq, kummerConstantTensorEquiv, AlgEquiv.trans_apply,
    AdjoinRoot.tensorAlgEquiv_of, AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_of]
  change algebraMap (FractionRing E[X]) LE
    (rationalConstantTensorEquiv K E ((1 : E) ⊗ₜ[K] algebraMap K[X] (FractionRing K[X]) X)) = _
  rw [rationalConstantTensorEquiv_X, ← IsScalarTower.algebraMap_apply]

/-- Polynomial base change of the original field is the same Kummer equation over the enlarged constants. -/
def kummerPolynomialConstantTensorEquiv :
    (E[X] ⊗[K[X]] L) ≃ₐ[E[X]] LE := by
  let e := (Algebra.IsPushout.cancelBaseChangeAlg K E K[X] E[X] L).trans
    (kummerConstantTensorEquiv K E c b R n)
  apply AlgEquiv.ofRingEquiv (f := e.toRingEquiv)
  intro P
  have hcomm : e.toRingHom.comp (algebraMap E[X] (E[X] ⊗[K[X]] L)) =
      algebraMap E[X] LE := by
    apply Polynomial.ringHom_ext
    · intro a
      change e (algebraMap E (E[X] ⊗[K[X]] L) a) = algebraMap E LE a
      exact e.commutes a
    · have hbase : (1 : E[X]) ⊗ₜ[K[X]] algebraMap K[X] L X =
          algebraMap E[X] (E[X] ⊗[K[X]] L) X := by
        calc
          _ = algebraMap K[X] (E[X] ⊗[K[X]] L) X :=
            (Algebra.TensorProduct.includeRight (R := K[X]) (A := E[X]) (B := L)).commutes X
          _ = algebraMap E[X] (E[X] ⊗[K[X]] L) ((X : K[X]).map (algebraMap K E)) :=
            IsScalarTower.algebraMap_apply K[X] E[X] (E[X] ⊗[K[X]] L) X
          _ = _ := congrArg (algebraMap E[X] (E[X] ⊗[K[X]] L)) (Polynomial.map_X _)
      change e (algebraMap E[X] (E[X] ⊗[K[X]] L) X) = algebraMap E[X] LE X
      rw [← hbase]
      change kummerConstantTensorEquiv K E c b R n
        ((Algebra.IsPushout.cancelBaseChangeAlg K E K[X] E[X] L)
          ((1 : E[X]) ⊗ₜ[K[X]] algebraMap K[X] L X)) = _
      rw [Algebra.IsPushout.cancelBaseChangeAlg_tmul, kummerConstantTensorEquiv_coordinate]
  exact RingHom.congr_fun hcomm P

variable [Algebra.IsSeparable K E]

/-- Finite separable constant extension commutes with the actual Kummer affine normalization. -/
def kummerNormalizationConstantTensorEquiv :
    (E ⊗[K] integralClosure K[X] L) ≃ₐ[E] integralClosure E[X] LE :=
  (polynomialNormalizationConstantTensorEquiv K E L).trans
    ((kummerPolynomialConstantTensorEquiv K E c b R n).mapIntegralClosure.restrictScalars E)

/-- On integral elements, the normalization comparison is the original function-field tensor map. -/
theorem kummerNormalizationConstantTensorEquiv_tmul (a : E) (x : integralClosure K[X] L) :
    (kummerNormalizationConstantTensorEquiv K E c b R n (a ⊗ₜ[K] x)).val =
      kummerConstantTensorEquiv K E c b R n (a ⊗ₜ[K] (x.val : L)) := by
  change kummerPolynomialConstantTensorEquiv K E c b R n
    (polynomialNormalizationConstantTensorEquiv K E L (a ⊗ₜ[K] x)).val = _
  rw [polynomialNormalizationConstantTensorEquiv_tmul]
  have h := (Algebra.IsPushout.cancelBaseChangeAlg K E K[X] E[X] L).apply_symm_apply
    (a ⊗ₜ[K] (x.val : L))
  rw [Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul] at h
  exact congrArg (kummerConstantTensorEquiv K E c b R n) h

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
