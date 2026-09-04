import GaloisForLFunctions.HTGeometry.RationalFunctionConstantBaseChange
import GaloisForLFunctions.HTGeometry.ConstantFieldGaloisBaseChange

/-!
# Finite constant scalar extensions as fraction fields

For a finite extension `S/F` over algebraically closed constants, the standard scalar extension
`Frac(F ⊗ K) ⊗[F] S` is canonically ring-equivalent to `Frac(S ⊗ K)`.  This identifies the Galois
base-change model with the rational-function presentation used by critical source fields.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000

variable {k F S K : Type*} [Field k] [IsAlgClosed k]
  [Field F] [Field S] [Field K]
  [Algebra k F] [Algebra k K] [Algebra F S]
  [Algebra k S] [IsScalarTower k F S]

/-- Canonical field structure on the right-oriented finite scalar extension. -/
@[implicit_reducible] noncomputable instance constantRightScalarExtensionField
    [FiniteDimensional F S] :
    Field (S ⊗[F] constantScalarBase k F K) := by
  let Q := S ⊗[F] constantScalarBase k F K
  letI : IsDomain Q := constantRightFractionTensor_isDomain
  let qComm : Q ≃+* constantScalarExtension k F S K :=
    (Algebra.TensorProduct.comm F S (constantScalarBase k F K)).toRingEquiv
  exact IsField.toField
    { exists_pair_ne := ⟨0, 1, zero_ne_one⟩
      mul_comm := mul_comm
      mul_inv_cancel := by
        intro a ha
        have hqa : qComm a ≠ 0 := qComm.injective.ne ha
        refine ⟨qComm.symm ((qComm a)⁻¹), ?_⟩
        apply qComm.injective
        simp [hqa] }

/-- Localization map after tensoring a finite extension on the left. -/
noncomputable def constantTensorLocalizedBaseMap :
    (S ⊗[F] (F ⊗[k] K)) →ₐ[F]
      (S ⊗[F] constantScalarBase k F K) :=
  tensorBaseHom (k := F) (P := F ⊗[k] K)
    (Q := constantScalarBase k F K) (F := S)

noncomputable instance constantTensorLocalizedAlgebra [FiniteDimensional F S] :
    Algebra (S ⊗[F] (F ⊗[k] K))
      (S ⊗[F] constantScalarBase k F K) :=
  (constantTensorLocalizedBaseMap (k := k) (F := F) (S := S) (K := K)).toRingHom.toAlgebra

noncomputable instance constantTensorLocalizedFaithful [FiniteDimensional F S] :
    FaithfulSMul (S ⊗[F] (F ⊗[k] K))
      (S ⊗[F] constantScalarBase k F K) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2
    (tensorBaseHom_injective (k := F) (P := F ⊗[k] K)
      (Q := constantScalarBase k F K) (F := S))

noncomputable instance constantTensorLocalizedScalarTower [FiniteDimensional F S] :
    IsScalarTower F (S ⊗[F] (F ⊗[k] K))
      (S ⊗[F] constantScalarBase k F K) :=
  IsScalarTower.of_algebraMap_eq fun x =>
    ((constantTensorLocalizedBaseMap
      (k := k) (F := F) (S := S) (K := K)).commutes x).symm

/-- Tensoring a finite extension with the fraction field of the constant tensor produces the
fraction field of the unlocalized tensor. -/
noncomputable instance constantTensorLocalizedIsFractionRing [FiniteDimensional F S] :
    IsFractionRing (S ⊗[F] (F ⊗[k] K))
      (S ⊗[F] constantScalarBase k F K) := by
  apply IsFractionRing.of_field _ _
  intro z
  obtain ⟨q, hq, eta, heta⟩ :=
    exists_denominator_clears (k := F) (P := F ⊗[k] K)
      (Q := constantScalarBase k F K) (F := S) z
  let d : S ⊗[F] (F ⊗[k] K) := (1 : S) ⊗ₜ[F] q
  have hunitB : IsUnit
      (algebraMap (F ⊗[k] K) (constantScalarBase k F K) q) :=
    IsLocalization.map_units (constantScalarBase k F K)
      ⟨q, mem_nonZeroDivisors_of_ne_zero hq⟩
  have hunitQ : IsUnit ((1 : S) ⊗ₜ[F]
      (algebraMap (F ⊗[k] K) (constantScalarBase k F K) q)) :=
    hunitB.map
      (Algebra.TensorProduct.includeRight :
        constantScalarBase k F K →ₐ[F]
          S ⊗[F] constantScalarBase k F K).toRingHom
  have hd : algebraMap (S ⊗[F] (F ⊗[k] K))
      (S ⊗[F] constantScalarBase k F K) d ≠ 0 := by
    change (1 : S) ⊗ₜ[F]
      (algebraMap (F ⊗[k] K) (constantScalarBase k F K) q) ≠ 0
    exact hunitQ.ne_zero
  refine ⟨eta, d, ?_⟩
  apply (eq_div_iff hd).2
  change z * constantTensorLocalizedBaseMap
      (k := k) (F := F) (S := S) (K := K) d =
    constantTensorLocalizedBaseMap
      (k := k) (F := F) (S := S) (K := K) eta
  have hdmap : constantTensorLocalizedBaseMap
      (k := k) (F := F) (S := S) (K := K) d =
      (1 : S) ⊗ₜ[F]
        (algebraMap (F ⊗[k] K) (constantScalarBase k F K) q) := rfl
  rw [hdmap]
  simpa [constantTensorLocalizedBaseMap, mul_comm] using heta

/-- The standard finite scalar extension is the fraction field of the full constant tensor. -/
noncomputable def constantScalarExtensionFractionRingEquiv
    [FiniteDimensional F S] :
    constantScalarExtension k F S K ≃+* FractionRing (S ⊗[k] K) := by
  let P := F ⊗[k] K
  let B := constantScalarBase k F K
  let A := S ⊗[F] P
  let Q := S ⊗[F] B
  let T := S ⊗[k] K
  let U := FractionRing T
  let e : A ≃ₐ[S] T := Algebra.TensorProduct.cancelBaseChange k F S S K
  let eF : A ≃ₐ[F] T := e.restrictScalars F
  let qToU : Q ≃ₐ[F] U := IsFractionRing.algEquivOfAlgEquiv eF
  exact (Algebra.TensorProduct.comm F B S).toRingEquiv.trans qToU.toRingEquiv

@[simp] theorem constantScalarExtensionFractionRingEquiv_base
    [FiniteDimensional F S] (p : F ⊗[k] K) :
    constantScalarExtensionFractionRingEquiv
        (k := k) (F := F) (S := S) (K := K)
        (algebraMap (constantScalarBase k F K)
          (constantScalarExtension k F S K)
          (algebraMap (F ⊗[k] K) (constantScalarBase k F K) p)) =
      algebraMap (S ⊗[k] K) (FractionRing (S ⊗[k] K))
        ((Algebra.TensorProduct.cancelBaseChange k F S S K)
          ((1 : S) ⊗ₜ[F] p)) := by
  simp [constantScalarExtensionFractionRingEquiv]
  rw [show (1 : S) ⊗ₜ[F]
        (algebraMap (F ⊗[k] K) (constantScalarBase k F K) p) =
      algebraMap (S ⊗[F] (F ⊗[k] K))
        (S ⊗[F] constantScalarBase k F K) ((1 : S) ⊗ₜ[F] p) by rfl]
  rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  rfl

end

end GaloisForLFunctions.HTGeometry
