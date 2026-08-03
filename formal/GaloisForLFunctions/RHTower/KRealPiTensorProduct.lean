import GaloisForLFunctions.RHTower.KRealTensorProduct
import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Real structures on indexed tensor products

An indexed tensor product of complex vector spaces carrying even Real structures inherits the
componentwise conjugate-linear involution.  The construction is made directly from
`PiTensorProduct.liftAddHom`, so it handles the balanced scalar relation correctly in every
finite cyclic degree, including degree zero.

This is the tensor-universal-property layer needed to put an actual degreewise Real structure on
cyclic bar modules.  No finite-dimensional model or pure-word proxy is used.
-/

noncomputable section

open scoped TensorProduct

namespace GaloisForLFunctions
namespace RHTower

variable {ι : Type*} {M : ι → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

private theorem kRealPiTensor_sigma_update
    (K : ∀ i, KRealStructure false (M i)) [DecidableEq ι]
    (f : ∀ i, M i) (i : ι) (x : M i) :
    (fun j => (K j).sigma (Function.update f i x j)) =
      Function.update (fun j => (K j).sigma (f j)) i ((K i).sigma x) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [Function.update_of_ne hji]

/-- Componentwise Real action on an indexed tensor product, bundled additively first. -/
def kRealEvenPiTensorSigmaAddHom
    (K : ∀ i, KRealStructure false (M i)) :
    PiTensorProduct ℂ M →+ PiTensorProduct ℂ M :=
  PiTensorProduct.liftAddHom
    (fun p : ℂ × (∀ i, M i) =>
      PiTensorProduct.tprodCoeff ℂ (star p.1)
        (fun i => (K i).sigma (p.2 i)))
    (by
      intro r f i hfi
      apply PiTensorProduct.zero_tprodCoeff' (star r)
        (fun j => (K j).sigma (f j)) i
      rw [hfi]
      exact map_zero _)
    (by
      intro f
      change PiTensorProduct.tprodCoeff ℂ (star (0 : ℂ))
          (fun i => (K i).sigma (f i)) = 0
      have hzero : star (0 : ℂ) = 0 := by
        change (starRingEnd ℂ) 0 = 0
        exact map_zero (starRingEnd ℂ)
      rw [hzero]
      exact PiTensorProduct.zero_tprodCoeff (R := ℂ) (s := M)
        (fun i => (K i).sigma (f i)))
    (by
      intro inst r f i m₁ m₂
      rw [kRealPiTensor_sigma_update K f i m₁,
        kRealPiTensor_sigma_update K f i m₂,
        kRealPiTensor_sigma_update K f i (m₁ + m₂), map_add]
      exact PiTensorProduct.add_tprodCoeff (R := ℂ) (s := M)
        (star r) (fun j => (K j).sigma (f j)) i
        ((K i).sigma m₁) ((K i).sigma m₂))
    (by
      intro r r' f
      change PiTensorProduct.tprodCoeff ℂ (star r)
          (fun i => (K i).sigma (f i)) +
          PiTensorProduct.tprodCoeff ℂ (star r')
            (fun i => (K i).sigma (f i)) =
        PiTensorProduct.tprodCoeff ℂ (star (r + r'))
          (fun i => (K i).sigma (f i))
      have hstar : star (r + r') = star r + star r' := by
        change (starRingEnd ℂ) (r + r') =
          (starRingEnd ℂ) r + (starRingEnd ℂ) r'
        exact map_add (starRingEnd ℂ) r r'
      rw [hstar]
      exact PiTensorProduct.add_tprodCoeff' (star r) (star r')
        (fun i => (K i).sigma (f i)))
    (by
      intro inst r f i r'
      rw [kRealPiTensor_sigma_update K f i (r' • f i), map_smulₛₗ]
      change PiTensorProduct.tprodCoeff ℂ (star r)
          (Function.update (fun j => (K j).sigma (f j)) i
            (star r' • (K i).sigma (f i))) =
        PiTensorProduct.tprodCoeff ℂ (star (r' * r))
          (fun j => (K j).sigma (f j))
      rw [PiTensorProduct.smul_tprodCoeff_aux]
      have hstar : star (r' * r) = star r' * star r := by
        change (starRingEnd ℂ) (r' * r) =
          (starRingEnd ℂ) r' * (starRingEnd ℂ) r
        exact map_mul (starRingEnd ℂ) r' r
      rw [hstar])

@[simp]
theorem kRealEvenPiTensorSigmaAddHom_tprodCoeff
    (K : ∀ i, KRealStructure false (M i)) (r : ℂ) (f : ∀ i, M i) :
    kRealEvenPiTensorSigmaAddHom K (PiTensorProduct.tprodCoeff ℂ r f) =
      PiTensorProduct.tprodCoeff ℂ (star r)
        (fun i => (K i).sigma (f i)) := by
  rfl

@[simp]
theorem kRealEvenPiTensorSigmaAddHom_tprod
    (K : ∀ i, KRealStructure false (M i)) (f : ∀ i, M i) :
    kRealEvenPiTensorSigmaAddHom K (PiTensorProduct.tprod ℂ f) =
      PiTensorProduct.tprod ℂ (fun i => (K i).sigma (f i)) := by
  rw [PiTensorProduct.tprod_eq_tprodCoeff_one,
    kRealEvenPiTensorSigmaAddHom_tprodCoeff]
  have hone : star (1 : ℂ) = 1 := by
    change (starRingEnd ℂ) 1 = 1
    exact map_one (starRingEnd ℂ)
  rw [hone]

/-- Componentwise Real action on an indexed tensor product, bundled conjugate-linearly. -/
def kRealEvenPiTensorSigma
    (K : ∀ i, KRealStructure false (M i)) :
    PiTensorProduct ℂ M →ₗ⋆[ℂ] PiTensorProduct ℂ M where
  toFun := kRealEvenPiTensorSigmaAddHom K
  map_add' := map_add _
  map_smul' z x := by
    induction x using PiTensorProduct.induction_on' with
    | tprodCoeff r f =>
        rw [PiTensorProduct.smul_tprodCoeff',
          kRealEvenPiTensorSigmaAddHom_tprodCoeff,
          kRealEvenPiTensorSigmaAddHom_tprodCoeff,
          PiTensorProduct.smul_tprodCoeff']
        change PiTensorProduct.tprodCoeff ℂ (star (z * r))
            (fun i => (K i).sigma (f i)) =
          PiTensorProduct.tprodCoeff ℂ (star z * star r)
            (fun i => (K i).sigma (f i))
        have hstar : star (z * r) = star z * star r := by
          change (starRingEnd ℂ) (z * r) =
            (starRingEnd ℂ) z * (starRingEnd ℂ) r
          exact map_mul (starRingEnd ℂ) z r
        rw [hstar]
    | add x y hx hy =>
        simp only [smul_add, map_add, hx, hy]

@[simp]
theorem kRealEvenPiTensorSigma_tprod
    (K : ∀ i, KRealStructure false (M i)) (f : ∀ i, M i) :
    kRealEvenPiTensorSigma K (PiTensorProduct.tprod ℂ f) =
      PiTensorProduct.tprod ℂ (fun i => (K i).sigma (f i)) :=
  kRealEvenPiTensorSigmaAddHom_tprod K f

/-- Componentwise indexed tensor Real action squares to the identity. -/
theorem kRealEvenPiTensorSigma_sq
    (K : ∀ i, KRealStructure false (M i))
    (x : PiTensorProduct ℂ M) :
    kRealEvenPiTensorSigma K (kRealEvenPiTensorSigma K x) = x := by
  induction x using PiTensorProduct.induction_on' with
  | tprodCoeff r f =>
      change kRealEvenPiTensorSigmaAddHom K
          (kRealEvenPiTensorSigmaAddHom K
            (PiTensorProduct.tprodCoeff ℂ r f)) =
        PiTensorProduct.tprodCoeff ℂ r f
      rw [kRealEvenPiTensorSigmaAddHom_tprodCoeff,
        kRealEvenPiTensorSigmaAddHom_tprodCoeff]
      change PiTensorProduct.tprodCoeff ℂ (star (star r))
          (fun i => (K i).sigma ((K i).sigma (f i))) =
        PiTensorProduct.tprodCoeff ℂ r f
      rw [star_star]
      congr 1
      funext i
      exact (K i).sq (f i)
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Even Real structure on the indexed complex tensor product. -/
def kRealEvenPiTensorProduct
    (K : ∀ i, KRealStructure false (M i)) :
    KRealStructure false (PiTensorProduct ℂ M) where
  sigma := kRealEvenPiTensorSigma K
  sq x := by
    simpa [kRealParityAction] using kRealEvenPiTensorSigma_sq K x

end RHTower
end GaloisForLFunctions
