import GaloisForLFunctions.HTGeometry.HardyBlaschkeNumberModes
import GaloisForLFunctions.HTGeometry.ClosedEigenbasisDomain
import GaloisForLFunctions.HTGeometry.LinearPMapBoundedUnitaryTransport

/-!
# The actual number-minus-KMS operator in the Blaschke basis

The bounded geometric kernel perturbs the maximal number operator. Its complete
Blaschke basis diagonalizes this actual operator and identifies its full domain.
-/

noncomputable section

open scoped InnerProductSpace LinearPMap

namespace GaloisForLFunctions.HTGeometry

variable {q : ℝ}

/-- Multiplication by the nonnegative integer coordinate on its maximal domain. -/
def hardyNumber : HardyDisk →ₗ.[ℂ] HardyDisk :=
  RHTower.maximalRealDiagonal (fun n : ℕ => (n : ℝ))

/-- The actual number-minus-KMS operator, including the restored unit diagonal. -/
def hardyNumberMinusKMS (hq : ‖(q : ℂ)‖ < 1) : HardyDisk →ₗ.[ℂ] HardyDisk :=
  (1 - hardyGeometricKMS hq).toLinearMap +ᵥ hardyNumber

theorem hardyNumberMinusKMS_domain (hq : ‖(q : ℂ)‖ < 1) :
    (hardyNumberMinusKMS hq).domain =
      RHTower.maximalRealDiagonalDomain (fun n : ℕ => (n : ℝ)) := rfl

theorem hardyNumberMinusKMS_apply (hq : ‖(q : ℂ)‖ < 1)
    (x : (hardyNumberMinusKMS hq).domain) (n : ℕ) :
    hardyNumberMinusKMS hq x n = (n : ℂ) * (x : HardyDisk) n -
      hardyGeometricKMS hq (x : HardyDisk) n + (x : HardyDisk) n := by
  change (x : HardyDisk) n - hardyGeometricKMS hq (x : HardyDisk) n +
    ((n : ℝ) : ℂ) * (x : HardyDisk) n = _
  rw [Complex.ofReal_natCast]
  ring

theorem hardyNumberMinusKMS_isClosed (hq : ‖(q : ℂ)‖ < 1) :
    (hardyNumberMinusKMS hq).IsClosed := by
  have hd := (RHTower.maximalRealDiagonal_isSelfAdjoint (fun n : ℕ => (n : ℝ))).isClosed
  exact LinearPMap.IsClosed.continuousLinearMap_vadd hd (1 - hardyGeometricKMS hq)

theorem hardyNumberMinusKMS_formalSelfAdjoint (hq : ‖(q : ℂ)‖ < 1) :
    (hardyNumberMinusKMS hq).IsFormalAdjoint (hardyNumberMinusKMS hq) := by
  intro x y
  let xD : hardyNumber.domain := ⟨(x : HardyDisk), x.property⟩
  let yD : hardyNumber.domain := ⟨(y : HardyDisk), y.property⟩
  change inner ℂ ((x : HardyDisk) - hardyGeometricKMS hq (x : HardyDisk) +
      hardyNumber xD) (y : HardyDisk) =
    inner ℂ (x : HardyDisk) ((y : HardyDisk) - hardyGeometricKMS hq (y : HardyDisk) +
      hardyNumber yD)
  rw [inner_add_left, inner_sub_left, inner_add_right, inner_sub_right]
  have hk := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (hardyGeometricKMS_isSelfAdjoint hq)
  have hk' : inner ℂ (hardyGeometricKMS hq (x : HardyDisk)) (y : HardyDisk) =
      inner ℂ (x : HardyDisk) (hardyGeometricKMS hq (y : HardyDisk)) := hk _ _
  rw [hk']
  exact congrArg (fun z : ℂ => inner ℂ (x : HardyDisk) (y : HardyDisk) -
    inner ℂ (x : HardyDisk) (hardyGeometricKMS hq (y : HardyDisk)) + z)
      (RHTower.maximalRealDiagonal_formalSelfAdjoint (fun n : ℕ => (n : ℝ)) xD yD)

/-- The geometric ground energy and the positive integer excitations. -/
def hardyBlaschkeEnergy (q : ℝ) : Option ℕ → ℝ
  | none => -(q ^ 2) / (1 - q ^ 2)
  | some j => (j : ℝ) + 1

theorem hardyKernel_mem_numberDomain (hq : ‖(q : ℂ)‖ < 1) :
    hardyKernel hq ∈ hardyNumber.domain := by
  change Memℓp (fun n : ℕ => ((n : ℝ) : ℂ) * hardyKernel hq n) 2
  simpa only [Complex.ofReal_natCast] using memlp_number_hardyKernel hq

theorem hardyBlaschkeMode_mem_numberDomain (hq : ‖(q : ℂ)‖ < 1) (i : Option ℕ) :
    hardyBlaschkeMode hq i ∈ (hardyNumberMinusKMS hq).domain := by
  cases i with
  | none =>
    exact hardyNumber.domain.smul_mem _ (hardyKernel_mem_numberDomain hq)
  | some j =>
    change Memℓp (fun n : ℕ => ((n : ℝ) : ℂ) *
      blaschkeMul hq (HilbertSchmidt.lpBasis ℕ j) n) 2
    simpa only [Complex.ofReal_natCast, HilbertSchmidt.lpBasis_apply] using
      memlp_number_blaschke_single hq j

/-- Every mode is an eigenvector of the actual maximal-domain operator. -/
theorem hardyNumberMinusKMS_mode (hq : ‖(q : ℂ)‖ < 1) (i : Option ℕ) :
    hardyNumberMinusKMS hq ⟨hardyBlaschkeMode hq i,
      hardyBlaschkeMode_mem_numberDomain hq i⟩ =
        (hardyBlaschkeEnergy q i : ℂ) • hardyBlaschkeMode hq i := by
  apply lp.ext
  funext n
  rw [hardyNumberMinusKMS_apply]
  cases i with
  | none =>
    change (n : ℂ) * hardyBlaschkeGround hq n -
      hardyGeometricKMS hq (hardyBlaschkeGround hq) n + hardyBlaschkeGround hq n =
        ((-(q ^ 2) / (1 - q ^ 2) : ℝ) : ℂ) * hardyBlaschkeGround hq n
    rw [hardyBlaschkeGround, map_smul]
    change (n : ℂ) * ((‖hardyKernel hq‖ : ℂ)⁻¹ * hardyKernel hq n) -
      (‖hardyKernel hq‖ : ℂ)⁻¹ * hardyGeometricKMS hq (hardyKernel hq) n +
      (‖hardyKernel hq‖ : ℂ)⁻¹ * hardyKernel hq n =
        ((-(q ^ 2) / (1 - q ^ 2) : ℝ) : ℂ) *
          ((‖hardyKernel hq‖ : ℂ)⁻¹ * hardyKernel hq n)
    rw [hardyGeometricKMS_kernel_apply]
    change (n : ℂ) * ((‖hardyKernel hq‖ : ℂ)⁻¹ * (starRingEnd ℂ (q : ℂ)) ^ n) -
      (‖hardyKernel hq‖ : ℂ)⁻¹ *
        (((n : ℂ) + (1 - (q : ℂ) ^ 2)⁻¹) * (q : ℂ) ^ n) +
      (‖hardyKernel hq‖ : ℂ)⁻¹ * (starRingEnd ℂ (q : ℂ)) ^ n =
        ((-(q ^ 2) / (1 - q ^ 2) : ℝ) : ℂ) *
          ((‖hardyKernel hq‖ : ℂ)⁻¹ * (starRingEnd ℂ (q : ℂ)) ^ n)
    rw [Complex.conj_ofReal]
    push_cast
    field_simp [hardyRealBlaschkeDen_ne_zero hq]
    ring
  | some j =>
    change (n : ℂ) * blaschkeMul hq (HilbertSchmidt.lpBasis ℕ j) n -
      hardyGeometricKMS hq (blaschkeMul hq (HilbertSchmidt.lpBasis ℕ j)) n +
      blaschkeMul hq (HilbertSchmidt.lpBasis ℕ j) n =
        (((j : ℝ) + 1 : ℝ) : ℂ) * blaschkeMul hq (HilbertSchmidt.lpBasis ℕ j) n
    rw [HilbertSchmidt.lpBasis_apply, hardyGeometricKMS_blaschke_single_apply]
    push_cast
    ring

theorem hardyBlaschkeBasis_mem_numberDomain (hq : ‖(q : ℂ)‖ < 1) (i : Option ℕ) :
    hardyBlaschkeBasis hq i ∈ (hardyNumberMinusKMS hq).domain := by
  rw [hardyBlaschkeBasis_apply]
  exact hardyBlaschkeMode_mem_numberDomain hq i

theorem hardyNumberMinusKMS_basis (hq : ‖(q : ℂ)‖ < 1) (i : Option ℕ) :
    hardyNumberMinusKMS hq ⟨hardyBlaschkeBasis hq i,
      hardyBlaschkeBasis_mem_numberDomain hq i⟩ =
        (hardyBlaschkeEnergy q i : ℂ) • hardyBlaschkeBasis hq i := by
  simpa only [hardyBlaschkeBasis_apply] using hardyNumberMinusKMS_mode hq i

/-- The complete spectral coordinates characterize the actual number domain. -/
theorem hardyNumberMinusKMS_domain_iff (hq : ‖(q : ℂ)‖ < 1) (x : HardyDisk) :
    x ∈ (hardyNumberMinusKMS hq).domain ↔
      Memℓp (fun i => (hardyBlaschkeEnergy q i : ℂ) *
        (hardyBlaschkeBasis hq).repr x i) 2 :=
  closed_eigenbasis_domain_iff _ _ _ (hardyNumberMinusKMS_isClosed hq)
    (hardyNumberMinusKMS_formalSelfAdjoint hq) (hardyBlaschkeBasis_mem_numberDomain hq)
    (hardyNumberMinusKMS_basis hq) x

/-- Self-adjointness holds on the full number domain. -/
theorem hardyNumberMinusKMS_isSelfAdjoint (hq : ‖(q : ℂ)‖ < 1) :
    IsSelfAdjoint (hardyNumberMinusKMS hq) :=
  closed_eigenbasis_isSelfAdjoint _ _ _ (hardyNumberMinusKMS_isClosed hq)
    (hardyNumberMinusKMS_formalSelfAdjoint hq) (hardyBlaschkeBasis_mem_numberDomain hq)
    (hardyNumberMinusKMS_basis hq)

end GaloisForLFunctions.HTGeometry
