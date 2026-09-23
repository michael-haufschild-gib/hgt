import GaloisForLFunctions.HTGeometry.FiniteBlaschkeGeneralizedSchurInertia

open Complex
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Hardy multiplication by a finite Blaschke product. -/
def finiteBlaschkeMul (B : FiniteBlaschke) : HardyDisk →L[ℂ] HardyDisk :=
  hardyMul B.toMultiplier

theorem norm_finiteBlaschkeMul (B : FiniteBlaschke) (x : HardyDisk) :
    ‖finiteBlaschkeMul B x‖ = ‖x‖ :=
  norm_hardyMul_blaschke B x

/-- Adjoint is a left inverse to an isometric finite-Blaschke multiplier. -/
theorem adjoint_finiteBlaschkeMul_comp (B : FiniteBlaschke) (x : HardyDisk) :
    ContinuousLinearMap.adjoint (finiteBlaschkeMul B) (finiteBlaschkeMul B x) = x := by
  refine ext_inner_right ℂ fun y => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact inner_map_map_of_isometry (fun u => norm_finiteBlaschkeMul B u) x y

/-- Orthogonal complement of finite-Blaschke model space is exactly multiplier range. -/
theorem finiteBlaschkeModelSpace_orthogonal_eq_range (B : FiniteBlaschke) :
    Submodule.orthogonal (finiteBlaschkeModelSpace B) =
      LinearMap.range ((finiteBlaschkeMul B : HardyDisk →L[ℂ] HardyDisk) :
        HardyDisk →ₗ[ℂ] HardyDisk) := by
  let R : Submodule ℂ HardyDisk :=
    LinearMap.range ((finiteBlaschkeMul B : HardyDisk →L[ℂ] HardyDisk) :
      HardyDisk →ₗ[ℂ] HardyDisk)
  have hclosed : IsClosed (R : Set HardyDisk) :=
    isClosed_coe_range_of_isometry (fun x => norm_finiteBlaschkeMul B x)
  haveI : CompleteSpace R := hclosed.completeSpace_coe
  change Submodule.orthogonal (Submodule.orthogonal R) = R
  rw [Submodule.orthogonal_orthogonal]

/-- Exact adjoint-energy loss of arbitrary finite-Blaschke multiplier. -/
theorem norm_sq_adjoint_finiteBlaschkeMul (B : FiniteBlaschke) (g : HardyDisk) :
    ‖ContinuousLinearMap.adjoint (finiteBlaschkeMul B) g‖ ^ (2 : ℕ) =
      ‖g‖ ^ (2 : ℕ) - ‖(finiteBlaschkeModelSpace B).starProjection g‖ ^ (2 : ℕ) := by
  classical
  set u : HardyDisk := (finiteBlaschkeModelSpace B).starProjection g with hu
  set v : HardyDisk := g - u with hv
  have hvmem : v ∈ Submodule.orthogonal (finiteBlaschkeModelSpace B) := by
    rw [hv, hu]
    exact (finiteBlaschkeModelSpace B).sub_starProjection_mem_orthogonal g
  obtain ⟨h, hh⟩ : ∃ h : HardyDisk, finiteBlaschkeMul B h = v := by
    have hrange : v ∈ LinearMap.range
        ((finiteBlaschkeMul B : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk) := by
      rw [← finiteBlaschkeModelSpace_orthogonal_eq_range B]
      exact hvmem
    simpa using hrange
  have humem : u ∈ finiteBlaschkeModelSpace B := by
    rw [hu]
    exact (finiteBlaschkeModelSpace B).starProjection_apply_mem g
  have hadjU : ContinuousLinearMap.adjoint (finiteBlaschkeMul B) u = 0 := by
    refine ext_inner_right ℂ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left]
    have hy : finiteBlaschkeMul B y ∈
        Submodule.orthogonal (finiteBlaschkeModelSpace B) := by
      rw [finiteBlaschkeModelSpace_orthogonal_eq_range B]
      exact ⟨y, rfl⟩
    exact ((finiteBlaschkeModelSpace B).mem_orthogonal _).1 hy u humem
  have hsplit : g = u + v := by rw [hv]; abel
  have hadj : ContinuousLinearMap.adjoint (finiteBlaschkeMul B) g = h := by
    rw [hsplit, map_add, hadjU, zero_add, ← hh, adjoint_finiteBlaschkeMul_comp]
  have hperp : (inner ℂ u v : ℂ) = 0 :=
    ((finiteBlaschkeModelSpace B).mem_orthogonal _).1 hvmem u humem
  have hpyth : ‖g‖ ^ (2 : ℕ) = ‖u‖ ^ (2 : ℕ) + ‖v‖ ^ (2 : ℕ) := by
    rw [hsplit]
    simpa [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u v hperp
  have hnh : ‖h‖ = ‖v‖ := by rw [← hh, norm_finiteBlaschkeMul]
  rw [hadj, hnh, hpyth, hu]
  ring

/-- Projected contraction form is difference of denominator and numerator adjoint energies. -/
theorem finiteBlaschkeGeneralizedSchurForm_eq_adjoint_energy_difference
    (F : DiskMultiplier) (B : FiniteBlaschke) (x : HardyDisk) :
    finiteBlaschkeGeneralizedSchurForm F B x =
      ‖ContinuousLinearMap.adjoint (finiteBlaschkeMul B) x‖ ^ (2 : ℕ) -
        ‖ContinuousLinearMap.adjoint (hardyMul F) x‖ ^ (2 : ℕ) := by
  rw [finiteBlaschkeGeneralizedSchurForm, projectedAdjointDefectForm,
    norm_sq_adjoint_finiteBlaschkeMul]
  ring

/-- Hardy coprimality: every `H²` vector is sum of numerator and denominator multiples. -/
def HardyCoprimeWithFiniteBlaschke (F : DiskMultiplier) (B : FiniteBlaschke) : Prop :=
  ∀ z : HardyDisk, ∃ a b : HardyDisk,
    hardyMul F a + finiteBlaschkeMul B b = z

/-- Hardy coprimality makes numerator adjoint faithful on denominator model space. -/
theorem adjoint_hardyMul_domRestrict_finiteBlaschkeModelSpace_injective_of_coprime
    (F : DiskMultiplier) (B : FiniteBlaschke)
    (hcop : HardyCoprimeWithFiniteBlaschke F B) :
    Function.Injective
      ((ContinuousLinearMap.adjoint (hardyMul F)).toLinearMap.domRestrict
        (finiteBlaschkeModelSpace B)) := by
  intro x y hxy
  let d : HardyDisk := (x : HardyDisk) - (y : HardyDisk)
  have hdK : d ∈ finiteBlaschkeModelSpace B := sub_mem x.property y.property
  have hFzero : ContinuousLinearMap.adjoint (hardyMul F) d = 0 := by
    change ContinuousLinearMap.adjoint (hardyMul F) ((x : HardyDisk) - (y : HardyDisk)) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hxy
  have hd0 : d = 0 := by
    refine ext_inner_right ℂ fun z => ?_
    obtain ⟨a0, b0, hab⟩ := hcop z
    have hFa : (inner ℂ d (hardyMul F a0) : ℂ) = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_left, hFzero, inner_zero_left]
    have hBb : (inner ℂ d (finiteBlaschkeMul B b0) : ℂ) = 0 := by
      rw [← inner_conj_symm]
      have hBmem : finiteBlaschkeMul B b0 ∈
          LinearMap.range ((finiteBlaschkeMul B : HardyDisk →L[ℂ] HardyDisk) :
            HardyDisk →ₗ[ℂ] HardyDisk) := ⟨b0, rfl⟩
      have hdK' : d ∈ Submodule.orthogonal
          (LinearMap.range ((finiteBlaschkeMul B : HardyDisk →L[ℂ] HardyDisk) :
            HardyDisk →ₗ[ℂ] HardyDisk)) := hdK
      have horth := ((LinearMap.range
        ((finiteBlaschkeMul B : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk)).mem_orthogonal _).1 hdK'
            (finiteBlaschkeMul B b0) hBmem
      rw [horth, map_zero]
    rw [inner_zero_left, ← hab, inner_add_right, hFa, hBb, add_zero]
  apply Subtype.ext
  exact sub_eq_zero.mp hd0

/-- Coprime finite generalized-Schur factors have exact denominator degree as negative index. -/
theorem finiteBlaschkeGeneralizedSchurForm_hasExactNegativeIndex_of_coprime
    (F : DiskMultiplier) (B : FiniteBlaschke) (hF : F.bd ≤ 1)
    (hcop : HardyCoprimeWithFiniteBlaschke F B) :
    HasExactNegativeIndex (finiteBlaschkeGeneralizedSchurForm F B) B.deg :=
  finiteBlaschkeGeneralizedSchurForm_hasExactNegativeIndex F B hF
    (adjoint_hardyMul_domRestrict_finiteBlaschkeModelSpace_injective_of_coprime F B hcop)

end GaloisForLFunctions.HTGeometry
