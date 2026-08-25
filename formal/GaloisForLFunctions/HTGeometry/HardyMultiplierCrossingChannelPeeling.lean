import GaloisForLFunctions.HTGeometry.HardyMultiplierLeakagePythagoras
import GaloisForLFunctions.HTGeometry.FiniteBlaschkeGeneralizedSchurInertia
import GaloisForLFunctions.HTGeometry.AdjointGramChannelPeeling

open Filter Topology
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Crossing channel `B₀ K_D` for an arbitrary persistent inner factor and a finite disappearing
Blaschke factor. -/
def hardyMultiplierFiniteCrossingChannel (B₀ : DiskMultiplier) (D : FiniteBlaschke) :
    Submodule ℂ HardyDisk :=
  (finiteBlaschkeModelSpace D).map
    ((hardyMul B₀ : HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk)

noncomputable instance (B₀ : DiskMultiplier) (D : FiniteBlaschke) :
    FiniteDimensional ℂ (hardyMultiplierFiniteCrossingChannel B₀ D) := by
  unfold hardyMultiplierFiniteCrossingChannel
  infer_instance

noncomputable instance (B₀ : DiskMultiplier) (D : FiniteBlaschke) :
    (hardyMultiplierFiniteCrossingChannel B₀ D).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- Crossing-channel dimension is exactly the disappearing divisor multiplicity, independently of
the possibly infinite persistent inner factor. -/
theorem finrank_hardyMultiplierFiniteCrossingChannel
    (B₀ : DiskMultiplier) (D : FiniteBlaschke)
    (hB₀ : HardyMultiplierIsometry B₀) :
    Module.finrank ℂ (hardyMultiplierFiniteCrossingChannel B₀ D) = D.deg := by
  have hinj : Function.Injective
      ((hardyMul B₀ : HardyDisk →L[ℂ] HardyDisk) :
        HardyDisk →ₗ[ℂ] HardyDisk) := by
    intro x y hxy
    have hzero : hardyMul B₀ (x - y) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    have hnorm : ‖x - y‖ = 0 := by
      rw [← hB₀ (x - y), hzero, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  let e := Submodule.equivMapOfInjective
    ((hardyMul B₀ : HardyDisk →L[ℂ] HardyDisk) :
      HardyDisk →ₗ[ℂ] HardyDisk) hinj (finiteBlaschkeModelSpace D)
  calc
    Module.finrank ℂ (hardyMultiplierFiniteCrossingChannel B₀ D) =
        Module.finrank ℂ (finiteBlaschkeModelSpace D) := by
      exact (LinearEquiv.finrank_eq e).symm
    _ = D.deg := finrank_finiteBlaschkeModelSpace D

/-- Exact theorem-C product decomposition with arbitrary persistent degree:
`K_(B₀D) = K_(B₀) ⊕ B₀ K_D`. -/
theorem hardyMultiplierModelSpace_mul_finite_eq_sup
    (B₀ : DiskMultiplier) (D : FiniteBlaschke)
    (hB₀ : HardyMultiplierIsometry B₀) :
    hardyMultiplierModelSpace (B₀.mul D.toMultiplier) =
      hardyMultiplierModelSpace B₀ ⊔
        hardyMultiplierFiniteCrossingChannel B₀ D := by
  simpa [hardyMultiplierFiniteCrossingChannel, finiteBlaschkeModelSpace,
    hardyMultiplierModelSpace] using
    hardyMultiplierModelSpace_mul_eq_sup B₀ D.toMultiplier hB₀

/-- Persistent inner multiplication cancels exactly from the causal compression on its transported
crossing channel. -/
theorem hardyMultiplierCausalCore_cancel_persistent
    (F B₀ D : DiskMultiplier) (hB₀ : HardyMultiplierIsometry B₀)
    (y : HardyDisk) :
    hardyMultiplierCausalCore F (B₀.mul D) (hardyMul B₀ y) =
      hardyMultiplierCausalCore F D y := by
  refine ext_inner_right ℂ fun x => ?_
  rw [hardyMultiplierCausalCore, hardyMultiplierCausalCore,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]
  rw [hardyMul_comm F B₀ y, ← hardyMul_mul B₀ D x]
  exact inner_map_map_of_isometry hB₀ (hardyMul F y) (hardyMul D x)

/-- Residual numerator after subtracting its local unimodular constant, compressed to the finite
crossing model space.  This is the operator controlled by boundary scaling. -/
def finiteModelResidualCore (F : DiskMultiplier) (D : FiniteBlaschke) (c : ℂ) :
    HardyDisk →L[ℂ] HardyDisk :=
  (hardyMul F - c • ContinuousLinearMap.id ℂ HardyDisk).comp
    (finiteBlaschkeModelSpace D).starProjection

private theorem adjoint_finiteBlaschkeMul_eq_zero_of_mem_modelSpace
    (D : FiniteBlaschke) (y : HardyDisk) (hy : y ∈ finiteBlaschkeModelSpace D) :
    (finiteBlaschkeMul D).adjoint y = 0 := by
  refine ext_inner_right ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left]
  change inner ℂ y (hardyMul D.toMultiplier x) = 0
  have horth : inner ℂ (hardyMul D.toMultiplier x) y = 0 :=
    hy _ ⟨x, rfl⟩
  rw [← inner_conj_symm, horth, map_zero]

/-- On `K_D`, the causal compression depends only on the residual after any scalar constant is
removed; the scalar channel is annihilated exactly. -/
theorem hardyMultiplierCausalCore_eq_finiteModelResidualCore
    (F : DiskMultiplier) (D : FiniteBlaschke) (c : ℂ)
    (y : HardyDisk) (hy : y ∈ finiteBlaschkeModelSpace D) :
    hardyMultiplierCausalCore F D.toMultiplier y =
      (finiteBlaschkeMul D).adjoint (finiteModelResidualCore F D c y) := by
  have hproj : (finiteBlaschkeModelSpace D).starProjection y = y :=
    (finiteBlaschkeModelSpace D).starProjection_eq_self_iff.mpr hy
  have hadj : (finiteBlaschkeMul D).adjoint y = 0 :=
    adjoint_finiteBlaschkeMul_eq_zero_of_mem_modelSpace D y hy
  rw [hardyMultiplierCausalCore, ContinuousLinearMap.comp_apply,
    finiteModelResidualCore, ContinuousLinearMap.comp_apply, hproj, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply]
  change (finiteBlaschkeMul D).adjoint (hardyMul F y) =
    (finiteBlaschkeMul D).adjoint (hardyMul F y - c • y)
  rw [map_sub, map_smul, hadj, smul_zero, sub_zero]

/-- Exact local boundary-scaling estimate: crossing-channel causal norm is bounded by the residual
multiplier compressed to the untransported finite model space. -/
theorem norm_hardyMultiplierCausalCore_comp_crossing_le_residual
    (F B₀ : DiskMultiplier) (D : FiniteBlaschke) (c : ℂ)
    (hB₀ : HardyMultiplierIsometry B₀) :
    ‖(hardyMultiplierCausalCore F (B₀.mul D.toMultiplier)).comp
        (hardyMultiplierFiniteCrossingChannel B₀ D).starProjection‖ ≤
      ‖finiteModelResidualCore F D c‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [ContinuousLinearMap.comp_apply]
  have hxC :=
    (hardyMultiplierFiniteCrossingChannel B₀ D).starProjection_apply_mem x
  rcases hxC with ⟨y, hy, hyEq⟩
  calc
    ‖hardyMultiplierCausalCore F (B₀.mul D.toMultiplier)
        ((hardyMultiplierFiniteCrossingChannel B₀ D).starProjection x)‖ =
        ‖hardyMultiplierCausalCore F D.toMultiplier y‖ := by
      rw [← hyEq]
      exact congrArg norm
        (hardyMultiplierCausalCore_cancel_persistent F B₀ D.toMultiplier hB₀ y)
    _ = ‖(finiteBlaschkeMul D).adjoint (finiteModelResidualCore F D c y)‖ := by
      rw [hardyMultiplierCausalCore_eq_finiteModelResidualCore F D c y hy]
    _ ≤ ‖finiteModelResidualCore F D c y‖ :=
      norm_adjoint_hardyMul_le_of_isometry D.toMultiplier
        (hardyMulBlaschke_isometry D) _
    _ ≤ ‖finiteModelResidualCore F D c‖ * ‖y‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖finiteModelResidualCore F D c‖ * ‖hardyMul B₀ y‖ := by rw [hB₀]
    _ = ‖finiteModelResidualCore F D c‖ *
        ‖(hardyMultiplierFiniteCrossingChannel B₀ D).starProjection x‖ := by
      simpa using congrArg
        (fun z : HardyDisk => ‖finiteModelResidualCore F D c‖ * ‖z‖) hyEq
    _ ≤ ‖finiteModelResidualCore F D c‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_left
        (by
          calc
            ‖(hardyMultiplierFiniteCrossingChannel B₀ D).starProjection x‖ ≤
                ‖(hardyMultiplierFiniteCrossingChannel B₀ D).starProjection‖ * ‖x‖ :=
              ContinuousLinearMap.le_opNorm _ _
            _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right
              (hardyMultiplierFiniteCrossingChannel B₀ D).starProjection_norm_le
              (norm_nonneg x)
            _ = ‖x‖ := one_mul _)
        (norm_nonneg _)

/-- Exact theorem-C `(11)` identity with an arbitrary persistent inner factor. -/
theorem norm_hardyMultiplierCrossingGramDefect_eq_sq
    (F B₀ : DiskMultiplier) (D : FiniteBlaschke)
    (hF : HardyMultiplierIsometry F) (hB₀ : HardyMultiplierIsometry B₀) :
    ‖channelGramDefect (hardyMultiplierFiniteCrossingChannel B₀ D)
        (hardyMultiplierLeakageCore F (B₀.mul D.toMultiplier))‖ =
      ‖(hardyMultiplierCausalCore F (B₀.mul D.toMultiplier)).comp
          (hardyMultiplierFiniteCrossingChannel B₀ D).starProjection‖ *
        ‖(hardyMultiplierCausalCore F (B₀.mul D.toMultiplier)).comp
          (hardyMultiplierFiniteCrossingChannel B₀ D).starProjection‖ := by
  exact norm_channelGramDefect_eq_sq _ _ _
    (adjoint_comp_hardyMultiplierLeakageCore_add_causalCore F
      (B₀.mul D.toMultiplier) hF (hB₀.mul (hardyMulBlaschke_isometry D)))

/-- Exact theorem-C `(12)` estimate with an arbitrary persistent inner factor. -/
theorem norm_hardyMultiplierCrossingOffDiagonalGram_le
    (F B₀ : DiskMultiplier) (D : FiniteBlaschke)
    (hF : HardyMultiplierIsometry F) (hB₀ : HardyMultiplierIsometry B₀) :
    ‖channelOffDiagonalGram (hardyMultiplierFiniteCrossingChannel B₀ D)
        (hardyMultiplierLeakageCore F (B₀.mul D.toMultiplier))‖ ≤
      ‖(hardyMultiplierCausalCore F (B₀.mul D.toMultiplier)).comp
        (hardyMultiplierFiniteCrossingChannel B₀ D).starProjection‖ := by
  exact norm_channelOffDiagonalGram_le _ _ _
    (adjoint_comp_hardyMultiplierLeakageCore_add_causalCore F
      (B₀.mul D.toMultiplier) hF (hB₀.mul (hardyMulBlaschke_isometry D)))
    (norm_hardyMultiplierCausalCore_le_one F (B₀.mul D.toMultiplier) hF
      (hB₀.mul (hardyMulBlaschke_isometry D)))

/-- Local residual convergence implies uniform disappearance of the causal compression on the
crossing channel. -/
theorem tendsto_norm_hardyMultiplierCausalCore_crossing_zero
    {ι : Type*} {l : Filter ι} (F B₀ : ι → DiskMultiplier)
    (D : ι → FiniteBlaschke) (c : ι → ℂ)
    (hB₀ : ∀ i, HardyMultiplierIsometry (B₀ i))
    (hresidual : Tendsto
      (fun i => ‖finiteModelResidualCore (F i) (D i) (c i)‖) l (𝓝 0)) :
    Tendsto (fun i =>
      ‖(hardyMultiplierCausalCore (F i) ((B₀ i).mul (D i).toMultiplier)).comp
        (hardyMultiplierFiniteCrossingChannel (B₀ i) (D i)).starProjection‖)
      l (𝓝 0) := by
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun i => norm_hardyMultiplierCausalCore_comp_crossing_le_residual
      (F i) (B₀ i) (D i) (c i) (hB₀ i)) hresidual

/-- Boundary-scaled residual convergence proves theorem-C `(11)`. -/
theorem tendsto_norm_hardyMultiplierCrossingGramDefect_zero
    {ι : Type*} {l : Filter ι} (F B₀ : ι → DiskMultiplier)
    (D : ι → FiniteBlaschke) (c : ι → ℂ)
    (hF : ∀ i, HardyMultiplierIsometry (F i))
    (hB₀ : ∀ i, HardyMultiplierIsometry (B₀ i))
    (hresidual : Tendsto
      (fun i => ‖finiteModelResidualCore (F i) (D i) (c i)‖) l (𝓝 0)) :
    Tendsto (fun i =>
      ‖channelGramDefect (hardyMultiplierFiniteCrossingChannel (B₀ i) (D i))
        (hardyMultiplierLeakageCore (F i)
          ((B₀ i).mul (D i).toMultiplier))‖) l (𝓝 0) := by
  have hc := tendsto_norm_hardyMultiplierCausalCore_crossing_zero
    F B₀ D c hB₀ hresidual
  convert hc.mul hc using 1
  · funext i
    exact norm_hardyMultiplierCrossingGramDefect_eq_sq
      (F i) (B₀ i) (D i) (hF i) (hB₀ i)
  · simp

/-- Boundary-scaled residual convergence proves theorem-C `(12)`. -/
theorem tendsto_norm_hardyMultiplierCrossingOffDiagonalGram_zero
    {ι : Type*} {l : Filter ι} (F B₀ : ι → DiskMultiplier)
    (D : ι → FiniteBlaschke) (c : ι → ℂ)
    (hF : ∀ i, HardyMultiplierIsometry (F i))
    (hB₀ : ∀ i, HardyMultiplierIsometry (B₀ i))
    (hresidual : Tendsto
      (fun i => ‖finiteModelResidualCore (F i) (D i) (c i)‖) l (𝓝 0)) :
    Tendsto (fun i =>
      ‖channelOffDiagonalGram
        (hardyMultiplierFiniteCrossingChannel (B₀ i) (D i))
        (hardyMultiplierLeakageCore (F i)
          ((B₀ i).mul (D i).toMultiplier))‖) l (𝓝 0) := by
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun i => norm_hardyMultiplierCrossingOffDiagonalGram_le
      (F i) (B₀ i) (D i) (hF i) (hB₀ i))
    (tendsto_norm_hardyMultiplierCausalCore_crossing_zero
      F B₀ D c hB₀ hresidual)

end

end GaloisForLFunctions.HTGeometry
