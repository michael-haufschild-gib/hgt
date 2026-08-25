import GaloisForLFunctions.HTGeometry.HardyBoundaryScalingRankOne
import GaloisForLFunctions.HTGeometry.HardyMultiplierCrossingChannelPeeling
import GaloisForLFunctions.HTGeometry.FiniteBlaschkeProduct
import GaloisForLFunctions.HTGeometry.CommutingProjectionIntersectionEnergy

open Complex Filter Topology
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem finiteBlaschkeModelSpace_singleBlaschke_eq_modelSpace
    {q : ℂ} (hq : ‖q‖ < 1) :
    finiteBlaschkeModelSpace (singleBlaschke hq) = modelSpace hq := by
  rw [finiteBlaschkeModelSpace, range_hardyMul_singleBlaschke hq,
    Submodule.orthogonal_orthogonal]
  rfl

theorem finiteModelResidualCore_singleBlaschke_eq
    (F : DiskMultiplier) {q : ℂ} (hq : ‖q‖ < 1) (c : ℂ) :
    finiteModelResidualCore F (singleBlaschke hq) c =
      singleModelResidualCore F hq c := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [finiteModelResidualCore, singleModelResidualCore,
    ContinuousLinearMap.comp_apply]
  rw [starProjection_congr
    (finiteBlaschkeModelSpace_singleBlaschke_eq_modelSpace hq) x]

theorem norm_finiteModelResidualCore_append_le
    (F : DiskMultiplier) (B₀ B₁ : FiniteBlaschke) (c : ℂ) :
    ‖finiteModelResidualCore F (FiniteBlaschke.append B₀ B₁) c‖ ≤
      ‖finiteModelResidualCore F B₀ c‖ + ‖finiteModelResidualCore F B₁ c‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  let y := (finiteBlaschkeModelSpace (FiniteBlaschke.append B₀ B₁)).starProjection x
  have hy : y ∈ finiteBlaschkeModelSpace (FiniteBlaschke.append B₀ B₁) :=
    (finiteBlaschkeModelSpace (FiniteBlaschke.append B₀ B₁)).starProjection_apply_mem x
  have hysup : y ∈ finiteBlaschkeModelSpace B₀ ⊔
      (finiteBlaschkeModelSpace B₁).map
        ((finiteBlaschkeMul B₀ : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk) := by
    rw [← FiniteBlaschke.finiteBlaschkeModelSpace_append_eq_sup B₀ B₁]
    exact hy
  rcases Submodule.mem_sup.mp hysup with ⟨u, hu, z, hz, huz⟩
  rcases hz with ⟨v, hv, rfl⟩
  have horth : inner ℂ u (finiteBlaschkeMul B₀ v) = 0 :=
    finiteBlaschkeModelSpace_inner_transported_eq_zero B₀ B₁ ⟨u, hu⟩ ⟨v, hv⟩
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    u (finiteBlaschkeMul B₀ v) horth
  change u + finiteBlaschkeMul B₀ v = y at huz
  have hu_norm : ‖u‖ ≤ ‖y‖ := by
    rw [huz] at hpyth
    nlinarith [norm_nonneg u, norm_nonneg y, norm_nonneg (finiteBlaschkeMul B₀ v)]
  have hv_norm : ‖v‖ ≤ ‖y‖ := by
    have hiso : ‖finiteBlaschkeMul B₀ v‖ = ‖v‖ :=
      hardyMulBlaschke_isometry B₀ v
    rw [huz, hiso] at hpyth
    nlinarith [norm_nonneg u, norm_nonneg y, norm_nonneg v]
  have hy_norm : ‖y‖ ≤ ‖x‖ := by
    calc
      ‖y‖ ≤ ‖(finiteBlaschkeModelSpace (FiniteBlaschke.append B₀ B₁)).starProjection‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right
        (finiteBlaschkeModelSpace (FiniteBlaschke.append B₀ B₁)).starProjection_norm_le
        (norm_nonneg _)
      _ = ‖x‖ := one_mul _
  have hcomm :
      (hardyMul F - c • ContinuousLinearMap.id ℂ HardyDisk)
          (finiteBlaschkeMul B₀ v) =
        finiteBlaschkeMul B₀
          ((hardyMul F - c • ContinuousLinearMap.id ℂ HardyDisk) v) := by
    simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply, map_sub, map_smul]
    change hardyMul F (hardyMul B₀.toMultiplier v) -
        c • hardyMul B₀.toMultiplier v =
      hardyMul B₀.toMultiplier (hardyMul F v) -
        c • hardyMul B₀.toMultiplier v
    rw [hardyMul_comm F B₀.toMultiplier v]
  have hu_proj : (finiteBlaschkeModelSpace B₀).starProjection u = u :=
    (finiteBlaschkeModelSpace B₀).starProjection_eq_self_iff.mpr hu
  have hv_proj : (finiteBlaschkeModelSpace B₁).starProjection v = v :=
    (finiteBlaschkeModelSpace B₁).starProjection_eq_self_iff.mpr hv
  rw [finiteModelResidualCore, ContinuousLinearMap.comp_apply]
  change ‖(hardyMul F - c • ContinuousLinearMap.id ℂ HardyDisk) y‖ ≤ _
  rw [← huz, map_add, hcomm]
  calc
    ‖(hardyMul F - c • ContinuousLinearMap.id ℂ HardyDisk) u +
        finiteBlaschkeMul B₀
          ((hardyMul F - c • ContinuousLinearMap.id ℂ HardyDisk) v)‖ ≤
        ‖(hardyMul F - c • ContinuousLinearMap.id ℂ HardyDisk) u‖ +
          ‖finiteBlaschkeMul B₀
            ((hardyMul F - c • ContinuousLinearMap.id ℂ HardyDisk) v)‖ :=
      norm_add_le _ _
    _ = ‖finiteModelResidualCore F B₀ c u‖ +
        ‖finiteModelResidualCore F B₁ c v‖ := by
      have hiso : ‖finiteBlaschkeMul B₀
          ((hardyMul F - c • ContinuousLinearMap.id ℂ HardyDisk) v)‖ =
          ‖(hardyMul F - c • ContinuousLinearMap.id ℂ HardyDisk) v‖ :=
        hardyMulBlaschke_isometry B₀ _
      rw [hiso]
      simp only [finiteModelResidualCore, ContinuousLinearMap.comp_apply, hu_proj, hv_proj]
    _ ≤ ‖finiteModelResidualCore F B₀ c‖ * ‖u‖ +
        ‖finiteModelResidualCore F B₁ c‖ * ‖v‖ :=
      add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ ‖finiteModelResidualCore F B₀ c‖ * ‖y‖ +
        ‖finiteModelResidualCore F B₁ c‖ * ‖y‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_left hu_norm (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hv_norm (norm_nonneg _))
    _ = (‖finiteModelResidualCore F B₀ c‖ +
        ‖finiteModelResidualCore F B₁ c‖) * ‖y‖ := by ring
    _ ≤ (‖finiteModelResidualCore F B₀ c‖ +
        ‖finiteModelResidualCore F B₁ c‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_left hy_norm (add_nonneg (norm_nonneg _) (norm_nonneg _))

namespace FiniteBlaschke

/-- One zero repeated with exact positive multiplicity `m + 1`. -/
def repeatSingle {q : ℂ} (hq : ‖q‖ < 1) : ℕ → FiniteBlaschke
  | 0 => singleBlaschke hq
  | m + 1 => append (singleBlaschke hq) (repeatSingle hq m)

@[simp] theorem deg_repeatSingle {q : ℂ} (hq : ‖q‖ < 1) (m : ℕ) :
    (repeatSingle hq m).deg = m + 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change (append (singleBlaschke hq) (repeatSingle hq m)).deg = m.succ + 1
      rw [deg_append, ih]
      change 1 + (m + 1) = m.succ + 1
      omega

end FiniteBlaschke

theorem norm_finiteModelResidualCore_repeatSingle_le
    (F : DiskMultiplier) {q : ℂ} (hq : ‖q‖ < 1) (c : ℂ) (m : ℕ) :
    ‖finiteModelResidualCore F (FiniteBlaschke.repeatSingle hq m) c‖ ≤
      ((m : ℝ) + 1) * ‖singleModelResidualCore F hq c‖ := by
  induction m with
  | zero =>
      simp only [FiniteBlaschke.repeatSingle]
      rw [finiteModelResidualCore_singleBlaschke_eq]
      norm_num
  | succ m ih =>
      rw [FiniteBlaschke.repeatSingle]
      have happ := norm_finiteModelResidualCore_append_le F
        (singleBlaschke hq) (FiniteBlaschke.repeatSingle hq m) c
      rw [finiteModelResidualCore_singleBlaschke_eq] at happ
      norm_num [Nat.cast_succ]
      nlinarith [norm_nonneg (singleModelResidualCore F hq c)]

theorem tendsto_norm_finiteModelResidualCore_repeatSingle_zero
    {ι : Type*} {l : Filter ι} (F : ι → DiskMultiplier)
    (hF : ∀ i, HardyMultiplierIsometry (F i))
    (q : ι → ℂ) (hq : ∀ i, ‖q i‖ < 1) (c : ι → ℂ)
    (hc : ∀ i, ‖c i‖ = 1) (m : ℕ)
    (hvalue : Tendsto (fun i => ‖(F i).fn (q i) - c i‖) l (𝓝 0)) :
    Tendsto (fun i =>
      ‖finiteModelResidualCore (F i) (FiniteBlaschke.repeatSingle (hq i) m) (c i)‖)
      l (𝓝 0) := by
  have hsingle := tendsto_norm_singleModelResidualCore_zero F hF q hq c hc hvalue
  have hbound : Tendsto (fun i =>
      (((m : ℝ) + 1) * ‖singleModelResidualCore (F i) (hq i) (c i)‖))
      l (𝓝 0) := by
    convert tendsto_const_nhds.mul hsingle using 1 <;> norm_num
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun i => norm_finiteModelResidualCore_repeatSingle_le
      (F i) (hq i) (c i) m)
    hbound

end

end GaloisForLFunctions.HTGeometry
