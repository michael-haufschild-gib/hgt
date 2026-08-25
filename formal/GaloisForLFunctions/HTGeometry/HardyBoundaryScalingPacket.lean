import GaloisForLFunctions.HTGeometry.HardyBoundaryScalingFiniteMultiplicity

open Complex Filter Topology
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Causal compression restricted to one finite Blaschke model space. -/
def finiteModelCausalCore (F : DiskMultiplier) (D : FiniteBlaschke) :
    HardyDisk →L[ℂ] HardyDisk :=
  (hardyMultiplierCausalCore F D.toMultiplier).comp
    (finiteBlaschkeModelSpace D).starProjection

/-- On one finite model block, subtracting any scalar local phase controls the causal core. -/
theorem norm_finiteModelCausalCore_le_residual
    (F : DiskMultiplier) (D : FiniteBlaschke) (c : ℂ) :
    ‖finiteModelCausalCore F D‖ ≤ ‖finiteModelResidualCore F D c‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  let y := (finiteBlaschkeModelSpace D).starProjection x
  have hy : y ∈ finiteBlaschkeModelSpace D :=
    (finiteBlaschkeModelSpace D).starProjection_apply_mem x
  rw [finiteModelCausalCore, ContinuousLinearMap.comp_apply]
  calc
    ‖hardyMultiplierCausalCore F D.toMultiplier y‖ =
        ‖(finiteBlaschkeMul D).adjoint (finiteModelResidualCore F D c y)‖ := by
      rw [hardyMultiplierCausalCore_eq_finiteModelResidualCore F D c y hy]
    _ ≤ ‖finiteModelResidualCore F D c y‖ :=
      norm_adjoint_hardyMul_le_of_isometry D.toMultiplier
        (hardyMulBlaschke_isometry D) _
    _ ≤ ‖finiteModelResidualCore F D c‖ * ‖y‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖finiteModelResidualCore F D c‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_left
        (by
          calc
            ‖y‖ ≤ ‖(finiteBlaschkeModelSpace D).starProjection‖ * ‖x‖ :=
              ContinuousLinearMap.le_opNorm _ _
            _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right
              (finiteBlaschkeModelSpace D).starProjection_norm_le (norm_nonneg _)
            _ = ‖x‖ := one_mul _)
        (norm_nonneg _)

/-- Adjoint product law for the causal core of an appended finite denominator. -/
theorem hardyMultiplierCausalCore_append
    (F : DiskMultiplier) (B₀ B₁ : FiniteBlaschke) (x : HardyDisk) :
    hardyMultiplierCausalCore F (FiniteBlaschke.append B₀ B₁).toMultiplier x =
      (finiteBlaschkeMul B₁).adjoint
        (hardyMultiplierCausalCore F B₀.toMultiplier x) := by
  refine ext_inner_right ℂ fun y => ?_
  rw [hardyMultiplierCausalCore, hardyMultiplierCausalCore,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (hardyMul F x)
      (finiteBlaschkeMul (FiniteBlaschke.append B₀ B₁) y) = _
  rw [FiniteBlaschke.finiteBlaschkeMul_append]
  rfl

/-- The transported tail of an appended model space sees exactly the tail causal core. -/
theorem hardyMultiplierCausalCore_append_transported
    (F : DiskMultiplier) (B₀ B₁ : FiniteBlaschke) (v : HardyDisk) :
    hardyMultiplierCausalCore F (FiniteBlaschke.append B₀ B₁).toMultiplier
        (finiteBlaschkeMul B₀ v) =
      hardyMultiplierCausalCore F B₁.toMultiplier v := by
  refine ext_inner_right ℂ fun x => ?_
  rw [hardyMultiplierCausalCore, hardyMultiplierCausalCore,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (hardyMul F (finiteBlaschkeMul B₀ v))
      (finiteBlaschkeMul (FiniteBlaschke.append B₀ B₁) x) = _
  rw [FiniteBlaschke.finiteBlaschkeMul_append]
  change inner ℂ (hardyMul F (hardyMul B₀.toMultiplier v))
      (hardyMul B₀.toMultiplier (hardyMul B₁.toMultiplier x)) =
    inner ℂ (hardyMul F v) (hardyMul B₁.toMultiplier x)
  rw [hardyMul_comm F B₀.toMultiplier v]
  exact inner_map_map_of_isometry (hardyMulBlaschke_isometry B₀) _ _

/-- Appending two finite boundary blocks adds their causal-error bounds. -/
theorem norm_finiteModelCausalCore_append_le
    (F : DiskMultiplier) (B₀ B₁ : FiniteBlaschke) (c₀ : ℂ) :
    ‖finiteModelCausalCore F (FiniteBlaschke.append B₀ B₁)‖ ≤
      ‖finiteModelResidualCore F B₀ c₀‖ + ‖finiteModelCausalCore F B₁‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  let y :=
    (finiteBlaschkeModelSpace (FiniteBlaschke.append B₀ B₁)).starProjection x
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
  change u + finiteBlaschkeMul B₀ v = y at huz
  have horth : inner ℂ u (finiteBlaschkeMul B₀ v) = 0 :=
    finiteBlaschkeModelSpace_inner_transported_eq_zero B₀ B₁ ⟨u, hu⟩ ⟨v, hv⟩
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    u (finiteBlaschkeMul B₀ v) horth
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
      ‖y‖ ≤
          ‖(finiteBlaschkeModelSpace (FiniteBlaschke.append B₀ B₁)).starProjection‖ *
            ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right
        (finiteBlaschkeModelSpace
          (FiniteBlaschke.append B₀ B₁)).starProjection_norm_le (norm_nonneg _)
      _ = ‖x‖ := one_mul _
  have hu_causal :
      ‖hardyMultiplierCausalCore F (FiniteBlaschke.append B₀ B₁).toMultiplier u‖ ≤
        ‖finiteModelResidualCore F B₀ c₀‖ * ‖u‖ := by
    rw [hardyMultiplierCausalCore_append]
    calc
      ‖(finiteBlaschkeMul B₁).adjoint
          (hardyMultiplierCausalCore F B₀.toMultiplier u)‖ ≤
          ‖hardyMultiplierCausalCore F B₀.toMultiplier u‖ :=
        norm_adjoint_hardyMul_le_of_isometry B₁.toMultiplier
          (hardyMulBlaschke_isometry B₁) _
      _ = ‖(finiteBlaschkeMul B₀).adjoint
          (finiteModelResidualCore F B₀ c₀ u)‖ := by
        rw [hardyMultiplierCausalCore_eq_finiteModelResidualCore F B₀ c₀ u hu]
      _ ≤ ‖finiteModelResidualCore F B₀ c₀ u‖ :=
        norm_adjoint_hardyMul_le_of_isometry B₀.toMultiplier
          (hardyMulBlaschke_isometry B₀) _
      _ ≤ ‖finiteModelResidualCore F B₀ c₀‖ * ‖u‖ :=
        ContinuousLinearMap.le_opNorm _ _
  have hv_proj : (finiteBlaschkeModelSpace B₁).starProjection v = v :=
    (finiteBlaschkeModelSpace B₁).starProjection_eq_self_iff.mpr hv
  rw [finiteModelCausalCore, ContinuousLinearMap.comp_apply]
  change ‖hardyMultiplierCausalCore F
      (FiniteBlaschke.append B₀ B₁).toMultiplier y‖ ≤ _
  rw [← huz, map_add, hardyMultiplierCausalCore_append_transported]
  calc
    ‖hardyMultiplierCausalCore F (FiniteBlaschke.append B₀ B₁).toMultiplier u +
        hardyMultiplierCausalCore F B₁.toMultiplier v‖ ≤
        ‖hardyMultiplierCausalCore F
          (FiniteBlaschke.append B₀ B₁).toMultiplier u‖ +
          ‖hardyMultiplierCausalCore F B₁.toMultiplier v‖ := norm_add_le _ _
    _ ≤ ‖finiteModelResidualCore F B₀ c₀‖ * ‖u‖ +
        ‖finiteModelCausalCore F B₁‖ * ‖v‖ := by
      refine add_le_add hu_causal ?_
      have hv_bound := ContinuousLinearMap.le_opNorm (finiteModelCausalCore F B₁) v
      simpa [finiteModelCausalCore, hv_proj] using hv_bound
    _ ≤ ‖finiteModelResidualCore F B₀ c₀‖ * ‖y‖ +
        ‖finiteModelCausalCore F B₁‖ * ‖y‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_left hu_norm (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hv_norm (norm_nonneg _))
    _ = (‖finiteModelResidualCore F B₀ c₀‖ +
        ‖finiteModelCausalCore F B₁‖) * ‖y‖ := by ring
    _ ≤ (‖finiteModelResidualCore F B₀ c₀‖ +
        ‖finiteModelCausalCore F B₁‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_left hy_norm
        (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Fixed-shape nonempty packet of separated finite boundary blocks. Each block may carry its own
local phase; the packet shape is fixed while its divisors vary over the parameter filter. -/
inductive FiniteBoundaryScalingPacket (ι : Type*) where
  | terminal (D : ι → FiniteBlaschke) (c : ι → ℂ)
  | cons (D : ι → FiniteBlaschke) (c : ι → ℂ)
      (tail : FiniteBoundaryScalingPacket ι)

namespace FiniteBoundaryScalingPacket

def divisor {ι : Type*} : FiniteBoundaryScalingPacket ι → ι → FiniteBlaschke
  | terminal D _, i => D i
  | cons D _ tail, i => FiniteBlaschke.append (D i) (divisor tail i)

def residualBudget {ι : Type*} (F : ι → DiskMultiplier) :
    FiniteBoundaryScalingPacket ι → ι → ℝ
  | terminal D c, i => ‖finiteModelResidualCore (F i) (D i) (c i)‖
  | cons D c tail, i =>
      ‖finiteModelResidualCore (F i) (D i) (c i)‖ + residualBudget F tail i

/-- Every separated packet's causal compression is controlled by the sum of its independent local
phase residuals. -/
theorem norm_finiteModelCausalCore_divisor_le_residualBudget
    {ι : Type*} (F : ι → DiskMultiplier)
    (P : FiniteBoundaryScalingPacket ι) (i : ι) :
    ‖finiteModelCausalCore (F i) (divisor P i)‖ ≤ residualBudget F P i := by
  induction P with
  | terminal D c =>
      exact norm_finiteModelCausalCore_le_residual (F i) (D i) (c i)
  | cons D c tail ih =>
      exact le_trans
        (norm_finiteModelCausalCore_append_le
          (F i) (D i) (divisor tail i) (c i))
        (by
          simpa [residualBudget] using
            add_le_add (le_refl ‖finiteModelResidualCore (F i) (D i) (c i)‖) ih)

/-- Predicate recording exactly that each local phase residual in a fixed packet vanishes. -/
def ResidualTendsToZero {ι : Type*} (F : ι → DiskMultiplier) (l : Filter ι) :
    FiniteBoundaryScalingPacket ι → Prop
  | terminal D c =>
      Tendsto (fun i => ‖finiteModelResidualCore (F i) (D i) (c i)‖) l (𝓝 0)
  | cons D c tail =>
      Tendsto (fun i => ‖finiteModelResidualCore (F i) (D i) (c i)‖) l (𝓝 0) ∧
        ResidualTendsToZero F l tail

theorem residualBudget_tendsto_zero
    {ι : Type*} {l : Filter ι} (F : ι → DiskMultiplier)
    (P : FiniteBoundaryScalingPacket ι)
    (hP : ResidualTendsToZero F l P) :
    Tendsto (residualBudget F P) l (𝓝 0) := by
  induction P with
  | terminal D c => exact hP
  | cons D c tail ih =>
      simpa [residualBudget] using hP.1.add (ih hP.2)

/-- Exact multiple-separated-point boundary-scaling lemma `(16)`: local residual convergence on
every finite block makes the causal compression vanish uniformly on the full packet model space. -/
theorem tendsto_norm_finiteModelCausalCore_divisor_zero
    {ι : Type*} {l : Filter ι} (F : ι → DiskMultiplier)
    (P : FiniteBoundaryScalingPacket ι)
    (hP : ResidualTendsToZero F l P) :
    Tendsto (fun i => ‖finiteModelCausalCore (F i) (divisor P i)‖) l (𝓝 0) := by
  exact squeeze_zero (fun _ => norm_nonneg _)
    (norm_finiteModelCausalCore_divisor_le_residualBudget F P)
    (residualBudget_tendsto_zero F P hP)

end FiniteBoundaryScalingPacket

/-- Persistent inner transport does not enlarge the finite-channel causal norm. -/
theorem norm_hardyMultiplierCausalCore_comp_crossing_le_finiteModelCausalCore
    (F B₀ : DiskMultiplier) (D : FiniteBlaschke)
    (hB₀ : HardyMultiplierIsometry B₀) :
    ‖(hardyMultiplierCausalCore F (B₀.mul D.toMultiplier)).comp
        (hardyMultiplierFiniteCrossingChannel B₀ D).starProjection‖ ≤
      ‖finiteModelCausalCore F D‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [ContinuousLinearMap.comp_apply]
  have hxC :=
    (hardyMultiplierFiniteCrossingChannel B₀ D).starProjection_apply_mem x
  rcases hxC with ⟨y, hy, hyEq⟩
  have hy_proj : (finiteBlaschkeModelSpace D).starProjection y = y :=
    (finiteBlaschkeModelSpace D).starProjection_eq_self_iff.mpr hy
  calc
    ‖hardyMultiplierCausalCore F (B₀.mul D.toMultiplier)
        ((hardyMultiplierFiniteCrossingChannel B₀ D).starProjection x)‖ =
        ‖hardyMultiplierCausalCore F D.toMultiplier y‖ := by
      rw [← hyEq]
      exact congrArg norm
        (hardyMultiplierCausalCore_cancel_persistent F B₀ D.toMultiplier hB₀ y)
    _ = ‖finiteModelCausalCore F D y‖ := by
      simp [finiteModelCausalCore, hy_proj]
    _ ≤ ‖finiteModelCausalCore F D‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖finiteModelCausalCore F D‖ * ‖hardyMul B₀ y‖ := by rw [hB₀]
    _ = ‖finiteModelCausalCore F D‖ *
        ‖(hardyMultiplierFiniteCrossingChannel B₀ D).starProjection x‖ := by
      exact congrArg (fun z : HardyDisk => ‖finiteModelCausalCore F D‖ * ‖z‖) hyEq
    _ ≤ ‖finiteModelCausalCore F D‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_left
        (by
          calc
            ‖(hardyMultiplierFiniteCrossingChannel B₀ D).starProjection x‖ ≤
                ‖(hardyMultiplierFiniteCrossingChannel B₀ D).starProjection‖ * ‖x‖ :=
              ContinuousLinearMap.le_opNorm _ _
            _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right
              (hardyMultiplierFiniteCrossingChannel B₀ D).starProjection_norm_le
              (norm_nonneg _)
            _ = ‖x‖ := one_mul _)
        (norm_nonneg _)

/-- Multiple separated collapsing blocks prove uniform causal disappearance on the transported
crossing channel, with an arbitrary finite- or infinite-degree persistent factor. -/
theorem tendsto_norm_hardyMultiplierCausalCore_packetCrossing_zero
    {ι : Type*} {l : Filter ι} (F B₀ : ι → DiskMultiplier)
    (P : FiniteBoundaryScalingPacket ι)
    (hB₀ : ∀ i, HardyMultiplierIsometry (B₀ i))
    (hP : P.ResidualTendsToZero F l) :
    Tendsto (fun i =>
      ‖(hardyMultiplierCausalCore (F i)
          ((B₀ i).mul (P.divisor i).toMultiplier)).comp
        (hardyMultiplierFiniteCrossingChannel (B₀ i) (P.divisor i)).starProjection‖)
      l (𝓝 0) := by
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun i => norm_hardyMultiplierCausalCore_comp_crossing_le_finiteModelCausalCore
      (F i) (B₀ i) (P.divisor i) (hB₀ i))
    (P.tendsto_norm_finiteModelCausalCore_divisor_zero F hP)

/-- Multiple separated collapsing blocks prove theorem-C Gram convergence `(11)`. -/
theorem tendsto_norm_hardyMultiplierPacketCrossingGramDefect_zero
    {ι : Type*} {l : Filter ι} (F B₀ : ι → DiskMultiplier)
    (P : FiniteBoundaryScalingPacket ι)
    (hF : ∀ i, HardyMultiplierIsometry (F i))
    (hB₀ : ∀ i, HardyMultiplierIsometry (B₀ i))
    (hP : P.ResidualTendsToZero F l) :
    Tendsto (fun i =>
      ‖channelGramDefect
        (hardyMultiplierFiniteCrossingChannel (B₀ i) (P.divisor i))
        (hardyMultiplierLeakageCore (F i)
          ((B₀ i).mul (P.divisor i).toMultiplier))‖) l (𝓝 0) := by
  have hc := tendsto_norm_hardyMultiplierCausalCore_packetCrossing_zero
    F B₀ P hB₀ hP
  convert hc.mul hc using 1
  · funext i
    exact norm_hardyMultiplierCrossingGramDefect_eq_sq
      (F i) (B₀ i) (P.divisor i) (hF i) (hB₀ i)
  · simp

/-- Multiple separated collapsing blocks prove theorem-C off-diagonal convergence `(12)`. -/
theorem tendsto_norm_hardyMultiplierPacketCrossingOffDiagonalGram_zero
    {ι : Type*} {l : Filter ι} (F B₀ : ι → DiskMultiplier)
    (P : FiniteBoundaryScalingPacket ι)
    (hF : ∀ i, HardyMultiplierIsometry (F i))
    (hB₀ : ∀ i, HardyMultiplierIsometry (B₀ i))
    (hP : P.ResidualTendsToZero F l) :
    Tendsto (fun i =>
      ‖channelOffDiagonalGram
        (hardyMultiplierFiniteCrossingChannel (B₀ i) (P.divisor i))
        (hardyMultiplierLeakageCore (F i)
          ((B₀ i).mul (P.divisor i).toMultiplier))‖) l (𝓝 0) := by
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun i => norm_hardyMultiplierCrossingOffDiagonalGram_le
      (F i) (B₀ i) (P.divisor i) (hF i) (hB₀ i))
    (tendsto_norm_hardyMultiplierCausalCore_packetCrossing_zero
      F B₀ P hB₀ hP)

end

end GaloisForLFunctions.HTGeometry
