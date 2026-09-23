import GaloisForLFunctions.HTGeometry.HardyMultiplierLeakagePythagoras
import GaloisForLFunctions.HTGeometry.HardyDiskKernelContinuity

open Complex Filter Topology
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Residual numerator compressed to the one-dimensional model space at `q`. -/
def singleModelResidualCore (F : DiskMultiplier) {q : ℂ} (hq : ‖q‖ < 1) (c : ℂ) :
    HardyDisk →L[ℂ] HardyDisk :=
  (hardyMul F - c • ContinuousLinearMap.id ℂ HardyDisk).comp
    (modelSpace hq).starProjection

theorem singleModelResidualCore_eq_rankOneTransport
    (F : DiskMultiplier) {q : ℂ} (hq : ‖q‖ < 1) (c : ℂ) :
    singleModelResidualCore F hq c =
      ((((‖hardyKernel hq‖ ^ (2 : ℕ) : ℝ) : ℂ))⁻¹) •
        rankOneTransport (𝕜 := ℂ) (hardyKernel hq)
          ((hardyMul F - c • ContinuousLinearMap.id ℂ HardyDisk) (hardyKernel hq)) := by
  rw [singleModelResidualCore, modelSpace_starProjection_eq_rankOneTransport]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, smul_apply, rankOneTransport_apply,
    map_smul]

/-- Exact norm of the residual multiplier on a rank-one model space. -/
theorem norm_singleModelResidualCore_eq
    (F : DiskMultiplier) {q : ℂ} (hq : ‖q‖ < 1) (c : ℂ) :
    ‖singleModelResidualCore F hq c‖ =
      ‖(hardyMul F - c • ContinuousLinearMap.id ℂ HardyDisk) (hardyKernel hq)‖ /
        ‖hardyKernel hq‖ := by
  rw [singleModelResidualCore_eq_rankOneTransport,
    norm_smul, norm_rankOneTransport]
  have hk : ‖hardyKernel hq‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (hardyKernel_ne_zero hq)
  rw [norm_inv, norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  field_simp

/-- For an inner numerator, rank-one residual energy is the exact boundary phase defect. -/
theorem norm_sq_singleModelResidualCore_eq
    (F : DiskMultiplier) (hF : HardyMultiplierIsometry F)
    {q : ℂ} (hq : ‖q‖ < 1) {c : ℂ} (hc : ‖c‖ = 1) :
    ‖singleModelResidualCore F hq c‖ ^ (2 : ℕ) =
      2 - 2 * Complex.re ((starRingEnd ℂ) c * F.fn q) := by
  rw [norm_singleModelResidualCore_eq, div_pow]
  have hk0 : ‖hardyKernel hq‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (hardyKernel_ne_zero hq)
  have hinner : inner ℂ (c • hardyKernel hq) (hardyMul F (hardyKernel hq)) =
      (starRingEnd ℂ) c * F.fn q * ((‖hardyKernel hq‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [inner_smul_left, inner_hardyKernel hq,
      hardyFun_hardyMul F (hardyKernel hq) hq,
      ← inner_hardyKernel hq, inner_self_eq_norm_sq_to_K]
    push_cast
    exact (mul_assoc _ _ _).symm
  have hresidual :
      (hardyMul F - c • ContinuousLinearMap.id ℂ HardyDisk) (hardyKernel hq) =
        hardyMul F (hardyKernel hq) - c • hardyKernel hq := by simp
  rw [hresidual, norm_sub_rev, norm_sub_sq (𝕜 := ℂ), norm_smul, hc, one_mul, hF,
    hinner]
  have hre :
      RCLike.re
        ((starRingEnd ℂ) c * F.fn q * ((‖hardyKernel hq‖ ^ (2 : ℕ) : ℝ) : ℂ)) =
        Complex.re ((starRingEnd ℂ) c * F.fn q) * ‖hardyKernel hq‖ ^ (2 : ℕ) := by
    change Complex.re
        ((starRingEnd ℂ) c * F.fn q * ((‖hardyKernel hq‖ ^ (2 : ℕ) : ℝ) : ℂ)) = _
    rw [Complex.mul_re]
    simp only [ofReal_re, ofReal_im, mul_zero, sub_zero]
  have hkpos : 0 < ‖hardyKernel hq‖ ^ (2 : ℕ) :=
    sq_pos_of_pos (norm_pos_iff.mpr (hardyKernel_ne_zero hq))
  rw [hre]
  field_simp
  ring

/-- If the numerator value converges to a unit local boundary value, its full residual multiplier
on the collapsing rank-one model channel converges to zero in operator norm. -/
theorem tendsto_norm_singleModelResidualCore_zero
    {ι : Type*} {l : Filter ι} (F : ι → DiskMultiplier)
    (hF : ∀ i, HardyMultiplierIsometry (F i))
    (q : ι → ℂ) (hq : ∀ i, ‖q i‖ < 1) (c : ι → ℂ)
    (hc : ∀ i, ‖c i‖ = 1)
    (hvalue : Tendsto (fun i => ‖(F i).fn (q i) - c i‖) l (𝓝 0)) :
    Tendsto (fun i => ‖singleModelResidualCore (F i) (hq i) (c i)‖) l (𝓝 0) := by
  have hphase : Tendsto
      (fun i => (starRingEnd ℂ) (c i) * (F i).fn (q i)) l (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    convert hvalue using 1
    funext i
    have hcc : (starRingEnd ℂ) (c i) * c i = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc i]
      norm_num
    calc
      ‖(starRingEnd ℂ) (c i) * (F i).fn (q i) - 1‖ =
          ‖(starRingEnd ℂ) (c i) * ((F i).fn (q i) - c i)‖ := by
        congr 1
        rw [mul_sub, hcc]
      _ = ‖(F i).fn (q i) - c i‖ := by
        rw [norm_mul, RCLike.norm_conj, hc i, one_mul]
  have hrhs : Tendsto
      (fun i => 2 - 2 * Complex.re
        ((starRingEnd ℂ) (c i) * (F i).fn (q i))) l (𝓝 0) := by
    have hcont : ContinuousAt (fun z : ℂ => 2 - 2 * Complex.re z) 1 := by fun_prop
    have h := hcont.tendsto.comp hphase
    norm_num only [Complex.one_re, mul_one, sub_self] at h
    change Tendsto (fun i => 2 - 2 * Complex.re
      ((starRingEnd ℂ) (c i) * (F i).fn (q i))) l (𝓝 0) at h
    exact h
  have hsq : Tendsto
      (fun i => ‖singleModelResidualCore (F i) (hq i) (c i)‖ ^ (2 : ℕ)) l (𝓝 0) := by
    exact hrhs.congr' (Filter.Eventually.of_forall fun i =>
      (norm_sq_singleModelResidualCore_eq (F i) (hF i) (hq i) (hc i)).symm)
  have hsqrt := hsq.sqrt
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsqrt

end

end GaloisForLFunctions.HTGeometry
