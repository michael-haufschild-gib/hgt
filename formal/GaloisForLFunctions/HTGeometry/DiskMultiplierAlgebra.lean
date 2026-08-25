import GaloisForLFunctions.HTGeometry.DiskMultiplierLineBoundary

open Complex MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Constant bounded analytic disk multiplier. -/
def DiskMultiplier.const (c : ℂ) : DiskMultiplier where
  fn := fun _ => c
  diff := differentiableOn_const c
  bd := ‖c‖
  bd_nonneg := norm_nonneg c
  bd_le := fun _ _ => le_rfl

/-- Sum in the bounded analytic disk-multiplier algebra. -/
def DiskMultiplier.add (φ ψ : DiskMultiplier) : DiskMultiplier where
  fn := fun z => φ.fn z + ψ.fn z
  diff := φ.diff.add ψ.diff
  bd := φ.bd + ψ.bd
  bd_nonneg := add_nonneg φ.bd_nonneg ψ.bd_nonneg
  bd_le := fun z hz => (norm_add_le _ _).trans (add_le_add (φ.bd_le z hz) (ψ.bd_le z hz))

/-- Additive inverse in the bounded analytic disk-multiplier algebra. -/
def DiskMultiplier.neg (φ : DiskMultiplier) : DiskMultiplier where
  fn := fun z => -φ.fn z
  diff := φ.diff.neg
  bd := φ.bd
  bd_nonneg := φ.bd_nonneg
  bd_le := fun z hz => by simpa using φ.bd_le z hz

/-- Difference in the bounded analytic disk-multiplier algebra. -/
def DiskMultiplier.sub (φ ψ : DiskMultiplier) : DiskMultiplier where
  fn := fun z => φ.fn z - ψ.fn z
  diff := φ.diff.sub ψ.diff
  bd := φ.bd + ψ.bd
  bd_nonneg := add_nonneg φ.bd_nonneg ψ.bd_nonneg
  bd_le := fun z hz => (norm_sub_le _ _).trans (add_le_add (φ.bd_le z hz) (ψ.bd_le z hz))

/-- Scalar multiple in the bounded analytic disk-multiplier algebra. -/
def DiskMultiplier.scale (c : ℂ) (φ : DiskMultiplier) : DiskMultiplier where
  fn := fun z => c * φ.fn z
  diff := (differentiableOn_const c).mul φ.diff
  bd := ‖c‖ * φ.bd
  bd_nonneg := mul_nonneg (norm_nonneg c) φ.bd_nonneg
  bd_le := fun z hz => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (φ.bd_le z hz) (norm_nonneg c)

/-- Reciprocal multiplier when the analytic function has a uniform positive lower bound. -/
def DiskMultiplier.invOfLowerBound (φ : DiskMultiplier) (δ : ℝ) (hδ : 0 < δ)
    (hlow : ∀ z ∈ Metric.ball (0 : ℂ) 1, δ ≤ ‖φ.fn z‖) : DiskMultiplier where
  fn := fun z => (φ.fn z)⁻¹
  diff := φ.diff.fun_inv fun z hz => norm_pos_iff.mp (hδ.trans_le (hlow z hz))
  bd := δ⁻¹
  bd_nonneg := (inv_pos.mpr hδ).le
  bd_le := fun z hz => by
    rw [norm_inv]
    have hnorm : 0 < ‖φ.fn z‖ := hδ.trans_le (hlow z hz)
    exact (inv_le_inv₀ hnorm hδ).2 (hlow z hz)

@[simp] theorem DiskMultiplier.const_fn (c : ℂ) (z : ℂ) :
    (DiskMultiplier.const c).fn z = c := rfl

@[simp] theorem DiskMultiplier.add_fn (φ ψ : DiskMultiplier) (z : ℂ) :
    (φ.add ψ).fn z = φ.fn z + ψ.fn z := rfl

@[simp] theorem DiskMultiplier.neg_fn (φ : DiskMultiplier) (z : ℂ) :
    φ.neg.fn z = -φ.fn z := rfl

@[simp] theorem DiskMultiplier.sub_fn (φ ψ : DiskMultiplier) (z : ℂ) :
    (φ.sub ψ).fn z = φ.fn z - ψ.fn z := rfl

@[simp] theorem DiskMultiplier.scale_fn (c : ℂ) (φ : DiskMultiplier) (z : ℂ) :
    (φ.scale c).fn z = c * φ.fn z := rfl

@[simp] theorem DiskMultiplier.invOfLowerBound_fn
    (φ : DiskMultiplier) (δ : ℝ) (hδ : 0 < δ)
    (hlow : ∀ z ∈ Metric.ball (0 : ℂ) 1, δ ≤ ‖φ.fn z‖) (z : ℂ) :
    (φ.invOfLowerBound δ hδ hlow).fn z = (φ.fn z)⁻¹ := rfl

theorem DiskMultiplier.mul_invOfLowerBound_fn
    (φ : DiskMultiplier) (δ : ℝ) (hδ : 0 < δ)
    (hlow : ∀ z ∈ Metric.ball (0 : ℂ) 1, δ ≤ ‖φ.fn z‖)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    (φ.mul (φ.invOfLowerBound δ hδ hlow)).fn z = 1 := by
  change φ.fn z * (φ.fn z)⁻¹ = 1
  exact mul_inv_cancel₀ (norm_pos_iff.mp (hδ.trans_le (hlow z hz)))

theorem hardyOf_congr {φ ψ : DiskMultiplier}
    (h : ∀ z ∈ Metric.ball (0 : ℂ) 1, φ.fn z = ψ.fn z) :
    hardyOf φ = hardyOf ψ := by
  apply hardyDisk_ext
  intro z hz
  rw [hardyFun_hardyOf φ hz, hardyFun_hardyOf ψ hz]
  exact h z (by simpa [Metric.mem_ball, dist_zero_right] using hz)

theorem diskMultiplierLineBoundary_congr_ae {φ ψ : DiskMultiplier}
    (h : ∀ z ∈ Metric.ball (0 : ℂ) 1, φ.fn z = ψ.fn z) :
    diskMultiplierLineBoundary φ =ᵐ[volume] diskMultiplierLineBoundary ψ := by
  have hhardy : hardyOf φ = hardyOf ψ := hardyOf_congr h
  have hcircle : diskMultiplierBoundaryFun φ = diskMultiplierBoundaryFun ψ := by
    simp only [diskMultiplierBoundaryFun, hhardy]
  filter_upwards [diskMultiplierLineBoundary_ae φ,
    diskMultiplierLineBoundary_ae ψ] with x hφ hψ
  rw [hφ, hψ, hcircle]

private theorem line_eventuallyEq_of_circle_eventuallyEq
    {f g : Circle → ℂ} (h : f =ᵐ[circleLebesgue] g) :
    (fun x => f (circleCayley x)) =ᵐ[volume]
      fun x => g (circleCayley x) := by
  have hweighted := h.comp_tendsto
    circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae
  exact (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
    standardCauchyWeight_pos).mp hweighted

theorem hardyOf_add (φ ψ : DiskMultiplier) :
    hardyOf (φ.add ψ) = hardyOf φ + hardyOf ψ := by
  apply hardyDisk_ext
  intro z hz
  rw [hardyFun_hardyOf (φ.add ψ) hz, hardyFun_add _ _ hz,
    hardyFun_hardyOf φ hz, hardyFun_hardyOf ψ hz]
  rfl

theorem hardyOf_neg (φ : DiskMultiplier) :
    hardyOf φ.neg = -hardyOf φ := by
  apply hardyDisk_ext
  intro z hz
  rw [hardyFun_hardyOf φ.neg hz]
  change -φ.fn z = hardyFun (-hardyOf φ) z
  rw [show -hardyOf φ = (-1 : ℂ) • hardyOf φ by simp,
    hardyFun_smul (-1 : ℂ) (hardyOf φ) hz, hardyFun_hardyOf φ hz]
  simp

theorem hardyOf_sub (φ ψ : DiskMultiplier) :
    hardyOf (φ.sub ψ) = hardyOf φ - hardyOf ψ := by
  apply hardyDisk_ext
  intro z hz
  rw [hardyFun_hardyOf (φ.sub ψ) hz]
  change φ.fn z - ψ.fn z = hardyFun (hardyOf φ - hardyOf ψ) z
  rw [show hardyOf φ - hardyOf ψ = hardyOf φ + (-hardyOf ψ) by rfl,
    hardyFun_add (hardyOf φ) (-hardyOf ψ) hz,
    show -hardyOf ψ = (-1 : ℂ) • hardyOf ψ by simp,
    hardyFun_smul (-1 : ℂ) (hardyOf ψ) hz,
    hardyFun_hardyOf φ hz, hardyFun_hardyOf ψ hz]
  simp [sub_eq_add_neg]

theorem hardyOf_scale (c : ℂ) (φ : DiskMultiplier) :
    hardyOf (φ.scale c) = c • hardyOf φ := by
  apply hardyDisk_ext
  intro z hz
  rw [hardyFun_hardyOf (φ.scale c) hz, hardyFun_smul _ _ hz,
    hardyFun_hardyOf φ hz]
  rfl

theorem diskMultiplierBoundaryFun_add_ae (φ ψ : DiskMultiplier) :
    diskMultiplierBoundaryFun (φ.add ψ) =ᵐ[circleLebesgue]
      fun z => diskMultiplierBoundaryFun φ z + diskMultiplierBoundaryFun ψ z := by
  rw [diskMultiplierBoundaryFun, hardyOf_add, map_add]
  exact Lp.coeFn_add _ _

theorem diskMultiplierBoundaryFun_neg_ae (φ : DiskMultiplier) :
    diskMultiplierBoundaryFun φ.neg =ᵐ[circleLebesgue]
      fun z => -diskMultiplierBoundaryFun φ z := by
  rw [diskMultiplierBoundaryFun, hardyOf_neg, map_neg]
  exact Lp.coeFn_neg _

theorem diskMultiplierBoundaryFun_sub_ae (φ ψ : DiskMultiplier) :
    diskMultiplierBoundaryFun (φ.sub ψ) =ᵐ[circleLebesgue]
      fun z => diskMultiplierBoundaryFun φ z - diskMultiplierBoundaryFun ψ z := by
  rw [diskMultiplierBoundaryFun, hardyOf_sub, map_sub]
  exact Lp.coeFn_sub _ _

theorem diskMultiplierBoundaryFun_scale_ae (c : ℂ) (φ : DiskMultiplier) :
    diskMultiplierBoundaryFun (φ.scale c) =ᵐ[circleLebesgue]
      fun z => c * diskMultiplierBoundaryFun φ z := by
  rw [diskMultiplierBoundaryFun, hardyOf_scale, map_smul]
  filter_upwards [Lp.coeFn_smul c (hardyDiskBoundary (hardyOf φ))] with z hz
  simpa only [Pi.smul_apply, smul_eq_mul, diskMultiplierBoundaryFun] using hz

theorem hardyOf_const (c : ℂ) :
    hardyOf (DiskMultiplier.const c) = c • hardyOne := by
  apply hardyDisk_ext
  intro z hz
  rw [hardyFun_hardyOf (DiskMultiplier.const c) hz,
    hardyFun_smul c hardyOne hz, hardyFun_hardyOne hz]
  simp

theorem diskMultiplierBoundaryFun_const_ae (c : ℂ) :
    diskMultiplierBoundaryFun (DiskMultiplier.const c) =ᵐ[circleLebesgue]
      fun _ => c := by
  obtain ⟨ns, -, hae⟩ :=
    exists_diskMultiplierRadialBoundary_subseq_ae (DiskMultiplier.const c)
  filter_upwards [hae] with z hz
  apply tendsto_nhds_unique hz
  convert tendsto_const_nhds using 1
  funext i
  rfl

theorem diskMultiplierLineBoundary_add_ae (φ ψ : DiskMultiplier) :
    diskMultiplierLineBoundary (φ.add ψ) =ᵐ[volume]
      fun x => diskMultiplierLineBoundary φ x + diskMultiplierLineBoundary ψ x := by
  have hcircle := line_eventuallyEq_of_circle_eventuallyEq
    (diskMultiplierBoundaryFun_add_ae φ ψ)
  filter_upwards [hcircle, diskMultiplierLineBoundary_ae (φ.add ψ),
    diskMultiplierLineBoundary_ae φ, diskMultiplierLineBoundary_ae ψ]
      with x h hsum hφ hψ
  rw [hsum, h, hφ, hψ]

theorem diskMultiplierLineBoundary_neg_ae (φ : DiskMultiplier) :
    diskMultiplierLineBoundary φ.neg =ᵐ[volume]
      fun x => -diskMultiplierLineBoundary φ x := by
  have hcircle := line_eventuallyEq_of_circle_eventuallyEq
    (diskMultiplierBoundaryFun_neg_ae φ)
  filter_upwards [hcircle, diskMultiplierLineBoundary_ae φ.neg,
    diskMultiplierLineBoundary_ae φ] with x h hneg hφ
  rw [hneg, h, hφ]

theorem diskMultiplierLineBoundary_sub_ae (φ ψ : DiskMultiplier) :
    diskMultiplierLineBoundary (φ.sub ψ) =ᵐ[volume]
      fun x => diskMultiplierLineBoundary φ x - diskMultiplierLineBoundary ψ x := by
  have hcircle := line_eventuallyEq_of_circle_eventuallyEq
    (diskMultiplierBoundaryFun_sub_ae φ ψ)
  filter_upwards [hcircle, diskMultiplierLineBoundary_ae (φ.sub ψ),
    diskMultiplierLineBoundary_ae φ, diskMultiplierLineBoundary_ae ψ]
      with x h hsub hφ hψ
  rw [hsub, h, hφ, hψ]

theorem diskMultiplierLineBoundary_scale_ae (c : ℂ) (φ : DiskMultiplier) :
    diskMultiplierLineBoundary (φ.scale c) =ᵐ[volume]
      fun x => c * diskMultiplierLineBoundary φ x := by
  have hcircle := line_eventuallyEq_of_circle_eventuallyEq
    (diskMultiplierBoundaryFun_scale_ae c φ)
  filter_upwards [hcircle, diskMultiplierLineBoundary_ae (φ.scale c),
    diskMultiplierLineBoundary_ae φ] with x h hscale hφ
  rw [hscale, h, hφ]

theorem diskMultiplierLineBoundary_const_ae (c : ℂ) :
    diskMultiplierLineBoundary (DiskMultiplier.const c) =ᵐ[volume]
      fun _ => c := by
  have hcircle := line_eventuallyEq_of_circle_eventuallyEq
    (diskMultiplierBoundaryFun_const_ae c)
  filter_upwards [hcircle, diskMultiplierLineBoundary_ae (DiskMultiplier.const c)]
      with x h hconst
  rw [hconst, h]

theorem diskMultiplierLineBoundary_invOfLowerBound_ae
    (φ : DiskMultiplier) (δ : ℝ) (hδ : 0 < δ)
    (hlow : ∀ z ∈ Metric.ball (0 : ℂ) 1, δ ≤ ‖φ.fn z‖) :
    diskMultiplierLineBoundary (φ.invOfLowerBound δ hδ hlow) =ᵐ[volume]
      fun x => (diskMultiplierLineBoundary φ x)⁻¹ := by
  let ψ := φ.invOfLowerBound δ hδ hlow
  have hprod : diskMultiplierLineBoundary (φ.mul ψ) =ᵐ[volume]
      fun _ => 1 := by
    exact (diskMultiplierLineBoundary_congr_ae
      (ψ := DiskMultiplier.const 1) fun z hz => by
        rw [DiskMultiplier.mul_invOfLowerBound_fn φ δ hδ hlow hz]
        rfl).trans (diskMultiplierLineBoundary_const_ae 1)
  filter_upwards [diskMultiplierLineBoundary_mul_ae φ ψ, hprod,
    diskMultiplierLineBoundary_ne_zero_ae φ
      ⟨0, Metric.mem_ball_self zero_lt_one,
        norm_pos_iff.mp (hδ.trans_le (hlow 0 (Metric.mem_ball_self zero_lt_one)))⟩]
      with x hmul hone hφ
  have heq : diskMultiplierLineBoundary φ x *
      diskMultiplierLineBoundary ψ x = 1 := by rw [← hmul, hone]
  apply mul_left_cancel₀ hφ
  rw [heq, mul_inv_cancel₀ hφ]

theorem diskMultiplierBoundaryFun_invOfLowerBound_ae
    (φ : DiskMultiplier) (δ : ℝ) (hδ : 0 < δ)
    (hlow : ∀ z ∈ Metric.ball (0 : ℂ) 1, δ ≤ ‖φ.fn z‖) :
    diskMultiplierBoundaryFun (φ.invOfLowerBound δ hδ hlow) =ᵐ[circleLebesgue]
      fun z => (diskMultiplierBoundaryFun φ z)⁻¹ := by
  let ψ := φ.invOfLowerBound δ hδ hlow
  have hhardy : hardyOf (φ.mul ψ) = hardyOf (DiskMultiplier.const 1) :=
    hardyOf_congr fun z hz => by
      rw [DiskMultiplier.mul_invOfLowerBound_fn φ δ hδ hlow hz]
      rfl
  have hprodEq : diskMultiplierBoundaryFun (φ.mul ψ) =
      diskMultiplierBoundaryFun (DiskMultiplier.const 1) := by
    simp only [diskMultiplierBoundaryFun, hhardy]
  filter_upwards [diskMultiplierBoundaryFun_mul_ae φ ψ,
    diskMultiplierBoundaryFun_const_ae 1,
    diskMultiplierBoundary_ne_zero_ae φ
      ⟨0, Metric.mem_ball_self zero_lt_one,
        norm_pos_iff.mp (hδ.trans_le (hlow 0 (Metric.mem_ball_self zero_lt_one)))⟩]
      with z hmul hone hφ
  have heq : diskMultiplierBoundaryFun φ z *
      diskMultiplierBoundaryFun ψ z = 1 := by
    rw [← hmul, hprodEq, hone]
  apply mul_left_cancel₀ hφ
  rw [heq, mul_inv_cancel₀ hφ]

end

end GaloisForLFunctions.HTGeometry
