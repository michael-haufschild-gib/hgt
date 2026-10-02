import GaloisForLFunctions.RHTower.ThetaTailConfluentCenterLimits

/-! The literal coordinate-source Schur residual at a coalescing center pair. -/

noncomputable section
open Filter Topology Set
namespace RHTower.ThetaCoordinate
open ThetaConfluent

local notation "k" => thetaCuspFullSource
local notation "H" => thetaTailFirstMomentKernel
local notation "D" => ThetaSturm.determinant

/-- Coordinate-source residual with its actual inverse-Gram coefficients. -/
def coordinateResidual (z y : ℝ) : ℝ :=
  y*k y-z*k z*(H 0 0*H z y-H 0 z*H 0 y)/D 0 z

/-- The exact confluent coordinate residual; its global sign is a separate problem. -/
def confluentCoordinateResidual (y : ℝ) : ℝ :=
  y*k y-k 0*centerMixedRow y/centerEntry

private theorem mixed_row_slope_limit (y : ℝ) :
    Tendsto (fun z => (H z y-H 0 y)/z) (𝓝[>] 0) (𝓝 (centerMixedRow y)) := by
  have h : Tendsto (fun z => (H y z-H y 0)/z) (𝓝[>] 0) (𝓝 (centerMixedRow y)) := by
    simpa only [zero_add, smul_eq_mul, inv_mul_eq_div] using
      (kernel_center_hasDerivAt y).tendsto_slope_zero_right
  apply h.congr'
  filter_upwards with z
  rw [thetaTailFirstMomentKernel_comm y z, thetaTailFirstMomentKernel_comm y 0]

private theorem center_row_slope_limit :
    Tendsto (fun z => (H 0 z-H 0 0)/z) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
  simpa only [zero_add, smul_eq_mul, inv_mul_eq_div, centerMixedRow_zero] using
    (kernel_center_hasDerivAt 0).tendsto_slope_zero_right

private theorem coordinate_numerator_limit (y : ℝ) :
    Tendsto (fun z => (H 0 0*H z y-H 0 z*H 0 y)/z) (𝓝[>] 0)
      (𝓝 (H 0 0*centerMixedRow y)) := by
  have h := ((mixed_row_slope_limit y).const_mul (H 0 0)).sub
    (center_row_slope_limit.mul_const (H 0 y))
  convert! h using 1
  · ext z
    ring
  · simp only [zero_mul, sub_zero]

/-- No coordinate coefficient sign is assumed in the actual inverse limit. -/
theorem coordinateResidual_limit (y : ℝ) :
    Tendsto (fun z => coordinateResidual z y) (𝓝[>] 0)
      (𝓝 (confluentCoordinateResidual y)) := by
  have hJ : 0 < H 0 0 := by
    rw [ThetaTailTwoPoint.kernel_diag_eq_cut]
    exact ThetaSourceWard.thetaPrimeGammaCutEnergy_pos 0
  have hk : Tendsto k (𝓝[>] 0) (𝓝 (k 0)) :=
    contDiff_thetaCuspFullSource.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h := (hk.mul (coordinate_numerator_limit y)).div determinant_quotient_limit
    (mul_ne_zero hJ.ne' centerEntry_pos.ne')
  have hl : Tendsto (fun z => z*k z*(H 0 0*H z y-H 0 z*H 0 y)/D 0 z)
      (𝓝[>] 0) (𝓝 (k 0*centerMixedRow y/centerEntry)) := by
    have h' : Tendsto (fun z =>
        (k z*((H 0 0*H z y-H 0 z*H 0 y)/z))/(D 0 z/z^2)) (𝓝[>] 0)
        (𝓝 ((k 0*(H 0 0*centerMixedRow y))/(H 0 0*centerEntry))) := h
    have he : (k 0*(H 0 0*centerMixedRow y))/(H 0 0*centerEntry) =
        k 0*centerMixedRow y/centerEntry := by
      field_simp [hJ.ne', centerEntry_pos.ne']
    rw [he] at h'
    apply h'.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ 0 := ne_of_gt hz
    by_cases hd : D 0 z = 0
    · simp only [hd, zero_div, div_zero]
    · field_simp [hz', hd]
  exact hl.const_sub (y*k y)

end RHTower.ThetaCoordinate
