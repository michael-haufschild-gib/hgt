import GaloisForLFunctions.HTGeometry.HorizontalLayerBlaschke
import GaloisForLFunctions.HTGeometry.ProjectiveCauchyDensityControl

open Complex Topology
open scoped OnePoint

noncomputable section

namespace GaloisForLFunctions.HTGeometry

abbrev ProjectiveBoundary := C(OnePoint ℝ, ℂ)

/-- Totalized projective resolvent. At nonreal poles this is the literal Cauchy resolvent;
at real poles it is set to zero. Horizontal-layer arguments only use nonreal poles. -/
def projectiveNonrealResolvent (z : ℂ) : ProjectiveBoundary :=
  if hz : z.im ≠ 0 then
    ⟨projectiveCauchyPower z 0, continuous_projectiveCauchyPower z hz 0⟩
  else 0

@[simp]
theorem projectiveNonrealResolvent_infty (z : ℂ) :
    projectiveNonrealResolvent z ∞ = 0 := by
  unfold projectiveNonrealResolvent
  split <;> simp

theorem projectiveNonrealResolvent_coe {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) :
    projectiveNonrealResolvent z (x : OnePoint ℝ) = ((x : ℂ) - z)⁻¹ := by
  simp [projectiveNonrealResolvent, hz]

/-- Projectively completed boundary symbol of one horizontal Blaschke layer. -/
def horizontalLayerProjective (a ω : ℝ) : ProjectiveBoundary :=
  let upper := (2 * I * ((a + ω : ℝ) : ℂ)) •
    projectiveNonrealResolvent (-((a + ω : ℝ) : ℂ) * I)
  let lower := (2 * I * ((a - ω : ℝ) : ℂ)) •
    projectiveNonrealResolvent (((a - ω : ℝ) : ℂ) * I)
  (1 - upper) * (1 + lower)

/-- Projectively completed derivative symbol of one horizontal Blaschke layer. -/
def horizontalLayerInfinitesimalProjective (a : ℝ) : ProjectiveBoundary :=
  (-2 * I) • projectiveNonrealResolvent ((a : ℂ) * I) +
    (-2 * I) • projectiveNonrealResolvent (-(a : ℂ) * I)

@[simp]
theorem horizontalLayerProjective_infty (a ω : ℝ) :
    horizontalLayerProjective a ω ∞ = 1 := by
  simp [horizontalLayerProjective]

@[simp]
theorem horizontalLayerInfinitesimalProjective_infty (a : ℝ) :
    horizontalLayerInfinitesimalProjective a ∞ = 0 := by
  simp [horizontalLayerInfinitesimalProjective]

theorem horizontalLayerProjective_coe {a ω : ℝ}
    (hplus : a + ω ≠ 0) (hminus : a - ω ≠ 0) (x : ℝ) :
    horizontalLayerProjective a ω (x : OnePoint ℝ) =
      horizontalLayerFactorRaw a ω x := by
  have hzplus : (-((a + ω : ℝ) : ℂ) * I).im ≠ 0 := by
    simpa [add_comm] using (neg_ne_zero.mpr hplus)
  have hzminus : (((a - ω : ℝ) : ℂ) * I).im ≠ 0 := by
    simp [hminus]
  rw [horizontalLayerProjective]
  simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply,
    ContinuousMap.one_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [projectiveNonrealResolvent_coe hzplus,
    projectiveNonrealResolvent_coe hzminus]
  have hdenplus :
      (x : ℂ) - (-((a + ω : ℝ) : ℂ) * I) =
        (x : ℂ) + ((a + ω : ℝ) : ℂ) * I := by ring
  rw [hdenplus]
  have hp := real_add_mul_I_ne_zero (x := x) hplus
  have hm := real_sub_mul_I_ne_zero (x := x) hminus
  have hfirst :
      1 - (2 * I * ((a + ω : ℝ) : ℂ)) *
          (((x : ℂ) + ((a + ω : ℝ) : ℂ) * I)⁻¹) =
        ((x : ℂ) - ((a + ω : ℝ) : ℂ) * I) /
          ((x : ℂ) + ((a + ω : ℝ) : ℂ) * I) := by
    apply (eq_div_iff hp).2
    rw [sub_mul, one_mul, mul_assoc, inv_mul_cancel₀ hp, mul_one]
    ring
  have hsecond :
      1 + (2 * I * ((a - ω : ℝ) : ℂ)) *
          (((x : ℂ) - ((a - ω : ℝ) : ℂ) * I)⁻¹) =
        ((x : ℂ) + ((a - ω : ℝ) : ℂ) * I) /
          ((x : ℂ) - ((a - ω : ℝ) : ℂ) * I) := by
    apply (eq_div_iff hm).2
    rw [add_mul, one_mul, mul_assoc, inv_mul_cancel₀ hm, mul_one]
    ring
  rw [hfirst, hsecond]
  rfl

theorem horizontalLayerInfinitesimalProjective_coe {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    horizontalLayerInfinitesimalProjective a (x : OnePoint ℝ) =
      horizontalLayerFullInfinitesimalSymbol a x := by
  have hzplus : (((a : ℝ) : ℂ) * I).im ≠ 0 := by simp [ha]
  have hzminus : (-(a : ℂ) * I).im ≠ 0 := by simp [ha]
  rw [horizontalLayerInfinitesimalProjective]
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [projectiveNonrealResolvent_coe hzplus,
    projectiveNonrealResolvent_coe hzminus]
  unfold horizontalLayerFullInfinitesimalSymbol
  ring

/-- Normalized projective one-layer slope. -/
def horizontalLayerNormalizedProjective (a ω : ℝ) : ProjectiveBoundary :=
  ((ω : ℂ)⁻¹) • (horizontalLayerProjective a ω - 1)

theorem horizontalLayerNormalizedProjective_coe {a ω : ℝ}
    (hplus : a + ω ≠ 0) (hminus : a - ω ≠ 0) (x : ℝ) :
    horizontalLayerNormalizedProjective a ω (x : OnePoint ℝ) =
      (horizontalLayerFactorRaw a ω x - 1) / (ω : ℂ) := by
  rw [horizontalLayerNormalizedProjective]
  simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply,
    smul_eq_mul, horizontalLayerProjective_coe hplus hminus]
  rw [div_eq_inv_mul]

theorem norm_horizontalLayerNormalizedProjective_sub_le {a ω : ℝ} (ha : 0 < a)
    (hω : ω ≠ 0) (hsmall : |ω| ≤ a / 2) :
    ‖horizontalLayerNormalizedProjective a ω -
        horizontalLayerInfinitesimalProjective a‖ ≤ 48 * |ω| / a ^ 2 := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  cases t with
  | infty =>
      simp [horizontalLayerNormalizedProjective]
      positivity
  | coe x =>
      have hωbounds := abs_le.mp hsmall
      have hplus : 0 < a + ω := by linarith
      have hminus : 0 < a - ω := by linarith
      simp only [ContinuousMap.sub_apply]
      rw [horizontalLayerNormalizedProjective_coe hplus.ne' hminus.ne',
        horizontalLayerInfinitesimalProjective_coe ha.ne']
      exact norm_horizontalLayerFactorRaw_normalized_sub_le ha hω hsmall x

end GaloisForLFunctions.HTGeometry
