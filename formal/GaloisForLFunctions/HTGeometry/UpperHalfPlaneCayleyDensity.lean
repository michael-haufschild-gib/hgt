import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

/-!
The Cayley map from the unit disk to the upper half-plane has exact hyperbolic
density pullback.  This is the measure-transport half of the literal native
circle polar realization used by the cyclic Peierls cap pairing.
-/
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory Set Metric
noncomputable section

/-- Cayley map from the upper half-plane to the unit disk, centered at `I`. -/
def upperToDisk (z : ℂ) : ℂ := (z - Complex.I) / (z + Complex.I)

/-- Inverse Cayley map from the unit disk to the upper half-plane. -/
def diskToUpper (w : ℂ) : ℂ := Complex.I * (1 + w) / (1 - w)

/-- Complex derivative of the inverse Cayley map. -/
theorem hasDerivAt_diskToUpper {w : ℂ} (hw : w ≠ 1) :
    HasDerivAt diskToUpper (2 * Complex.I / (1 - w) ^ (2 : ℕ)) w := by
  have hv : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have hu : HasDerivAt (fun z : ℂ => Complex.I * (1 + z)) Complex.I w := by
    simpa using ((hasDerivAt_id w).const_add (1 : ℂ)).const_mul Complex.I
  have hd : HasDerivAt (fun z : ℂ => (1 : ℂ) - z) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub (1 : ℂ)
  have hdiv := hu.div hd hv
  rw [show diskToUpper = (fun z : ℂ => Complex.I * (1 + z)) / (fun z : ℂ => (1 : ℂ) - z) by rfl,
    show (2 : ℂ) * Complex.I / (1 - w) ^ (2 : ℕ) =
      (Complex.I * (1 - w) - Complex.I * (1 + w) * (-1)) / (1 - w) ^ (2 : ℕ) by ring]
  exact hdiv

/-- Exact height of the inverse Cayley image. -/
theorem diskToUpper_im {w : ℂ} (hw : w ≠ 1) :
    (diskToUpper w).im = (1 - Complex.normSq w) / Complex.normSq (1 - w) := by
  have hne : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have hns : Complex.normSq ((1 : ℂ) - w) ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hne)
  rw [diskToUpper, Complex.div_im]
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
  field_simp
  ring

/-- The inverse Cayley map sends the open unit disk into the upper half-plane. -/
theorem diskToUpper_im_pos (w : ℂ) (hw : w ∈ ball 0 1) :
    0 < (diskToUpper w).im := by
  have hnorm : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hw
  have hsq : Complex.normSq w < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [show 0 ≤ ‖w‖ from norm_nonneg _]
  have hne : w ≠ 1 := by
    intro h
    rw [h] at hsq
    norm_num at hsq
  rw [diskToUpper_im hne]
  exact div_pos (by linarith) (Complex.normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm hne)))

/-- Absolute real Jacobian of inverse Cayley. -/
theorem abs_det_diskToUpper_realFDeriv (w : ℂ) :
    |((2 * Complex.I / (1 - w) ^ (2 : ℕ)) • (1 : ℂ →L[ℝ] ℂ)).det| =
      4 / Complex.normSq (1 - w) ^ (2 : ℕ) := by
  rw [← Complex.restrictScalars_toSpanSingleton]
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq, norm_pow]
  rw [abs_of_nonneg (by positivity)]
  norm_num

/-- Inverse Cayley pulls `dx dy / y²` back to `4 dx dy / (1-|w|²)²`. -/
theorem diskToUpper_hyperbolic_density (w : ℂ) (hw : w ∈ ball 0 1) :
    |((2 * Complex.I / (1 - w) ^ (2 : ℕ)) • (1 : ℂ →L[ℝ] ℂ)).det| *
        ((diskToUpper w).im)⁻¹ ^ (2 : ℕ) =
      4 / (1 - Complex.normSq w) ^ (2 : ℕ) := by
  have hnorm : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hw
  have hsq : Complex.normSq w < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [show 0 ≤ ‖w‖ from norm_nonneg _]
  have hne : w ≠ 1 := by
    intro h
    rw [h] at hsq
    norm_num at hsq
  have hnum : 1 - Complex.normSq w ≠ 0 := by linarith
  have hden : Complex.normSq (1 - w) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm hne)))
  rw [abs_det_diskToUpper_realFDeriv, diskToUpper_im hne]
  field_simp [hnum, hden]

/-- Cayley maps every upper-half-plane point strictly inside the unit disk. -/
theorem normSq_upperToDisk_lt_one {z : ℂ} (hz : 0 < z.im) :
    Complex.normSq (upperToDisk z) < 1 := by
  have hne : z + Complex.I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
    linarith
  have hpos : 0 < Complex.normSq (z + Complex.I) := Complex.normSq_pos.mpr hne
  rw [upperToDisk, Complex.normSq_div, div_lt_one hpos]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.I_re, Complex.I_im]
  nlinarith

/-- Inverse Cayley followed by Cayley is the identity away from the boundary point `1`. -/
theorem upperToDisk_diskToUpper {w : ℂ} (hw : w ≠ 1) :
    upperToDisk (diskToUpper w) = w := by
  have hne : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have hden : diskToUpper w + Complex.I = (2 * Complex.I) / (1 - w) := by
    rw [diskToUpper, div_add' _ _ _ hne]
    field_simp
    ring
  have hdne : diskToUpper w + Complex.I ≠ 0 := by
    rw [hden]
    exact div_ne_zero (by simp) hne
  rw [upperToDisk, div_eq_iff hdne, hden, diskToUpper]
  field_simp
  ring

/-- Cayley followed by inverse Cayley is the identity on the upper half-plane. -/
theorem diskToUpper_upperToDisk {z : ℂ} (hz : 0 < z.im) :
    diskToUpper (upperToDisk z) = z := by
  have h : z + Complex.I ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith
  have hne : (1 : ℂ) - upperToDisk z ≠ 0 := by
    rw [upperToDisk]
    apply sub_ne_zero.mpr
    intro heq
    have heq' : (1 : ℂ) * (z + Complex.I) = z - Complex.I :=
      (eq_div_iff h).mp heq
    have : (2 : ℂ) * Complex.I = 0 := by linear_combination heq'
    simp at this
  rw [diskToUpper, div_eq_iff hne]
  have hone : 1 - upperToDisk z = (2 * Complex.I) / (z + Complex.I) := by
    rw [upperToDisk, eq_div_iff h, sub_mul, div_mul_cancel₀ _ h, one_mul]
    ring
  rw [hone, upperToDisk]
  field_simp
  ring

/-- Inverse Cayley is a global bijection from the open disk to the upper half-plane. -/
theorem diskToUpper_image_ball :
    diskToUpper '' ball 0 1 = {z : ℂ | 0 < z.im} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact diskToUpper_im_pos w hw
  · intro hz
    let w : ℂ := upperToDisk z
    have hsq : Complex.normSq w < 1 := by
      simpa only [w] using normSq_upperToDisk_lt_one hz
    have hnorm : ‖w‖ < 1 := by
      rw [Complex.normSq_eq_norm_sq] at hsq
      nlinarith [show 0 ≤ ‖w‖ from norm_nonneg _]
    have hw : w ∈ ball 0 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hnorm
    refine ⟨w, hw, ?_⟩
    exact diskToUpper_upperToDisk hz

/-- The inverse Cayley map is injective on the literal open disk. -/
theorem diskToUpper_injOn_ball : InjOn diskToUpper (ball 0 1) := by
  intro u hu v hv huv
  have hu_norm : ‖u‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hu
  have hv_norm : ‖v‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hv
  have hu_ne : u ≠ 1 := by
    intro h
    rw [h] at hu_norm
    norm_num at hu_norm
  have hv_ne : v ≠ 1 := by
    intro h
    rw [h] at hv_norm
    norm_num at hv_norm
  calc
    u = upperToDisk (diskToUpper u) := (upperToDisk_diskToUpper hu_ne).symm
    _ = upperToDisk (diskToUpper v) := congrArg upperToDisk huv
    _ = v := upperToDisk_diskToUpper hv_ne

/-- Exact change of variables for inverse Cayley over its literal disk domain. -/
theorem integral_diskToUpper_image {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) :
    (∫ z in {z : ℂ | 0 < z.im}, f z) =
      ∫ w in ball 0 1,
        |((2 * Complex.I / (1 - w) ^ (2 : ℕ)) • (1 : ℂ →L[ℝ] ℂ)).det| • f (diskToUpper w) := by
  rw [← diskToUpper_image_ball]
  apply integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_ball _
    diskToUpper_injOn_ball f
  intro w hw
  have hw_norm : ‖w‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hw
  have hw_ne : w ≠ 1 := by
    intro h
    rw [h] at hw_norm
    norm_num at hw_norm
  exact (hasDerivAt_diskToUpper hw_ne).complexToReal_fderiv.hasFDerivWithinAt

/-- The literal hyperbolic-area change of variables from the disk to the upper half-plane. -/
theorem integral_diskToUpper_hyperbolic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) :
    (∫ z in {z : ℂ | 0 < z.im}, (z.im)⁻¹ ^ (2 : ℕ) • f z) =
      ∫ w in ball 0 1,
        (4 / (1 - Complex.normSq w) ^ (2 : ℕ)) • f (diskToUpper w) := by
  rw [integral_diskToUpper_image (fun z : ℂ => (z.im)⁻¹ ^ (2 : ℕ) • f z)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
  rw [smul_smul, diskToUpper_hyperbolic_density w hw]

end
end GaloisForLFunctions.HTGeometry
