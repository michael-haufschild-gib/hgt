import GaloisForLFunctions.RHTower.ProlateBandEigenvalueSimplicity
import GaloisForLFunctions.RHTower.BandFormBridge

/-!
# The small-aperture rank-one anchor for the Slepian band family

At aperture zero the band operator vanishes, and its operator-norm derivative is the constant-kernel
operator.  This file identifies that derivative exactly as a positive rank-one operator and packages
the quantitative expansion

```text
B_c = (c / π) |1⟩⟨1| + R_c,       ‖R_c‖ ≤ 4 c² / π,
```

where `1` is the unnormalised constant class on `[-1,1]`, of squared norm `2`.  Thus the leading
eigenvalue is `2c/π` and every other leading-order direction is zero.  This is the rank-one
spectral anchor needed by the Slepian--Pollak no-crossing argument; no eigenvalue asymptotic is
assumed.
-/

noncomputable section

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

open MeasureTheory Set

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- The entire sinc profile vanishes when the aperture is zero. -/
theorem sincSmooth_aperture_zero (u : ℝ) : sincSmooth 0 u = 0 := by
  rw [sincSmooth]
  rcases eq_or_ne u 0 with rfl | hu
  · rw [dslope_same]
    simp
  · rw [dslope_of_ne _ hu]
    simp [slope]

/-- The continuous Slepian kernel is zero at aperture zero. -/
theorem sincKernelContinuous_zero : sincKernelContinuous 0 = 0 := by
  ext z
  change sincSmooth 0 ((z.1 : ℝ) - (z.2 : ℝ)) = 0
  exact sincSmooth_aperture_zero _

/-- The band operator itself vanishes at aperture zero. -/
theorem bandOperatorL2_zero : bandOperatorL2 0 = 0 := by
  apply norm_eq_zero.mp
  have h := norm_continuousKernelOperator_le (a := (-1 : ℝ)) (b := 1)
    (by norm_num : (-1 : ℝ) ≤ 1) (sincKernelContinuous 0)
  rw [← bandOperatorL2] at h
  rw [sincKernelContinuous_zero] at h
  simpa using h

/-- Quantitative operator-norm linearisation at the zero aperture. -/
theorem norm_bandOperatorL2_sub_linear_zero_le (c : ℝ) :
    ‖bandOperatorL2 c - c • cosOperatorL2 0‖ ≤ 4 * c ^ 2 / Real.pi := by
  have h := norm_bandOperator_taylor_le 0 c
  simpa [bandOperatorL2_zero] using h

/-- The unnormalised constant class on the unit band. -/
noncomputable def constantBandClass : RealIntervalL2 (-1 : ℝ) 1 :=
  bandClass (fun _ : ℝ => 1) continuous_const

/-- The zero-aperture cosine operator maps every vector to its integral times the constant class. -/
theorem cosOperatorL2_zero_apply (f : RealIntervalL2 (-1 : ℝ) 1) :
    cosOperatorL2 0 f =
      ((∫ y : ClosedInterval (-1 : ℝ) 1, f y ∂volume) / Real.pi) • constantBandClass := by
  change continuousKernelOperator (cosKernelContinuous 0) f = _
  apply Lp.ext
  filter_upwards [continuousKernelOperator_coeFn (cosKernelContinuous 0) f,
    Lp.coeFn_smul ((∫ y : ClosedInterval (-1 : ℝ) 1, f y ∂volume) / Real.pi)
      constantBandClass,
    coeFn_bandClass (fun _ : ℝ => 1) continuous_const] with x hleft hright hone
  rw [hleft, hright]
  change (∫ y : ClosedInterval (-1 : ℝ) 1,
      cosKernelContinuous 0 (x, y) * f y ∂volume) =
    ((∫ y : ClosedInterval (-1 : ℝ) 1, f y ∂volume) / Real.pi) *
      (bandClass (fun _ : ℝ => 1) continuous_const :
        ClosedInterval (-1 : ℝ) 1 → ℝ) x
  rw [hone, mul_one]
  calc
    (∫ y : ClosedInterval (-1 : ℝ) 1,
        cosKernelContinuous 0 (x, y) * f y ∂volume) =
        ∫ y : ClosedInterval (-1 : ℝ) 1, (1 / Real.pi) * f y ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp [cosKernelContinuous]
    _ = (1 / Real.pi) * ∫ y : ClosedInterval (-1 : ℝ) 1, f y ∂volume := by
      rw [integral_const_mul]
    _ = (∫ y : ClosedInterval (-1 : ℝ) 1, f y ∂volume) / Real.pi := by ring

/-- Pairing against the constant class is literal integration over the aperture. -/
theorem inner_constantBandClass_eq_integral (f : RealIntervalL2 (-1 : ℝ) 1) :
    (inner ℝ constantBandClass f : ℝ) =
      ∫ y : ClosedInterval (-1 : ℝ) 1, f y ∂volume := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_bandClass (fun _ : ℝ => 1) continuous_const] with x hx
  rw [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  change f x * (constantBandClass : ClosedInterval (-1 : ℝ) 1 → ℝ) x = f x
  change f x * (bandClass (fun _ : ℝ => 1) continuous_const :
    ClosedInterval (-1 : ℝ) 1 → ℝ) x = f x
  rw [hx]
  ring

/-- The constant class has squared norm equal to the aperture length `2`. -/
theorem norm_sq_constantBandClass : ‖constantBandClass‖ ^ 2 = 2 := by
  change ‖bandClass (fun _ : ℝ => 1) continuous_const‖ ^ 2 = 2
  rw [norm_sq_bandClass]
  norm_num

/-- Exact rank-one identification of the zero-aperture derivative. -/
theorem cosOperatorL2_zero_eq_rankOne :
    cosOperatorL2 0 =
      (1 / Real.pi) •
        InnerProductSpace.rankOne ℝ constantBandClass constantBandClass := by
  apply ContinuousLinearMap.ext
  intro f
  rw [smul_apply, InnerProductSpace.rankOne_apply, inner_constantBandClass_eq_integral]
  calc
    cosOperatorL2 0 f =
        ((∫ y : ClosedInterval (-1 : ℝ) 1, f y ∂volume) / Real.pi) •
          constantBandClass := cosOperatorL2_zero_apply f
    _ = ((1 / Real.pi) *
        (∫ y : ClosedInterval (-1 : ℝ) 1, f y ∂volume)) • constantBandClass := by
      congr 1
      ring
    _ = (1 / Real.pi) •
        ((∫ y : ClosedInterval (-1 : ℝ) 1, f y ∂volume) • constantBandClass) := by
      rw [smul_smul]

/-- The rank-one tangent acts on the constant line by its unique nonzero eigenvalue `2/π`. -/
theorem cosOperatorL2_zero_constantBandClass :
    cosOperatorL2 0 constantBandClass = (2 / Real.pi) • constantBandClass := by
  rw [cosOperatorL2_zero_eq_rankOne, smul_apply, InnerProductSpace.rankOne_apply,
    real_inner_self_eq_norm_sq, norm_sq_constantBandClass, smul_smul]
  congr 1
  ring

/-- Every zero-aperture tangent value lies on the constant line. -/
theorem cosOperatorL2_zero_mem_span (f : RealIntervalL2 (-1 : ℝ) 1) :
    cosOperatorL2 0 f ∈ ℝ ∙ constantBandClass := by
  rw [cosOperatorL2_zero_apply]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- The zero-aperture tangent has rank at most one. -/
theorem hasRankLE_cosOperatorL2_zero :
    Module.finrank ℝ (LinearMap.range (cosOperatorL2 0).toLinearMap) ≤ 1 := by
  have hrange : LinearMap.range (cosOperatorL2 0).toLinearMap ≤
      ℝ ∙ constantBandClass := by
    rintro _ ⟨f, rfl⟩
    exact cosOperatorL2_zero_mem_span f
  have hconst : constantBandClass ≠ 0 := by
    intro hzero
    have hnorm := norm_sq_constantBandClass
    rw [hzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hnorm
    norm_num at hnorm
  simpa [finrank_span_singleton hconst] using Submodule.finrank_mono hrange

end GaloisForLFunctions.RHTower

end
