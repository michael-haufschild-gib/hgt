import GaloisForLFunctions.RHTower.HedenmalmWardGreenRemovableExtensionKernelProjection

open Complex Filter Topology

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Source-only Abel weight built from Ward mass and Euclidean Ward energy. -/
def thetaXiWardKernelAbelWeight (n : ℕ) (q : XiZeroCopy) : ℝ :=
  2 * thetaXiWardRealificationMass q ^ (2 : ℕ) /
    (2 * thetaXiWardRealificationMass q ^ (2 : ℕ) +
      n * thetaXiWardEuclideanEnergy q)

/-- Exact scalar normal form of the source-only Abel weight. -/
theorem thetaXiWardKernelAbelWeight_eq (n : ℕ) (q : XiZeroCopy) :
    thetaXiWardKernelAbelWeight n q =
      (1 + (n : ℝ) * (xiSpectralPoint q).im ^ (2 : ℕ))⁻¹ := by
  rw [thetaXiWardKernelAbelWeight,
    thetaXiWardEuclideanEnergy_eq_transverse_sq_mul_mass_sq]
  have hm : thetaXiWardRealificationMass q ≠ 0 :=
    (thetaXiWardRealificationMass_pos q).ne'
  have hden : 0 < 1 + (n : ℝ) * (xiSpectralPoint q).im ^ (2 : ℕ) := by
    positivity
  field_simp [hm, hden.ne']

theorem thetaXiWardKernelAbelWeight_nonneg (n : ℕ) (q : XiZeroCopy) :
    0 ≤ thetaXiWardKernelAbelWeight n q := by
  rw [thetaXiWardKernelAbelWeight_eq]
  positivity

theorem thetaXiWardKernelAbelWeight_le_one (n : ℕ) (q : XiZeroCopy) :
    thetaXiWardKernelAbelWeight n q ≤ 1 := by
  rw [thetaXiWardKernelAbelWeight_eq]
  apply inv_le_one_of_one_le₀
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [hn, sq_nonneg (xiSpectralPoint q).im]

/-- Pointwise source recovery of the critical-line indicator. -/
theorem tendsto_thetaXiWardKernelAbelWeight (q : XiZeroCopy) :
    Tendsto (fun n : ℕ => thetaXiWardKernelAbelWeight n q) atTop
      (𝓝 (if (q.1 : ℂ).re = 1 / 2 then 1 else 0)) := by
  simp_rw [thetaXiWardKernelAbelWeight_eq]
  by_cases hq : (q.1 : ℂ).re = 1 / 2
  · have him : (xiSpectralPoint q).im = 0 := by
      rw [xiSpectralPoint_im_eq, hq]
      ring
    simp [hq, him]
  · have him : (xiSpectralPoint q).im ≠ 0 := by
      rw [xiSpectralPoint_im_eq]
      intro him
      apply hq
      linarith
    rw [if_neg hq]
    have himsq : 0 < (xiSpectralPoint q).im ^ (2 : ℕ) := sq_pos_of_ne_zero him
    have htop : Tendsto
        (fun n : ℕ => 1 + (n : ℝ) * (xiSpectralPoint q).im ^ (2 : ℕ))
        atTop atTop := by
      have hmul := tendsto_natCast_atTop_atTop.atTop_mul_const himsq
      simpa [add_comm] using hmul.atTop_add
        (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ)))
    convert htop.inv_tendsto_atTop using 1 <;> rfl

def thetaXiWardKernelAbelCriticalFeatureCurrent
    (n : ℕ) (t : ℝ) (q : XiZeroCopy) : ℝ :=
  thetaXiWardKernelAbelWeight n q *
    Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q))

theorem thetaXiWardKernelAbelCriticalFeatureCurrent_nonneg
    (n : ℕ) (t : ℝ) (q : XiZeroCopy) :
    0 ≤ thetaXiWardKernelAbelCriticalFeatureCurrent n t q := by
  exact mul_nonneg (thetaXiWardKernelAbelWeight_nonneg n q)
    (Complex.normSq_nonneg _)

theorem thetaXiWardKernelAbelCriticalFeatureCurrent_le
    (n : ℕ) (t : ℝ) (q : XiZeroCopy) :
    thetaXiWardKernelAbelCriticalFeatureCurrent n t q ≤
      Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)) := by
  rw [thetaXiWardKernelAbelCriticalFeatureCurrent]
  exact mul_le_of_le_one_left (Complex.normSq_nonneg _)
    (thetaXiWardKernelAbelWeight_le_one n q)

theorem thetaXiWardKernelAbelCriticalFeatureCurrent_summable
    (n : ℕ) (t : ℝ) :
    Summable (thetaXiWardKernelAbelCriticalFeatureCurrent n t) := by
  exact Summable.of_nonneg_of_le
    (thetaXiWardKernelAbelCriticalFeatureCurrent_nonneg n t)
    (thetaXiWardKernelAbelCriticalFeatureCurrent_le n t)
    (criticalFeatureHermitianEnergy_summable t)

def thetaXiWardKernelAbelCriticalFeatureTrace (n : ℕ) (t : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, thetaXiWardKernelAbelCriticalFeatureCurrent n t q

theorem tendsto_thetaXiWardKernelAbelCriticalFeatureCurrent
    (t : ℝ) (q : XiZeroCopy) :
    Tendsto
      (fun n : ℕ => thetaXiWardKernelAbelCriticalFeatureCurrent n t q)
      atTop (𝓝 (criticalLineCriticalFeatureEnergy t q)) := by
  have h := (tendsto_thetaXiWardKernelAbelWeight q).mul_const
    (Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)))
  simpa [thetaXiWardKernelAbelCriticalFeatureCurrent,
    criticalLineCriticalFeatureEnergy] using h

/-- Exact trace-level recovery of the critical-line projection from regular source weights. -/
theorem tendsto_thetaXiWardKernelAbelCriticalFeatureTrace (t : ℝ) :
    Tendsto (fun n : ℕ => thetaXiWardKernelAbelCriticalFeatureTrace n t)
      atTop (𝓝 (criticalLineCriticalFeatureEnergyTrace t)) := by
  unfold thetaXiWardKernelAbelCriticalFeatureTrace
  rw [criticalLineCriticalFeatureEnergyTrace]
  apply tendsto_tsum_of_dominated_convergence
    (criticalFeatureHermitianEnergy_summable t)
  · exact tendsto_thetaXiWardKernelAbelCriticalFeatureCurrent t
  · filter_upwards [] with n q
    rw [Real.norm_eq_abs,
      abs_of_nonneg (thetaXiWardKernelAbelCriticalFeatureCurrent_nonneg n t q)]
    exact thetaXiWardKernelAbelCriticalFeatureCurrent_le n t q

/-- P-G152's missing projection trace is the boundary value of regular source Abel traces. -/
theorem tendsto_fiveShiftWardGreenKernelProjectionAbelTrace (t : ℝ) :
    Tendsto
      (fun n : ℕ => fiveShiftWardGreenKernelJump *
        thetaXiWardKernelAbelCriticalFeatureTrace n t)
      atTop (𝓝 (fiveShiftWardGreenKernelProjectionTrace t)) := by
  have h := (tendsto_thetaXiWardKernelAbelCriticalFeatureTrace t).const_mul
    fiveShiftWardGreenKernelJump
  rw [fiveShiftWardGreenKernelProjectionTrace_eq_jump_mul_lineEnergy]
  exact h

/-- The totalized Ward trace is the boundary value of extension minus source Abel projection. -/
theorem tendsto_fiveShiftCriticalFeatureWardGreenTrace_via_sourceAbel (t : ℝ) :
    Tendsto
      (fun n : ℕ => fiveShiftWardGreenRemovableCriticalFeatureTrace t -
        fiveShiftWardGreenKernelJump *
          thetaXiWardKernelAbelCriticalFeatureTrace n t)
      atTop (𝓝 (fiveShiftCriticalFeatureWardGreenTrace t)) := by
  have hconst : Tendsto
      (fun _ : ℕ => fiveShiftWardGreenRemovableCriticalFeatureTrace t)
      atTop (𝓝 (fiveShiftWardGreenRemovableCriticalFeatureTrace t)) :=
    tendsto_const_nhds
  have h := hconst.sub
    (tendsto_fiveShiftWardGreenKernelProjectionAbelTrace t)
  rw [fiveShiftCriticalFeatureWardGreenTrace_eq_removable_sub_kernelProjection]
  exact h

end

end RHTower
