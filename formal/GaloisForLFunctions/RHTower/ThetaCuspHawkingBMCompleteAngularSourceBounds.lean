import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompleteAngularSourceContinuity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceGreenProfileBounds
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceContinuationCorridor

/-! Bounds for every original channel of the complete projected source on the physical response overlap. -/
open Complex Set Filter MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMModularCore D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- All three original principal chambers contain the physical weighted-response overlap. -/
theorem principalChamber_of_three_halves (q : XiZeroCopy) (w : ℂ) (hw : 3/2 < w.re) :
    PrincipalChamber q w := fun i => (principalFrequency_abs_im_lt_three_halves q i).trans hw

/-- The original reduced forcing has a uniform negative-ray bound in the positive-frequency chamber. -/
theorem reducedCoefficient_bounded (s w a T : ℂ) (hw : 0 < w.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t < 0 → ‖reducedCoefficient s w a T t‖ ≤ C := by
  have hc : ContinuousOn (fun u : ℝ => reducedPolynomial s w (u:ℂ)) (Icc 0 1) := by
    unfold reducedPolynomial liftSecondPolynomial amplitudeRate
    fun_prop
  obtain ⟨C,hC,hb⟩ := sourceAmplitude_profile_norm_le_exp s w a T _ hc
  refine ⟨C,hC,fun t ht => (hb t ht).trans ?_⟩
  exact mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonneg_of_nonpos hw.le ht.le))

/-- The continued principal response is bounded by its original Green representative on the actual overlap. -/
theorem continuedPrincipalDifference_bounded (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 3/2 < w.re) (hwi : w.im ≠ 0) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t < 0 → ‖continuedPrincipalDifference q branch w a i t‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := principalDifference_bounded q branch w a
    (onsetTransform (2*physicalRate q branch) w) (principalChamber_of_three_halves q w hw) i
  have hs := currentRate_re_lt q branch
  change (2*physicalRate q branch).re < -2 at hs
  refine ⟨C,hC,fun t ht => ?_⟩
  rw [continuedPrincipalDifference_eq_original q branch w a hwi (by linarith) (by linarith) i t ht]
  exact hb t ht

/-- Each complete cutoff coefficient inherits its bound with the original radial geometric weight retained. -/
theorem continuedCutoffRadialCoefficient_bounded (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 3/2 < w.re) (hwi : w.im ≠ 0) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t < 0 → ‖continuedCutoffRadialCoefficient q branch w a i t‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := continuedPrincipalDifference_bounded q branch w a hw hwi i
  refine ⟨C,hC,fun t ht => ?_⟩
  have hz := horizonCoordinate_interior t ht
  have hn : ‖(horizonCoordinate t:ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_of_nonneg hz.1.le]
    exact hz.2.le
  rw [continuedCutoffRadialCoefficient,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hn).trans (hb t ht)

/-- The literal full angular integral is uniformly bounded, with the residual and all three cutoff channels included. -/
theorem continuedAngularSourceProjection_bounded (q : XiZeroCopy) (branch : Bool) (u a w : ℂ)
    (hw : 3/2 < w.re) (hwi : w.im ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t < 0 → ‖continuedAngularSourceProjection q branch u a w t‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := reducedCoefficient_bounded (physicalRate q branch) w a
    (continuedOnset (physicalRate q branch) w) (by linarith)
  choose D hD hd using continuedCutoffRadialCoefficient_bounded q branch w a hw hwi
  refine ⟨C*‖scalarResidualPeriod q u‖+∑ i : Fin 3, D i*‖scalarCutoffPeriod u (principalExponent q i)‖,
    add_nonneg (mul_nonneg hC (norm_nonneg _)) (Finset.sum_nonneg (fun i _ => mul_nonneg (hD i) (norm_nonneg _))),
    fun t ht => ?_⟩
  rw [continuedAngularSourceProjection_eq]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg _)
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hd i t ht) (norm_nonneg _)

end
end RHTower.D4BMJointSource
