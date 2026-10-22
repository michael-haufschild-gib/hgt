import GaloisForLFunctions.RHTower.CCM.CCMExponentialRampArithmeticEnergy

/-!
# Removing the current-invisible transport direction

The exponential-ramp current has one exact field symmetry: adding a multiple
of (b,-a) to the position/mass pair preserves a*x+b*y. The canonical projection
removes that direction. Its Gamma energy is the visible squared current, and
the full energy splits into visible and transverse nonnegative energies.
-/

noncomputable section
open MeasureTheory Filter

namespace RHTower

def ccmExponentialRampWeightSquare (r : ℝ) : ℝ :=
  (ccmExponentialRampDisplacementWeight r)^2+(ccmExponentialRampDerivativeWeight r)^2

theorem ccmExponentialRampWeightSquare_nonneg (r : ℝ) : 0 ≤ ccmExponentialRampWeightSquare r :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem weightSquare_pos {r : ℝ} (hr : r ≠ 0) : 0 < ccmExponentialRampWeightSquare r := by
  have hb : ccmExponentialRampDerivativeWeight r ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hr) (Real.exp_ne_zero _)
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hb)

def ccmExponentialRampFieldGauge (r z : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (v.1+z*ccmExponentialRampDerivativeWeight r, v.2-z*ccmExponentialRampDisplacementWeight r)

theorem ccmExponentialRampFieldGauge_zero (r : ℝ) (v : ℝ × ℝ) :
    ccmExponentialRampFieldGauge r 0 v = v := by
  simp [ccmExponentialRampFieldGauge]

theorem ccmExponentialRampFieldGauge_add (r z w : ℝ) (v : ℝ × ℝ) :
    ccmExponentialRampFieldGauge r (z+w) v =
      ccmExponentialRampFieldGauge r z (ccmExponentialRampFieldGauge r w v) := by
  ext <;> simp only [ccmExponentialRampFieldGauge] <;> ring

theorem continuous_ccmExponentialRampFieldGauge (r : ℝ) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => ccmExponentialRampFieldGauge r p.1 p.2) := by
  unfold ccmExponentialRampFieldGauge
  fun_prop

/-- A continuous one-parameter field symmetry with an exactly conserved signed current. -/
theorem ccmExponentialRampCurrent_fieldGauge (r x y z : ℝ) :
    ccmExponentialRampDisplacementWeight r*(x+z*ccmExponentialRampDerivativeWeight r) +
      ccmExponentialRampDerivativeWeight r*(y-z*ccmExponentialRampDisplacementWeight r) =
        ccmExponentialRampDisplacementWeight r*x+ccmExponentialRampDerivativeWeight r*y := by ring

def ccmExponentialRampVisibleEnergyDensity (T : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  ccmGammaHigherBinetDualDensity |r| *
    (ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T) r)^2 /
      ccmExponentialRampWeightSquare r

def ccmExponentialRampTransverseEnergyDensity (T : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  ccmGammaHigherBinetDualDensity |r| *
    (ccmExponentialRampDerivativeWeight r*ccmActualHeadExponentialRampPositionField T N r -
      ccmExponentialRampDisplacementWeight r*ccmActualHeadExponentialRampMassField T N r)^2 /
        ccmExponentialRampWeightSquare r

theorem ccmExponentialRampVisibleEnergyDensity_nonneg (T : ℝ) (N : ℕ) (r : ℝ) :
    0 ≤ ccmExponentialRampVisibleEnergyDensity T N r :=
  div_nonneg (mul_nonneg (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)) (sq_nonneg _))
    (ccmExponentialRampWeightSquare_nonneg r)

theorem ccmExponentialRampTransverseEnergyDensity_nonneg (T : ℝ) (N : ℕ) (r : ℝ) :
    0 ≤ ccmExponentialRampTransverseEnergyDensity T N r :=
  div_nonneg (mul_nonneg (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)) (sq_nonneg _))
    (ccmExponentialRampWeightSquare_nonneg r)

theorem ccmExponentialRampArithmeticEnergyDensity_eq_visible_add_transverse
    (T : ℝ) (N : ℕ) (r : ℝ) :
    ccmExponentialRampArithmeticEnergyDensity T N r =
      ccmExponentialRampVisibleEnergyDensity T N r+ccmExponentialRampTransverseEnergyDensity T N r := by
  by_cases hr : r = 0
  · simp [hr, ccmExponentialRampArithmeticEnergyDensity, ccmExponentialRampVisibleEnergyDensity,
      ccmExponentialRampTransverseEnergyDensity, ccmGammaHigherBinetDualDensity]
  · have hw := ne_of_gt (weightSquare_pos hr)
    unfold ccmExponentialRampArithmeticEnergyDensity ccmExponentialRampVisibleEnergyDensity
      ccmExponentialRampTransverseEnergyDensity
    rw [ccmActualHeadExponentialRampCurrent_eq_two_fields]
    field_simp [hw]
    unfold ccmExponentialRampWeightSquare
    ring

theorem integrable_ccmExponentialRampVisibleEnergyDensity (T : ℝ) (N : ℕ) :
    Integrable (ccmExponentialRampVisibleEnergyDensity T N) := by
  apply Integrable.mono' (integrable_ccmExponentialRampArithmeticEnergyDensity T N)
  · have hJ := (integrable_ccmActualHeadQuantileTestCurrent T N
      (ccmNormalizedExponentialRampTest T)).aestronglyMeasurable
    have hk : Continuous (fun r : ℝ => ccmGammaHigherBinetDualDensity |r|) := by
      unfold ccmGammaHigherBinetDualDensity
      fun_prop
    have hw : Continuous ccmExponentialRampWeightSquare := by
      unfold ccmExponentialRampWeightSquare ccmExponentialRampDisplacementWeight ccmExponentialRampDerivativeWeight
      fun_prop
    exact (hk.aestronglyMeasurable.mul (hJ.pow 2)).div₀ hw.aestronglyMeasurable
  · filter_upwards with r
    rw [Real.norm_eq_abs, abs_of_nonneg (ccmExponentialRampVisibleEnergyDensity_nonneg T N r),
      ccmExponentialRampArithmeticEnergyDensity_eq_visible_add_transverse]
    exact le_add_of_nonneg_right (ccmExponentialRampTransverseEnergyDensity_nonneg T N r)

theorem integrable_ccmExponentialRampTransverseEnergyDensity (T : ℝ) (N : ℕ) :
    Integrable (ccmExponentialRampTransverseEnergyDensity T N) := by
  refine ((integrable_ccmExponentialRampArithmeticEnergyDensity T N).sub
    (integrable_ccmExponentialRampVisibleEnergyDensity T N)).congr (Eventually.of_forall fun r => ?_)
  simp only [Pi.sub_apply, ccmExponentialRampArithmeticEnergyDensity_eq_visible_add_transverse,
    add_sub_cancel_left]

def ccmExponentialRampVisibleEnergy (T : ℝ) (N : ℕ) : ℝ :=
  ∫ r : ℝ, ccmExponentialRampVisibleEnergyDensity T N r

def ccmExponentialRampTransverseEnergy (T : ℝ) (N : ℕ) : ℝ :=
  ∫ r : ℝ, ccmExponentialRampTransverseEnergyDensity T N r

theorem ccmExponentialRampVisibleEnergy_nonneg (T : ℝ) (N : ℕ) :
    0 ≤ ccmExponentialRampVisibleEnergy T N :=
  integral_nonneg (ccmExponentialRampVisibleEnergyDensity_nonneg T N)

theorem ccmExponentialRampArithmeticEnergy_eq_visible_add_transverse (T : ℝ) (N : ℕ) :
    ccmExponentialRampArithmeticEnergy T N =
      ccmExponentialRampVisibleEnergy T N+ccmExponentialRampTransverseEnergy T N := by
  unfold ccmExponentialRampArithmeticEnergy ccmExponentialRampVisibleEnergy ccmExponentialRampTransverseEnergy
  simp_rw [ccmExponentialRampArithmeticEnergyDensity_eq_visible_add_transverse]
  exact integral_add (integrable_ccmExponentialRampVisibleEnergyDensity T N)
    (integrable_ccmExponentialRampTransverseEnergyDensity T N)

theorem ccmExponentialRampVisibleEnergy_le_energy (T : ℝ) (N : ℕ) :
    ccmExponentialRampVisibleEnergy T N ≤ ccmExponentialRampArithmeticEnergy T N := by
  rw [ccmExponentialRampArithmeticEnergy_eq_visible_add_transverse]
  exact le_add_of_nonneg_right (integral_nonneg (ccmExponentialRampTransverseEnergyDensity_nonneg T N))

def ccmExponentialRampProjectedPositionField (T : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  ccmExponentialRampDisplacementWeight r *
    ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T) r / ccmExponentialRampWeightSquare r

def ccmExponentialRampProjectedMassField (T : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  ccmExponentialRampDerivativeWeight r *
    ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T) r / ccmExponentialRampWeightSquare r

theorem ccmExponentialRampProjectedField_preserves_current (T : ℝ) (N : ℕ) (r : ℝ) :
    ccmExponentialRampDisplacementWeight r*ccmExponentialRampProjectedPositionField T N r +
      ccmExponentialRampDerivativeWeight r*ccmExponentialRampProjectedMassField T N r =
        ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T) r := by
  by_cases hr : r = 0
  · simp [hr, ccmExponentialRampDisplacementWeight, ccmExponentialRampDerivativeWeight,
      ccmActualHeadQuantileTestCurrent]
  · unfold ccmExponentialRampProjectedPositionField ccmExponentialRampProjectedMassField
    field_simp [ne_of_gt (weightSquare_pos hr)]
    unfold ccmExponentialRampWeightSquare
    ring

theorem ccmExponentialRampProjectedField_energy (T : ℝ) (N : ℕ) (r : ℝ) :
    ((ccmExponentialRampProjectedPositionField T N r)^2+(ccmExponentialRampProjectedMassField T N r)^2)*
      ccmGammaHigherBinetDualDensity |r| = ccmExponentialRampVisibleEnergyDensity T N r := by
  by_cases hr : r = 0
  · simp [hr, ccmGammaHigherBinetDualDensity, ccmExponentialRampVisibleEnergyDensity]
  · unfold ccmExponentialRampProjectedPositionField ccmExponentialRampProjectedMassField
      ccmExponentialRampVisibleEnergyDensity
    field_simp [ne_of_gt (weightSquare_pos hr)]
    unfold ccmExponentialRampWeightSquare
    ring

theorem ccmExponentialRampAction_visible_dual_bound (T : ℝ) (N : ℕ) (t : ℝ) :
    2*t*ccmActualHeadQuantileTestAction T N (ccmNormalizedExponentialRampTest T) ≤
      ccmExponentialRampVisibleEnergy T N+t^2*ccmExponentialRampGammaCapacity := by
  have hp (r : ℝ) : 2*t*ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T) r ≤
      ccmExponentialRampVisibleEnergyDensity T N r+t^2*ccmExponentialRampGammaCapacityDensity r := by
    have h := add_nonneg
      (sq_nonneg (ccmExponentialRampProjectedPositionField T N r*Real.sqrt (ccmGammaHigherBinetDualDensity |r|)-
        t*ccmExponentialRampDisplacementWeight r*Real.sqrt (ccmGammaHigherBinetModeDensity |r|)))
      (sq_nonneg (ccmExponentialRampProjectedMassField T N r*Real.sqrt (ccmGammaHigherBinetDualDensity |r|)-
        t*ccmExponentialRampDerivativeWeight r*Real.sqrt (ccmGammaHigherBinetModeDensity |r|)))
    rw [ccmExponentialRampWeightedSquare, ccmExponentialRampProjectedField_energy,
      ccmExponentialRampProjectedField_preserves_current] at h
    linarith only [h]
  have h := integral_mono
    ((integrable_ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T)).const_mul (2*t))
    ((integrable_ccmExponentialRampVisibleEnergyDensity T N).add
      (integrable_ccmExponentialRampGammaCapacityDensity.const_mul (t^2))) hp
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_ccmExponentialRampVisibleEnergyDensity T N)
    (integrable_ccmExponentialRampGammaCapacityDensity.const_mul (t^2)),
    integral_const_mul, integral_const_mul] at h
  exact h

theorem sq_ccmExponentialRampAction_le_five_visibleEnergy (T : ℝ) (N : ℕ) :
    (ccmActualHeadQuantileTestAction T N (ccmNormalizedExponentialRampTest T))^2 ≤
      5*ccmExponentialRampVisibleEnergy T N := by
  let Q := ccmActualHeadQuantileTestAction T N (ccmNormalizedExponentialRampTest T)
  have h := ccmExponentialRampAction_visible_dual_bound T N (Q/5)
  have hc := mul_le_mul_of_nonneg_left ccmExponentialRampGammaCapacity_le_five (sq_nonneg (Q/5))
  change 2*(Q/5)*Q ≤ ccmExponentialRampVisibleEnergy T N+(Q/5)^2*ccmExponentialRampGammaCapacity at h
  change Q^2 ≤ 5*ccmExponentialRampVisibleEnergy T N
  nlinarith only [h, hc]

theorem abs_normalized_chebyshevDeficit_le_exponentialRampVisibleEnergy (H : NNReal) :
    |Real.exp (-(H : ℝ)/2)*ccmLogChebyshevDeficitPrimitive (H : ℝ)| ≤
      2+Real.sqrt (5*ccmExponentialRampVisibleEnergy (H : ℝ) (Nat.floor (Real.exp (H : ℝ))+1)) := by
  have hQ : |ccmActualHeadQuantileTestAction (H : ℝ) (Nat.floor (Real.exp (H : ℝ))+1)
      (ccmNormalizedExponentialRampTest (H : ℝ))| ≤
      Real.sqrt (5*ccmExponentialRampVisibleEnergy (H : ℝ) (Nat.floor (Real.exp (H : ℝ))+1)) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt (mul_nonneg (by norm_num) (ccmExponentialRampVisibleEnergy_nonneg _ _))]
    exact sq_ccmExponentialRampAction_le_five_visibleEnergy _ _
  have he : Real.exp (-(H : ℝ)/2)*ccmLogChebyshevDeficitPrimitive (H : ℝ) =
      (H : ℝ)*Real.exp (-(H : ℝ)/2) +
        ccmActualHeadQuantileTestAction (H : ℝ) (Nat.floor (Real.exp (H : ℝ))+1)
          (ccmNormalizedExponentialRampTest (H : ℝ)) := by
    rw [ccmActualTimeExponentialRampAction_eq_normalizedDeficit]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add (ccmExponentialRampTransient_bound H) hQ)

end RHTower
