import GaloisForLFunctions.RHTower.CCM.CCMCoherentExteriorSupportGauge

/-!
# Exact tradeoff for outward-moving moment cancellation

The first frequency moment can be cancelled by exterior corrections tending
to zero in the physical Hilbert norm. Their cubic Taylor budget grows at the
reciprocal rate. An exact product identity records the tradeoff; small field
cost alone does not give a uniform spectral remainder bound.
-/

noncomputable section
open Complex MeasureTheory Filter Topology
open scoped InnerProduct

namespace RHTower

def ccmMidpointExteriorFrequencyAt (a : SuzukiPositiveAperture) (r : ℝ) (n : ℕ) : ℝ :=
  2*Real.pi*(ccmMidpointExteriorShiftAt a r n+r/2)

theorem ccmMidpointExteriorFrequencyAt_eq (a : SuzukiPositiveAperture) (r : ℝ) (n : ℕ) :
    ccmMidpointExteriorFrequencyAt a r n = ccmMidpointExteriorFrequency a r+2*Real.pi*n := by
  unfold ccmMidpointExteriorFrequencyAt ccmMidpointExteriorFrequency ccmMidpointExteriorShiftAt
  ring

theorem ccmMidpointExteriorFrequencyAt_pos (a : SuzukiPositiveAperture) (r : ℝ) (n : ℕ) :
    0 < ccmMidpointExteriorFrequencyAt a r n := by
  rw [ccmMidpointExteriorFrequencyAt_eq]
  exact add_pos_of_pos_of_nonneg (ccmMidpointExteriorFrequency_pos a r) (by positivity)

theorem tendsto_ccmMidpointExteriorFrequencyAt (a : SuzukiPositiveAperture) (r : ℝ) :
    Tendsto (ccmMidpointExteriorFrequencyAt a r) atTop atTop := by
  change Tendsto (fun n : ℕ => ccmMidpointExteriorFrequencyAt a r n) atTop atTop
  simp_rw [ccmMidpointExteriorFrequencyAt_eq]
  exact tendsto_atTop_add_const_left _ _
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by positivity : 0 < 2*Real.pi))

def ccmActualHeadMomentCorrectionAt (a : SuzukiPositiveAperture) (N : ℕ)
    (f : SoninL2) (r : ℝ) (n : ℕ) : SoninL2 :=
  ((ccmActualHeadMidpointSignedMoment (2*a.1) N r/ccmMidpointExteriorFrequencyAt a r n : ℝ) : ℂ) •
    ccmMidpointExteriorOddFieldAt a f r n

def ccmActualHeadMomentCancelledFieldAt (a : SuzukiPositiveAperture) (N : ℕ)
    (f : SoninL2) (r : ℝ) (n : ℕ) : SoninL2 :=
  ccmActualHeadMidpointOddField (2*a.1) N f r-ccmActualHeadMomentCorrectionAt a N f r n

def ccmActualHeadMomentCancelledSineAt (a : SuzukiPositiveAperture) (N : ℕ)
    (r : ℝ) (n : ℕ) (ξ : ℝ) : ℝ :=
  ccmActualHeadMidpointSineSymbol (2*a.1) N r ξ -
    (ccmActualHeadMidpointSignedMoment (2*a.1) N r/ccmMidpointExteriorFrequencyAt a r n)*
      Real.sin (ccmMidpointExteriorFrequencyAt a r n*ξ)

def ccmActualHeadMomentCancelledCubicBudgetAt (a : SuzukiPositiveAperture) (N : ℕ)
    (r : ℝ) (n : ℕ) : ℝ :=
  ccmActualHeadMidpointCubicMoment (2*a.1) N r +
    |ccmActualHeadMidpointSignedMoment (2*a.1) N r| * (ccmMidpointExteriorFrequencyAt a r n)^2

/-- Every correction is wholly invisible to physical support. -/
theorem ccmIncrementSupportProjection_momentCorrectionAt_zero
    (a : SuzukiPositiveAperture) (N : ℕ) (f : suzukiApertureHilbert a) (r : ℝ) (n : ℕ) :
    ccmIncrementSupportProjection a r (ccmActualHeadMomentCorrectionAt a N f.1 r n) = 0 := by
  rw [ccmActualHeadMomentCorrectionAt, map_smul, ccmIncrementSupportProjection_exteriorOddAt_zero,
    smul_zero]

theorem ccmGammaIncrementAction_momentCancelledFieldAt
    (a : SuzukiPositiveAperture) (N : ℕ) (f : suzukiApertureHilbert a) (r : ℝ) (n : ℕ) :
    ccmGammaIncrementAction f.1 r (ccmActualHeadMomentCancelledFieldAt a N f.1 r n) =
      ccmGammaIncrementAction f.1 r (ccmActualHeadMidpointOddField (2*a.1) N f.1 r) := by
  apply (ccmGammaIncrementAction_eq_iff_current_eq _ _ _ _).mpr
  rw [ccmActualHeadMomentCancelledFieldAt, inner_sub_right, ccmActualHeadMomentCorrectionAt,
    inner_smul_right, inner_increment_exteriorOddAt_zero, mul_zero, sub_zero]

theorem norm_ccmActualHeadMomentCorrectionAt_le (a : SuzukiPositiveAperture) (N : ℕ)
    (f : SoninL2) (r : ℝ) (n : ℕ) :
    ‖ccmActualHeadMomentCorrectionAt a N f r n‖ ≤
      |ccmActualHeadMidpointSignedMoment (2*a.1) N r/ccmMidpointExteriorFrequencyAt a r n| * ‖f‖ := by
  rw [ccmActualHeadMomentCorrectionAt, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_ccmMidpointExteriorOddFieldAt_le a f r n) (abs_nonneg _)

/-- Exact current preservation is compatible with corrections arbitrarily small in `L²`. -/
theorem tendsto_ccmActualHeadMomentCorrectionAt_zero (a : SuzukiPositiveAperture) (N : ℕ)
    (f : SoninL2) (r : ℝ) :
    Tendsto (fun n => ccmActualHeadMomentCorrectionAt a N f r n) atTop (𝓝 0) := by
  have hc : Tendsto (fun n => ccmActualHeadMidpointSignedMoment (2*a.1) N r /
      ccmMidpointExteriorFrequencyAt a r n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_ccmMidpointExteriorFrequencyAt a r)
  have hb : Tendsto (fun n =>
      |ccmActualHeadMidpointSignedMoment (2*a.1) N r/ccmMidpointExteriorFrequencyAt a r n| * ‖f‖)
      atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, norm_zero, zero_mul] using hc.norm.mul_const ‖f‖
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => norm_ccmActualHeadMomentCorrectionAt_le a N f r n) hb

theorem tendsto_ccmActualHeadMomentCancelledFieldAt (a : SuzukiPositiveAperture) (N : ℕ)
    (f : SoninL2) (r : ℝ) :
    Tendsto (fun n => ccmActualHeadMomentCancelledFieldAt a N f r n) atTop
      (𝓝 (ccmActualHeadMidpointOddField (2*a.1) N f r)) := by
  have h : Tendsto (fun n => ccmActualHeadMidpointOddField (2*a.1) N f r -
      ccmActualHeadMomentCorrectionAt a N f r n) atTop
      (𝓝 (ccmActualHeadMidpointOddField (2*a.1) N f r-0)) :=
    tendsto_const_nhds.sub (tendsto_ccmActualHeadMomentCorrectionAt_zero a N f r)
  simpa only [ccmActualHeadMomentCancelledFieldAt, sub_zero] using h

/-- The exact squared norm of a correction is the inverse-square frequency cost. -/
theorem norm_sq_ccmActualHeadMomentCorrectionAt (a : SuzukiPositiveAperture) (N : ℕ)
    (f : suzukiApertureHilbert a) (r : ℝ) (n : ℕ) :
    ‖ccmActualHeadMomentCorrectionAt a N f.1 r n‖^2 =
      (ccmActualHeadMidpointSignedMoment (2*a.1) N r/ccmMidpointExteriorFrequencyAt a r n)^2 *
        (‖f.1‖^2/2) := by
  rw [ccmActualHeadMomentCorrectionAt, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs, norm_sq_ccmMidpointExteriorOddFieldAt]

/-- Moving the null gauge outward conserves the product of field cost and added cubic budget. -/
theorem ccmActualHeadMomentCorrectionAt_energy_budget_product
    (a : SuzukiPositiveAperture) (N : ℕ) (f : suzukiApertureHilbert a) (r : ℝ) (n : ℕ) :
    ‖ccmActualHeadMomentCorrectionAt a N f.1 r n‖^2 *
      (ccmActualHeadMomentCancelledCubicBudgetAt a N r n-ccmActualHeadMidpointCubicMoment (2*a.1) N r) =
      |ccmActualHeadMidpointSignedMoment (2*a.1) N r|^3 * ‖f.1‖^2/2 := by
  rw [norm_sq_ccmActualHeadMomentCorrectionAt, ccmActualHeadMomentCancelledCubicBudgetAt,
    add_sub_cancel_left, div_pow]
  have hβ := ne_of_gt (ccmMidpointExteriorFrequencyAt_pos a r n)
  field_simp [hβ]
  rw [← sq_abs (ccmActualHeadMidpointSignedMoment (2*a.1) N r)]
  ring

end RHTower
