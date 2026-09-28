import GaloisForLFunctions.RHTower.CCMExponentialRampGammaCapacity

/-!
# Signed energy control of the actual critical deficit

The two exponential-ramp fields have finite reciprocal-Gamma energy at every
literal cutoff. Completing two reciprocal weighted squares bounds their
signed action by a fixed capacity, at most five. The resulting estimate applies
directly to the square-root-normalized Chebyshev deficit. Uniform arithmetic
energy control is not assumed or claimed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators

namespace RHTower

theorem memLp_ccmOutgoingQuantileCellDensity_continuousTest (n : ℕ) (F : C(ℝ, ℝ)) :
    MemLp (fun r => ccmOutgoingQuantileDisplacementCellDensity n r*F r) 2 := by
  apply (memLp_two_iff_integrable_sq
    ((measurable_ccmOutgoingQuantileDisplacementCellDensity n).mul F.continuous.measurable).aestronglyMeasurable).mpr
  have h := integrable_ccmOutgoingQuantileCellDensity_continuousTest n
    ⟨fun r => Real.exp ((r+Real.log n)/2)*(F r)^2, by fun_prop⟩
  refine h.congr (Eventually.of_forall fun r => ?_)
  change ccmOutgoingQuantileDisplacementCellDensity n r*(Real.exp ((r+Real.log n)/2)*(F r)^2) = _
  by_cases hr : r ∈ Ioc (ccmOutgoingPrimeQuantileBoundary n-Real.log n)
      (ccmOutgoingPrimeQuantileBoundary (n+1)-Real.log n) <;>
    simp [ccmOutgoingQuantileDisplacementCellDensity, hr]
  ring

theorem memLp_ccmActualHeadQuantileTerminalDensity_continuousTest
    (T : ℝ) (N : ℕ) (F : C(ℝ, ℝ)) :
    MemLp (fun r => ccmActualHeadQuantileTerminalDisplacementDensity T N r*F r) 2 := by
  apply (memLp_two_iff_integrable_sq
    ((measurable_ccmActualHeadQuantileTerminalDisplacementDensity T N).mul
      F.continuous.measurable).aestronglyMeasurable).mpr
  have h := (integrable_ccmActualHeadQuantileTerminalDensity_continuousTest T N
    ⟨fun r => Real.exp ((r+T)/2)*(F r)^2, by fun_prop⟩).abs
  refine h.congr (Eventually.of_forall fun r => ?_)
  change |ccmActualHeadQuantileTerminalDisplacementDensity T N r*(Real.exp ((r+T)/2)*(F r)^2)| = _
  by_cases hb : ccmOutgoingPrimeQuantileBoundary N ≤ T
  · by_cases hr : r ∈ Ioc (ccmOutgoingPrimeQuantileBoundary N-T) 0 <;>
      simp [ccmActualHeadQuantileTerminalDisplacementDensity, hb, hr, abs_mul,
        abs_of_pos (Real.exp_pos _), mul_pow]
    ring
  · by_cases hr : r ∈ Ioc 0 (ccmOutgoingPrimeQuantileBoundary N-T) <;>
      simp [ccmActualHeadQuantileTerminalDisplacementDensity, hb, hr, abs_mul,
        abs_of_pos (Real.exp_pos _), mul_pow]
    ring

theorem memLp_ccmExponentialRampPosition_mul_sqrtDual (T : ℝ) (N : ℕ) :
    MemLp (fun r : ℝ => ccmActualHeadExponentialRampPositionField T N r*
      Real.sqrt (ccmGammaHigherBinetDualDensity |r|)) 2 := by
  have h := memLp_finsetSum (Finset.range N) (fun n _ =>
    memLp_ccmOutgoingQuantileCellDensity_continuousTest n
      ⟨fun r => Real.exp ((Real.log n-T)/2)*(T-Real.log n)*
        Real.sqrt (ccmGammaHigherBinetDualDensity |r|), by
          unfold ccmGammaHigherBinetDualDensity
          fun_prop⟩)
  refine h.ae_eq (Eventually.of_forall fun r => ?_)
  change (∑ n ∈ Finset.range N, ccmOutgoingQuantileDisplacementCellDensity n r *
      (Real.exp ((Real.log n-T)/2)*(T-Real.log n)*Real.sqrt (ccmGammaHigherBinetDualDensity |r|))) =
    (∑ n ∈ Finset.range N, ccmOutgoingQuantileDisplacementCellDensity n r *
      Real.exp ((Real.log n-T)/2)*(T-Real.log n))*Real.sqrt (ccmGammaHigherBinetDualDensity |r|)
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem memLp_ccmExponentialRampMass_mul_sqrtDual (T : ℝ) (N : ℕ) :
    MemLp (fun r : ℝ => ccmActualHeadExponentialRampMassField T N r*
      Real.sqrt (ccmGammaHigherBinetDualDensity |r|)) 2 := by
  have h := memLp_finsetSum (Finset.range N) (fun n _ =>
    memLp_ccmOutgoingQuantileCellDensity_continuousTest n
      ⟨fun r => Real.exp ((Real.log n-T)/2)*Real.sqrt (ccmGammaHigherBinetDualDensity |r|), by
        unfold ccmGammaHigherBinetDualDensity
        fun_prop⟩)
  have ht := memLp_ccmActualHeadQuantileTerminalDensity_continuousTest T N
    ⟨fun r => Real.sqrt (ccmGammaHigherBinetDualDensity |r|), by
      unfold ccmGammaHigherBinetDualDensity
      fun_prop⟩
  refine (h.add ht).ae_eq (Eventually.of_forall fun r => ?_)
  simp only [Pi.add_apply, ccmActualHeadExponentialRampMassField, add_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  change ccmOutgoingQuantileDisplacementCellDensity n r *
      (Real.exp ((Real.log n-T)/2)*Real.sqrt (ccmGammaHigherBinetDualDensity |r|)) =
    ccmOutgoingQuantileDisplacementCellDensity n r *
      Real.exp ((Real.log n-T)/2)*Real.sqrt (ccmGammaHigherBinetDualDensity |r|)
  ring

def ccmExponentialRampArithmeticEnergyDensity (T : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  ((ccmActualHeadExponentialRampPositionField T N r)^2+
    (ccmActualHeadExponentialRampMassField T N r)^2)*ccmGammaHigherBinetDualDensity |r|

theorem integrable_ccmExponentialRampArithmeticEnergyDensity (T : ℝ) (N : ℕ) :
    Integrable (ccmExponentialRampArithmeticEnergyDensity T N) := by
  have hA := (memLp_ccmExponentialRampPosition_mul_sqrtDual T N).integrable_sq
  have hB := (memLp_ccmExponentialRampMass_mul_sqrtDual T N).integrable_sq
  refine (hA.add hB).congr (Eventually.of_forall fun r => ?_)
  simp only [Pi.add_apply, mul_pow, Real.sq_sqrt (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)),
    ccmExponentialRampArithmeticEnergyDensity]
  ring

def ccmExponentialRampArithmeticEnergy (T : ℝ) (N : ℕ) : ℝ :=
  ∫ r : ℝ, ccmExponentialRampArithmeticEnergyDensity T N r

theorem ccmExponentialRampArithmeticEnergy_nonneg (T : ℝ) (N : ℕ) :
    0 ≤ ccmExponentialRampArithmeticEnergy T N :=
  integral_nonneg fun r => mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))

theorem ccmExponentialRampWeightedSquare (r x y t : ℝ) :
    (x*Real.sqrt (ccmGammaHigherBinetDualDensity |r|)-
      t*ccmExponentialRampDisplacementWeight r*Real.sqrt (ccmGammaHigherBinetModeDensity |r|))^2 +
    (y*Real.sqrt (ccmGammaHigherBinetDualDensity |r|)-
      t*ccmExponentialRampDerivativeWeight r*Real.sqrt (ccmGammaHigherBinetModeDensity |r|))^2 =
      (x^2+y^2)*ccmGammaHigherBinetDualDensity |r| -
        2*t*(ccmExponentialRampDisplacementWeight r*x+ccmExponentialRampDerivativeWeight r*y) +
          t^2*ccmExponentialRampGammaCapacityDensity r := by
  by_cases hr : r = 0
  · simp [hr, ccmGammaHigherBinetDualDensity, ccmGammaHigherBinetModeDensity,
      ccmExponentialRampDisplacementWeight, ccmExponentialRampDerivativeWeight,
      ccmExponentialRampGammaCapacityDensity]
  · have hk := ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)
    have hg := ccmGammaHigherBinetModeDensity_abs_nonneg r
    have hs : Real.sqrt (ccmGammaHigherBinetDualDensity |r|)*
        Real.sqrt (ccmGammaHigherBinetModeDensity |r|) = 1 := by
      rw [← Real.sqrt_mul hk, mul_comm, ccmGammaHigherBinetModeDensity_mul_dual (abs_pos.mpr hr),
        Real.sqrt_one]
    calc
      _ = (x^2+y^2)*(Real.sqrt (ccmGammaHigherBinetDualDensity |r|))^2 -
          2*t*(ccmExponentialRampDisplacementWeight r*x+ccmExponentialRampDerivativeWeight r*y)*
            (Real.sqrt (ccmGammaHigherBinetDualDensity |r|)*Real.sqrt (ccmGammaHigherBinetModeDensity |r|)) +
          t^2*((ccmExponentialRampDisplacementWeight r)^2+(ccmExponentialRampDerivativeWeight r)^2)*
            (Real.sqrt (ccmGammaHigherBinetModeDensity |r|))^2 := by ring
      _ = _ := by
        rw [Real.sq_sqrt hk, Real.sq_sqrt hg, hs]
        unfold ccmExponentialRampGammaCapacityDensity
        ring

theorem ccmExponentialRampAction_dual_bound (T : ℝ) (N : ℕ) (t : ℝ) :
    2*t*ccmActualHeadQuantileTestAction T N (ccmNormalizedExponentialRampTest T) ≤
      ccmExponentialRampArithmeticEnergy T N+t^2*ccmExponentialRampGammaCapacity := by
  have hp (r : ℝ) : 2*t*ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T) r ≤
      ccmExponentialRampArithmeticEnergyDensity T N r+t^2*ccmExponentialRampGammaCapacityDensity r := by
    have h := add_nonneg
      (sq_nonneg (ccmActualHeadExponentialRampPositionField T N r*Real.sqrt (ccmGammaHigherBinetDualDensity |r|)-
        t*ccmExponentialRampDisplacementWeight r*Real.sqrt (ccmGammaHigherBinetModeDensity |r|)))
      (sq_nonneg (ccmActualHeadExponentialRampMassField T N r*Real.sqrt (ccmGammaHigherBinetDualDensity |r|)-
        t*ccmExponentialRampDerivativeWeight r*Real.sqrt (ccmGammaHigherBinetModeDensity |r|)))
    rw [ccmExponentialRampWeightedSquare] at h
    rw [ccmActualHeadExponentialRampCurrent_eq_two_fields]
    unfold ccmExponentialRampArithmeticEnergyDensity
    linarith only [h]
  have h := integral_mono
    ((integrable_ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T)).const_mul (2*t))
    ((integrable_ccmExponentialRampArithmeticEnergyDensity T N).add
      (integrable_ccmExponentialRampGammaCapacityDensity.const_mul (t^2))) hp
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_ccmExponentialRampArithmeticEnergyDensity T N)
    (integrable_ccmExponentialRampGammaCapacityDensity.const_mul (t^2)),
    integral_const_mul, integral_const_mul] at h
  exact h

theorem sq_ccmExponentialRampAction_le_five_energy (T : ℝ) (N : ℕ) :
    (ccmActualHeadQuantileTestAction T N (ccmNormalizedExponentialRampTest T))^2 ≤
      5*ccmExponentialRampArithmeticEnergy T N := by
  let Q := ccmActualHeadQuantileTestAction T N (ccmNormalizedExponentialRampTest T)
  have h := ccmExponentialRampAction_dual_bound T N (Q/5)
  have hc := mul_le_mul_of_nonneg_left ccmExponentialRampGammaCapacity_le_five (sq_nonneg (Q/5))
  change 2*(Q/5)*Q ≤ ccmExponentialRampArithmeticEnergy T N+(Q/5)^2*ccmExponentialRampGammaCapacity at h
  change Q^2 ≤ 5*ccmExponentialRampArithmeticEnergy T N
  nlinarith only [h, hc]

theorem abs_ccmExponentialRampAction_le_sqrt_energy (T : ℝ) (N : ℕ) :
    |ccmActualHeadQuantileTestAction T N (ccmNormalizedExponentialRampTest T)| ≤
      Real.sqrt (5*ccmExponentialRampArithmeticEnergy T N) := by
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt (mul_nonneg (by norm_num) (ccmExponentialRampArithmeticEnergy_nonneg T N))]
  exact sq_ccmExponentialRampAction_le_five_energy T N

/-- Direct control of the actual RH remainder by literal signed transport energy and a fixed transient. -/
theorem abs_normalized_chebyshevDeficit_le_exponentialRampEnergy (H : NNReal) :
    |Real.exp (-(H : ℝ)/2)*ccmLogChebyshevDeficitPrimitive (H : ℝ)| ≤
      2+Real.sqrt (5*ccmExponentialRampArithmeticEnergy (H : ℝ) (Nat.floor (Real.exp (H : ℝ))+1)) := by
  have he : Real.exp (-(H : ℝ)/2)*ccmLogChebyshevDeficitPrimitive (H : ℝ) =
      (H : ℝ)*Real.exp (-(H : ℝ)/2) +
        ccmActualHeadQuantileTestAction (H : ℝ) (Nat.floor (Real.exp (H : ℝ))+1)
          (ccmNormalizedExponentialRampTest (H : ℝ)) := by
    rw [ccmActualTimeExponentialRampAction_eq_normalizedDeficit]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add (ccmExponentialRampTransient_bound H)
    (abs_ccmExponentialRampAction_le_sqrt_energy (H : ℝ) (Nat.floor (Real.exp (H : ℝ))+1)))

end RHTower
