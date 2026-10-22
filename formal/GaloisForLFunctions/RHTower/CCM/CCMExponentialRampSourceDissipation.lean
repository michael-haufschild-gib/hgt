import GaloisForLFunctions.RHTower.CCM.CCMExponentialRampTerminalEntropy

/-!
# Signed source, dissipation, and age-moment balance

The literal arithmetic action plus nonnegative bulk dissipation and twice the
fixed-head age-moment derivative equals nonnegative terminal entropy. This is
an exact balance for the actual prime cells, not a uniform-bound assumption.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace RHTower

private theorem integrable_bulk_test (T : ℝ) (N : ℕ) (F : C(ℝ, ℝ)) :
    Integrable (fun r => ccmExponentialRampBulkMassField T N r*F r) := by
  have h := integrable_finsetSum (Finset.range N) (fun n _ =>
    (integrable_ccmOutgoingQuantileCellDensity_continuousTest n F).mul_const
      (Real.exp ((Real.log n-T)/2)))
  refine h.congr (Eventually.of_forall fun r => ?_)
  simp only [ccmExponentialRampBulkMassField, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  ring

def ccmExponentialRampBulkDissipationDensity (T : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  -ccmExponentialRampSecondOrderWeight r*ccmExponentialRampBulkMassField T N r

theorem ccmExponentialRampBulkDissipationDensity_nonneg (T : ℝ) (N : ℕ) (r : ℝ) :
    0 ≤ ccmExponentialRampBulkDissipationDensity T N r :=
  mul_nonneg (neg_nonneg.mpr (ccmExponentialRampSecondOrderWeight_nonpos r))
    (ccmExponentialRampBulkMassField_nonneg T N r)

theorem integrable_ccmExponentialRampBulkDissipationDensity (T : ℝ) (N : ℕ) :
    Integrable (ccmExponentialRampBulkDissipationDensity T N) := by
  have h := integrable_bulk_test T N
    ⟨fun r => -ccmExponentialRampSecondOrderWeight r, by
      unfold ccmExponentialRampSecondOrderWeight ccmExponentialRampDisplacementWeight
        ccmExponentialRampDerivativeWeight
      fun_prop⟩
  change Integrable (fun r => -ccmExponentialRampSecondOrderWeight r *
    ccmExponentialRampBulkMassField T N r)
  simpa only [ContinuousMap.coe_mk, mul_comm] using h

def ccmExponentialRampBulkDissipation (T : ℝ) (N : ℕ) : ℝ :=
  ∫ r : ℝ, ccmExponentialRampBulkDissipationDensity T N r

theorem ccmExponentialRampBulkDissipation_nonneg (T : ℝ) (N : ℕ) :
    0 ≤ ccmExponentialRampBulkDissipation T N :=
  integral_nonneg (ccmExponentialRampBulkDissipationDensity_nonneg T N)

def ccmExponentialRampAgeForceDensity (T : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  ccmExponentialRampDisplacementWeight r*ccmExponentialRampCenteredBulkField T N r

theorem ccmExponentialRampCurrent_source_dissipation (T : ℝ) (N : ℕ) (r : ℝ) :
    ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T) r+
      ccmExponentialRampBulkDissipationDensity T N r =
        ccmExponentialRampAgeForceDensity T N r+ccmExponentialRampTerminalEntropyDensity T N r := by
  rw [ccmExponentialRampCurrent_eq_centeredAge_bulk_terminal]
  unfold ccmExponentialRampBulkDissipationDensity ccmExponentialRampAgeForceDensity
    ccmExponentialRampTerminalEntropyDensity
  ring

theorem integrable_ccmExponentialRampAgeForceDensity (T : ℝ) (N : ℕ) :
    Integrable (ccmExponentialRampAgeForceDensity T N) := by
  refine (((integrable_ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T)).add
    (integrable_ccmExponentialRampBulkDissipationDensity T N)).sub
      (integrable_ccmExponentialRampTerminalEntropyDensity T N)).congr
        (Eventually.of_forall fun r => ?_)
  simp only [Pi.add_apply, Pi.sub_apply, ccmExponentialRampCurrent_source_dissipation,
    add_sub_cancel_right]

def ccmExponentialRampAgeForce (T : ℝ) (N : ℕ) : ℝ :=
  ∫ r : ℝ, ccmExponentialRampAgeForceDensity T N r

theorem ccmExponentialRampAction_source_dissipation (T : ℝ) (N : ℕ) :
    ccmActualHeadQuantileTestAction T N (ccmNormalizedExponentialRampTest T)+
      ccmExponentialRampBulkDissipation T N =
        ccmExponentialRampAgeForce T N+ccmExponentialRampTerminalEntropy T N := by
  unfold ccmActualHeadQuantileTestAction ccmExponentialRampBulkDissipation
    ccmExponentialRampAgeForce ccmExponentialRampTerminalEntropy
  rw [← integral_add (integrable_ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T))
      (integrable_ccmExponentialRampBulkDissipationDensity T N),
    ← integral_add (integrable_ccmExponentialRampAgeForceDensity T N)
      (integrable_ccmExponentialRampTerminalEntropyDensity T N)]
  exact integral_congr_ae (Eventually.of_forall (ccmExponentialRampCurrent_source_dissipation T N))

def ccmExponentialRampCellDisplacementMoment (n : ℕ) : ℝ :=
  ∫ r : ℝ, ccmOutgoingQuantileDisplacementCellDensity n r*ccmExponentialRampDisplacementWeight r

def ccmExponentialRampAgeMoment (T : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, ccmExponentialRampCellDisplacementMoment n*
    Real.exp ((Real.log n-T)/2)*(T-Real.log n)

private theorem integrable_cell_displacement (n : ℕ) :
    Integrable (fun r => ccmOutgoingQuantileDisplacementCellDensity n r*ccmExponentialRampDisplacementWeight r) :=
  integrable_ccmOutgoingQuantileCellDensity_continuousTest n
    ⟨ccmExponentialRampDisplacementWeight, by unfold ccmExponentialRampDisplacementWeight; fun_prop⟩

theorem ccmExponentialRampAgeForce_eq_cellMoments (T : ℝ) (N : ℕ) :
    ccmExponentialRampAgeForce T N = ∑ n ∈ Finset.range N,
      ccmExponentialRampCellDisplacementMoment n*(Real.exp ((Real.log n-T)/2)*(T-Real.log n-2)) := by
  have he (r : ℝ) : ccmExponentialRampAgeForceDensity T N r =
      ∑ n ∈ Finset.range N, (ccmOutgoingQuantileDisplacementCellDensity n r*ccmExponentialRampDisplacementWeight r)*
        (Real.exp ((Real.log n-T)/2)*(T-Real.log n-2)) := by
    unfold ccmExponentialRampAgeForceDensity ccmExponentialRampCenteredBulkField
      ccmActualHeadExponentialRampPositionField ccmExponentialRampBulkMassField
    rw [mul_sub, Finset.mul_sum, ← mul_assoc (ccmExponentialRampDisplacementWeight r) 2,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  unfold ccmExponentialRampAgeForce
  simp_rw [he]
  rw [integral_finsetSum _ (fun n _ => (integrable_cell_displacement n).mul_const _)]
  simp only [integral_mul_const, ccmExponentialRampCellDisplacementMoment]

theorem hasDerivAt_ccmExponentialRampAgeMoment (T : ℝ) (N : ℕ) :
    HasDerivAt (fun t => ccmExponentialRampAgeMoment t N)
      (-(1/2 : ℝ)*ccmExponentialRampAgeForce T N) T := by
  have hd (n : ℕ) : HasDerivAt
      (fun t : ℝ => ccmExponentialRampCellDisplacementMoment n*Real.exp ((Real.log n-t)/2)*(t-Real.log n))
      (-(1/2 : ℝ)*(ccmExponentialRampCellDisplacementMoment n*
        (Real.exp ((Real.log n-T)/2)*(T-Real.log n-2)))) T := by
    have he := (((hasDerivAt_id T).const_sub (Real.log n)).div_const 2).exp
    convert! (he.const_mul (ccmExponentialRampCellDisplacementMoment n)).mul
      ((hasDerivAt_id T).sub_const (Real.log n)) using 1
    simp only [id_eq]
    ring
  have h := HasDerivAt.fun_sum (u := Finset.range N) (fun n _ => hd n)
  simpa only [ccmExponentialRampAgeMoment, ccmExponentialRampAgeForce_eq_cellMoments,
    Finset.mul_sum] using h

/-- Exact arithmetic source/dissipation balance at fixed head; no moving-cutoff derivative is taken. -/
theorem ccmExponentialRampAction_ageMoment_balance (T : ℝ) (N : ℕ) :
    ccmActualHeadQuantileTestAction T N (ccmNormalizedExponentialRampTest T)+
      ccmExponentialRampBulkDissipation T N+
        2*deriv (fun t => ccmExponentialRampAgeMoment t N) T =
          ccmExponentialRampTerminalEntropy T N := by
  rw [(hasDerivAt_ccmExponentialRampAgeMoment T N).deriv]
  have h := ccmExponentialRampAction_source_dissipation T N
  linarith only [h]

theorem ccmExponentialRampAction_le_ageForce_add_entropy (T : ℝ) (N : ℕ) :
    ccmActualHeadQuantileTestAction T N (ccmNormalizedExponentialRampTest T) ≤
      ccmExponentialRampAgeForce T N+ccmExponentialRampTerminalEntropy T N := by
  have h := ccmExponentialRampAction_source_dissipation T N
  have hd := ccmExponentialRampBulkDissipation_nonneg T N
  linarith only [h, hd]

theorem ccmExponentialRampAgeForce_sub_dissipation_le_action (T : ℝ) (N : ℕ) :
    ccmExponentialRampAgeForce T N-ccmExponentialRampBulkDissipation T N ≤
      ccmActualHeadQuantileTestAction T N (ccmNormalizedExponentialRampTest T) := by
  have h := ccmExponentialRampAction_source_dissipation T N
  have hs := ccmExponentialRampTerminalEntropy_nonneg T N
  linarith only [h, hs]

/-- At physical heads this balance concerns the actual square-root-normalized deficit. -/
theorem normalized_chebyshevDeficit_ageMoment_balance (H : NNReal) :
    Real.exp (-(H : ℝ)/2)*ccmLogChebyshevDeficitPrimitive (H : ℝ)+
      ccmExponentialRampBulkDissipation (H : ℝ) (Nat.floor (Real.exp (H : ℝ))+1)+
        2*deriv (fun t => ccmExponentialRampAgeMoment t (Nat.floor (Real.exp (H : ℝ))+1)) (H : ℝ) =
          (H : ℝ)*Real.exp (-(H : ℝ)/2)+
            ccmExponentialRampTerminalEntropy (H : ℝ) (Nat.floor (Real.exp (H : ℝ))+1) := by
  have h := ccmExponentialRampAction_ageMoment_balance (H : ℝ) (Nat.floor (Real.exp (H : ℝ))+1)
  rw [ccmActualTimeExponentialRampAction_eq_normalizedDeficit] at h
  linarith only [h]

theorem ccmExponentialRampAgeMoment_head_succ (T : ℝ) (N : ℕ) :
    ccmExponentialRampAgeMoment T (N+1) = ccmExponentialRampAgeMoment T N+
      ccmExponentialRampCellDisplacementMoment N*Real.exp ((Real.log N-T)/2)*(T-Real.log N) := by
  exact Finset.sum_range_succ _ N

/-- Newly admitted atoms have age zero, so the age moment has no admission jump. -/
theorem ccmExponentialRampAgeMoment_admission (N : ℕ) :
    ccmExponentialRampAgeMoment (Real.log N) (N+1) = ccmExponentialRampAgeMoment (Real.log N) N := by
  simp [ccmExponentialRampAgeMoment_head_succ]

theorem ccmExponentialRampAction_head_succ (T : ℝ) (N : ℕ) :
    ccmActualHeadQuantileTestAction T (N+1) (ccmNormalizedExponentialRampTest T) =
      ccmActualHeadQuantileTestAction T N (ccmNormalizedExponentialRampTest T)-
        criticalMellinAtomWeight N*ccmNormalizedExponentialRampTest T (Real.log N) := by
  rw [ccmActualHeadQuantileTestAction_eq_source_balance,
    ccmActualHeadQuantileTestAction_eq_source_balance]
  simp only [ccmNormalizedExponentialRampTest_terminal, mul_zero, sub_zero, Finset.sum_range_succ]
  ring

theorem ccmExponentialRampAction_admission (N : ℕ) :
    ccmActualHeadQuantileTestAction (Real.log N) (N+1) (ccmNormalizedExponentialRampTest (Real.log N)) =
      ccmActualHeadQuantileTestAction (Real.log N) N (ccmNormalizedExponentialRampTest (Real.log N)) := by
  rw [ccmExponentialRampAction_head_succ, ccmNormalizedExponentialRampTest_terminal, mul_zero, sub_zero]

/-- The field is continuous at admission, but its fixed-head derivative acquires a literal prime-cell moment. -/
theorem ccmExponentialRampAgeMoment_derivative_admission (N : ℕ) :
    deriv (fun t => ccmExponentialRampAgeMoment t (N+1)) (Real.log N)-
      deriv (fun t => ccmExponentialRampAgeMoment t N) (Real.log N) =
        ccmExponentialRampCellDisplacementMoment N := by
  rw [(hasDerivAt_ccmExponentialRampAgeMoment (Real.log N) (N+1)).deriv,
    (hasDerivAt_ccmExponentialRampAgeMoment (Real.log N) N).deriv]
  simp only [ccmExponentialRampAgeForce_eq_cellMoments, Finset.sum_range_succ,
    sub_self, zero_div, Real.exp_zero, one_mul, zero_sub]
  ring

end RHTower
