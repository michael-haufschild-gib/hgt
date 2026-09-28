import GaloisForLFunctions.RHTower.CCMExponentialRampArithmeticEnergy

/-!
# The exact RH target in exponential-ramp action coordinates

The bounded deterministic transient does not change uniform boundedness.
Consequently the actual signed quantile action, at every physical cutoff, is
an exact RH criterion. Its boundedness is the remaining arithmetic question.
-/

noncomputable section
namespace RHTower

theorem abs_ccmActualTimeExponentialRampAction_le_normalizedDeficit_add_two (H : NNReal) :
    |ccmActualHeadQuantileTestAction (H : ℝ) (Nat.floor (Real.exp (H : ℝ))+1)
      (ccmNormalizedExponentialRampTest (H : ℝ))| ≤
        |Real.exp (-(H : ℝ)/2)*ccmLogChebyshevDeficitPrimitive (H : ℝ)|+2 := by
  rw [ccmActualTimeExponentialRampAction_eq_normalizedDeficit, mul_sub]
  exact (abs_sub _ _).trans (add_le_add le_rfl
    (by simpa only [mul_comm] using ccmExponentialRampTransient_bound H))

theorem abs_normalizedDeficit_le_ccmActualTimeExponentialRampAction_add_two (H : NNReal) :
    |Real.exp (-(H : ℝ)/2)*ccmLogChebyshevDeficitPrimitive (H : ℝ)| ≤
      |ccmActualHeadQuantileTestAction (H : ℝ) (Nat.floor (Real.exp (H : ℝ))+1)
        (ccmNormalizedExponentialRampTest (H : ℝ))|+2 := by
  have he : Real.exp (-(H : ℝ)/2)*ccmLogChebyshevDeficitPrimitive (H : ℝ) =
      ccmActualHeadQuantileTestAction (H : ℝ) (Nat.floor (Real.exp (H : ℝ))+1)
        (ccmNormalizedExponentialRampTest (H : ℝ)) + (H : ℝ)*Real.exp (-(H : ℝ)/2) := by
    rw [ccmActualTimeExponentialRampAction_eq_normalizedDeficit]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add le_rfl (ccmExponentialRampTransient_bound H))

private theorem exp_half_cancel (T : ℝ) : Real.exp (T/2)*Real.exp (-T/2) = 1 := by
  rw [← Real.exp_add, show T/2+(-T/2) = 0 by ring, Real.exp_zero]

/-- Exact RH equivalence for the literal prime-plus-terminal action, with no crossing or energy premise. -/
theorem riemannHypothesis_iff_exponentialRampAction_uniformBound :
    RiemannHypothesis ↔ ∃ B : ℝ, 0 ≤ B ∧ ∀ H : NNReal,
      |ccmActualHeadQuantileTestAction (H : ℝ) (Nat.floor (Real.exp (H : ℝ))+1)
        (ccmNormalizedExponentialRampTest (H : ℝ))| ≤ B := by
  constructor
  · intro hRH
    obtain ⟨B, hB, hbound⟩ := riemannHypothesis_iff_logChebyshevDeficitPrimitive_bound.mp hRH
    refine ⟨B+2, by linarith, fun H => ?_⟩
    apply (abs_ccmActualTimeExponentialRampAction_le_normalizedDeficit_add_two H).trans
    apply add_le_add _ le_rfl
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-(H : ℝ)/2)*(B*Real.exp ((H : ℝ)/2)) :=
        mul_le_mul_of_nonneg_left (hbound (H : ℝ) H.coe_nonneg) (Real.exp_pos _).le
      _ = B := by
        calc
          _ = B*(Real.exp ((H : ℝ)/2)*Real.exp (-(H : ℝ)/2)) := by ring
          _ = B := by rw [exp_half_cancel, mul_one]
  · rintro ⟨B, hB, hbound⟩
    apply riemannHypothesis_iff_logChebyshevDeficitPrimitive_bound.mpr
    refine ⟨B+2, by linarith, fun T hT => ?_⟩
    let H := NNReal.mk T hT
    have hnorm := (abs_normalizedDeficit_le_ccmActualTimeExponentialRampAction_add_two H).trans
      (add_le_add (hbound H) le_rfl)
    change |Real.exp (-T/2)*ccmLogChebyshevDeficitPrimitive T| ≤ B+2 at hnorm
    rw [abs_mul, abs_of_pos (Real.exp_pos _)] at hnorm
    calc
      |ccmLogChebyshevDeficitPrimitive T| =
          Real.exp (T/2)*(Real.exp (-T/2)*|ccmLogChebyshevDeficitPrimitive T|) := by
        rw [← mul_assoc, exp_half_cancel, one_mul]
      _ ≤ Real.exp (T/2)*(B+2) := mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le
      _ = (B+2)*Real.exp (T/2) := mul_comm _ _

end RHTower
