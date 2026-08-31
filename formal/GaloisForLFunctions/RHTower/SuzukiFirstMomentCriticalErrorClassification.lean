import GaloisForLFunctions.RHTower.SuzukiFirstMomentTriangularAbelTransfer
import GaloisForLFunctions.RHTower.CCMFUSuzukiCoherentBoundaryTransport
import GaloisForLFunctions.RHTower.CCMFUSuzukiSelbergSquareRootAbelAction
import GaloisForLFunctions.RHTower.CCMUnitRieszSharpPoleClassification
import GaloisForLFunctions.RHTower.PrimeAmplitudeUniformBound

/-!
# Critical-error classification of the Suzuki first-moment route

The event-label-weighted Suzuki curvature first-moment bound and uniform central unit-Riesz
barycenter bound are equivalent.  The exact incoming/outgoing boundary jump then classifies either
condition as RH together with a square-root bound for the literal Chebyshev remainder.  Thus the
central-source proposal contains an independent critical-error burden beyond RH.
-/

open Set
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.RHTower

noncomputable section

/-- Uniform boundedness of the critical-normalized Chebyshev error on the natural log mesh. -/
def CriticalMellinNormalizedChebyshevErrorLogNatBounded : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 3 ≤ M →
    |criticalMellinNormalizedChebyshevError (Real.log (M : ℝ))| ≤ C

/-- Square-root boundedness of the literal discrete Chebyshev remainder. -/
def PsiRemainderSquareRootBounded : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 3 ≤ M →
    |psiRemainder M| ≤ C * Real.sqrt (M : ℝ)

/-- The analytic critical-error condition is exactly the arithmetic square-root remainder bound. -/
theorem normalizedErrorLogNatBounded_iff_psiRemainderSquareRootBounded :
    CriticalMellinNormalizedChebyshevErrorLogNatBounded ↔
      PsiRemainderSquareRootBounded := by
  constructor
  · rintro ⟨C, hC0, herror⟩
    refine ⟨C, hC0, ?_⟩
    intro M hM
    have hMpos : (0 : ℝ) < M := by positivity
    have hsqrtpos : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMpos
    have h := herror M hM
    rw [normalizedChebyshevError_log_nat_eq_psiRemainder_div_sqrt (by omega),
      abs_div, abs_of_pos hsqrtpos] at h
    exact (div_le_iff₀ hsqrtpos).mp h
  · rintro ⟨C, hC0, hremainder⟩
    refine ⟨C, hC0, ?_⟩
    intro M hM
    have hMpos : (0 : ℝ) < M := by positivity
    have hsqrtpos : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMpos
    rw [normalizedChebyshevError_log_nat_eq_psiRemainder_div_sqrt (by omega),
      abs_div, abs_of_pos hsqrtpos]
    exact (div_le_iff₀ hsqrtpos).2 (hremainder M hM)

/-- The endpoint atom is uniformly bounded at the critical half-density. -/
theorem abs_vonMangoldt_div_sqrt_le_two {M : ℕ} (hM : 2 ≤ M) :
    |ArithmeticFunction.vonMangoldt M / Real.sqrt (M : ℝ)| ≤ 2 := by
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by positivity
  have hsqrtpos : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMpos
  have hv0 : 0 ≤ ArithmeticFunction.vonMangoldt M :=
    ArithmeticFunction.vonMangoldt_nonneg
  rw [abs_of_nonneg (div_nonneg hv0 hsqrtpos.le)]
  apply (div_le_iff₀ hsqrtpos).2
  calc
    ArithmeticFunction.vonMangoldt M ≤ Real.log (M : ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log
    _ ≤ 2 * (Real.sqrt (M : ℝ) - 1) :=
      log_le_two_mul_sqrt_sub_one (by linarith)
    _ ≤ 2 * Real.sqrt (M : ℝ) := by linarith

/-- Reverse source landing: a linear Suzuki first moment uniformly bounds the central unit-Riesz
barycenter.  Together with the existing forward landing, this closes the source equivalence. -/
theorem unitRieszCentralBarycenterNaturalBound_of_weightedFirstMomentLinearBound
    (hfirst : CCMFUSuzukiWeightedCurvatureFirstMomentLinearBound) :
    CCMUnitRieszCentralBarycenterNaturalBound := by
  obtain ⟨C, hC0, hprefix⟩ := hfirst
  refine ⟨C + 13, add_nonneg hC0 (by norm_num), ?_⟩
  intro N hN
  let X : ℝ := (N + 2 : ℕ)
  have hX1 : 1 ≤ X := by
    dsimp only [X]
    exact_mod_cast (by omega : 1 ≤ N + 2)
  have hX0 : 0 ≤ X := zero_le_one.trans hX1
  have hXpos : 0 < X := zero_lt_one.trans_le hX1
  have hsqrt : Real.sqrt X ≤ X := by
    rw [Real.sqrt_le_iff]
    exact ⟨hX0, by nlinarith⟩
  have hlanding := unitRiesz_center_eq_weightedSignedCurvature_add_arch hN
  have hrearrange : unitRieszCompletedCoherentBarycenter (N + 2) 0 =
      suzukiCheckpointWeightedSignedCurvaturePrefix N / X +
        suzukiCheckpointWeightedArchRenormalization N / X := by
    rw [← add_div]
    apply (eq_div_iff (ne_of_gt hXpos)).2
    linarith
  rw [hrearrange]
  calc
    |suzukiCheckpointWeightedSignedCurvaturePrefix N / X +
        suzukiCheckpointWeightedArchRenormalization N / X| ≤
      |suzukiCheckpointWeightedSignedCurvaturePrefix N / X| +
        |suzukiCheckpointWeightedArchRenormalization N / X| := abs_add_le _ _
    _ = |suzukiCheckpointWeightedSignedCurvaturePrefix N| / X +
        |suzukiCheckpointWeightedArchRenormalization N| / X := by
          rw [abs_div, abs_div, abs_of_pos hXpos]
    _ ≤ (C * X) / X + (8 * Real.sqrt X + 5) / X := by
      exact add_le_add
        (div_le_div_of_nonneg_right (by simpa only [X] using hprefix N hN) hX0)
        (div_le_div_of_nonneg_right
          (by simpa only [X] using abs_suzukiCheckpointWeightedArchRenormalization_le hN) hX0)
    _ = C + (8 * Real.sqrt X + 5) / X := by field_simp
    _ ≤ C + 13 := by
      have : 8 * Real.sqrt X + 5 ≤ 13 * X := by nlinarith
      have hdiv : (8 * Real.sqrt X + 5) / X ≤ 13 := by
        exact (div_le_iff₀ hXpos).2 (by nlinarith)
      linarith

/-- Exact equivalence of the two proposed source-side producers. -/
theorem weightedFirstMomentLinearBound_iff_unitRieszCentralBarycenterNaturalBound :
    CCMFUSuzukiWeightedCurvatureFirstMomentLinearBound ↔
      CCMUnitRieszCentralBarycenterNaturalBound := by
  exact ⟨unitRieszCentralBarycenterNaturalBound_of_weightedFirstMomentLinearBound,
    weightedFirstMomentLinearBound_of_unitRieszCentralBarycenterNaturalBound⟩

/-- Reindexed exact boundary jump at every aperture where the central criterion is stated. -/
theorem unitRieszCoherentBoundaryJump_eq_normalizedChebyshevError_of_three_le
    {M : ℕ} (hM : 3 ≤ M) :
    unitRieszCoherentCompletedOutgoingCharge M -
        unitRieszCompletedCoherentBarycenter M 0 +
        ArithmeticFunction.vonMangoldt M / Real.sqrt (M : ℝ) =
      criticalMellinNormalizedChebyshevError (Real.log (M : ℝ)) := by
  have hEq : M - 3 + 3 = M := Nat.sub_add_cancel hM
  simpa only [hEq] using
    unitRieszCoherentBoundaryJump_eq_normalizedChebyshevError (M - 3)

/-- Exact classification of the central unit-Riesz proposal: RH controls the outgoing source, but
boundedness of the incoming center additionally requires bounded critical Chebyshev error. -/
theorem unitRieszCentralBarycenterNaturalBound_iff_rh_and_normalizedErrorBounded :
    CCMUnitRieszCentralBarycenterNaturalBound ↔
      RiemannHypothesis ∧ CriticalMellinNormalizedChebyshevErrorLogNatBounded := by
  constructor
  · intro hcenterBound
    have hRH : RiemannHypothesis :=
      riemannHypothesis_of_unitRieszCentralBarycenterNaturalBound hcenterBound
    refine ⟨hRH, ?_⟩
    obtain ⟨C, hC0, hcenter⟩ := hcenterBound
    refine ⟨C + 4, add_nonneg hC0 (by norm_num), ?_⟩
    intro M hM
    have hcenterM : |unitRieszCompletedCoherentBarycenter M 0| ≤ C := by
      have h := hcenter (M - 2) (by omega)
      have hEq : M - 2 + 2 = M := Nat.sub_add_cancel (by omega)
      simpa only [hEq] using h
    have hout : |unitRieszCoherentCompletedOutgoingCharge M| ≤ 2 :=
      (abs_unitRieszCoherentCompletedOutgoingCharge_lt_two_of_riemannHypothesis
        hRH (by omega)).le
    have hend := abs_vonMangoldt_div_sqrt_le_two (M := M) (by omega)
    have hboundary :=
      unitRieszCoherentBoundaryJump_eq_normalizedChebyshevError_of_three_le hM
    rw [← hboundary]
    calc
      |unitRieszCoherentCompletedOutgoingCharge M -
          unitRieszCompletedCoherentBarycenter M 0 +
          ArithmeticFunction.vonMangoldt M / Real.sqrt (M : ℝ)| ≤
        |unitRieszCoherentCompletedOutgoingCharge M| +
          |unitRieszCompletedCoherentBarycenter M 0| +
          |ArithmeticFunction.vonMangoldt M / Real.sqrt (M : ℝ)| := by
            have hsub := abs_sub (unitRieszCoherentCompletedOutgoingCharge M)
              (unitRieszCompletedCoherentBarycenter M 0)
            have hadd := abs_add_le
              (unitRieszCoherentCompletedOutgoingCharge M -
                unitRieszCompletedCoherentBarycenter M 0)
              (ArithmeticFunction.vonMangoldt M / Real.sqrt (M : ℝ))
            linarith
      _ ≤ C + 4 := by linarith
  · rintro ⟨hRH, herrorBound⟩
    obtain ⟨E, hE0, herror⟩ := herrorBound
    refine ⟨E + 4, add_nonneg hE0 (by norm_num), ?_⟩
    intro N hN
    let M : ℕ := N + 2
    have hM : 3 ≤ M := by dsimp only [M]; omega
    have hout : |unitRieszCoherentCompletedOutgoingCharge M| ≤ 2 :=
      (abs_unitRieszCoherentCompletedOutgoingCharge_lt_two_of_riemannHypothesis
        hRH (by omega)).le
    have hend := abs_vonMangoldt_div_sqrt_le_two (M := M) (by omega)
    have herr := herror M hM
    have hboundary :=
      unitRieszCoherentBoundaryJump_eq_normalizedChebyshevError_of_three_le hM
    have hrearrange : unitRieszCompletedCoherentBarycenter M 0 =
        unitRieszCoherentCompletedOutgoingCharge M +
          ArithmeticFunction.vonMangoldt M / Real.sqrt (M : ℝ) -
          criticalMellinNormalizedChebyshevError (Real.log (M : ℝ)) := by
      linarith
    change |unitRieszCompletedCoherentBarycenter M 0| ≤ E + 4
    rw [hrearrange]
    calc
      |unitRieszCoherentCompletedOutgoingCharge M +
          ArithmeticFunction.vonMangoldt M / Real.sqrt (M : ℝ) -
          criticalMellinNormalizedChebyshevError (Real.log (M : ℝ))| ≤
        |unitRieszCoherentCompletedOutgoingCharge M| +
          |ArithmeticFunction.vonMangoldt M / Real.sqrt (M : ℝ)| +
          |criticalMellinNormalizedChebyshevError (Real.log (M : ℝ))| := by
            have hadd := abs_add_le (unitRieszCoherentCompletedOutgoingCharge M)
              (ArithmeticFunction.vonMangoldt M / Real.sqrt (M : ℝ))
            have hsub := abs_sub
              (unitRieszCoherentCompletedOutgoingCharge M +
                ArithmeticFunction.vonMangoldt M / Real.sqrt (M : ℝ))
              (criticalMellinNormalizedChebyshevError (Real.log (M : ℝ)))
            linarith
      _ ≤ E + 4 := by linarith

/-- The weighted Suzuki first moment has exactly the same RH-plus-critical-error content. -/
theorem weightedFirstMomentLinearBound_iff_rh_and_normalizedErrorBounded :
    CCMFUSuzukiWeightedCurvatureFirstMomentLinearBound ↔
      RiemannHypothesis ∧ CriticalMellinNormalizedChebyshevErrorLogNatBounded := by
  rw [weightedFirstMomentLinearBound_iff_unitRieszCentralBarycenterNaturalBound,
    unitRieszCentralBarycenterNaturalBound_iff_rh_and_normalizedErrorBounded]

/-- Literal arithmetic classification of the first-moment route. -/
theorem weightedFirstMomentLinearBound_iff_rh_and_psiRemainderSquareRootBounded :
    CCMFUSuzukiWeightedCurvatureFirstMomentLinearBound ↔
      RiemannHypothesis ∧ PsiRemainderSquareRootBounded := by
  rw [weightedFirstMomentLinearBound_iff_rh_and_normalizedErrorBounded,
    normalizedErrorLogNatBounded_iff_psiRemainderSquareRootBounded]

end

end RHTower
