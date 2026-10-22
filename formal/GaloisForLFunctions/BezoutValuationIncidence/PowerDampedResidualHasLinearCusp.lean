import GaloisForLFunctions.BezoutValuationIncidence.DampedChebyshevTangentFormOfTheReceiver
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDerivativeBoundary
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusCriterion

/-!
# A linear cusp in the literal power-damped residual

A critical zeta zero detects the residual at a distance equal to the damping.
The exact step-source Mellin identity retains the fractional-part correction.
The conclusion concerns finite horizons and assumes neither RH nor admission.
-/

open MeasureTheory Set Filter Topology Complex Finset RHTower
open GaloisForLFunctions.NymanMellin
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The original residual, with no change of weight or centering. -/
def pmPowerDampedDualResidual (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T, (pmPowerDampedCenteredDivisorPrefix ε n - 1) ^ 2 /
    ((n : ℝ) * ((n : ℝ) + 1))

private def cuspStepTail (a : ℕ → ℝ) : ℝ → ℂ :=
  (Ici (1 : ℝ)).indicator (fun x => (a ⌊x⌋₊ : ℂ))

private def cuspStepHead (a : ℕ → ℝ) (u : ℝ) : ℂ := cuspStepTail a (1 / u)

private theorem cuspStepHead_zero (a : ℕ → ℝ) {u : ℝ} (hu : 1 < u) :
    cuspStepHead a u = 0 := by
  apply indicator_of_notMem
  exact not_le.mpr ((div_lt_one (lt_trans zero_lt_one hu)).mpr hu)

private theorem cuspStepHead_eq (a : ℕ → ℝ) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    cuspStepHead a u = (a ⌊1 / u⌋₊ : ℂ) := by
  apply indicator_of_mem
  exact (le_div_iff₀ hu).mpr (by simpa using hu1)

private theorem measurable_cuspStepHead (a : ℕ → ℝ) : Measurable (cuspStepHead a) :=
  (((Complex.measurable_ofReal.comp
    ((measurable_of_countable a).comp Nat.measurable_floor)).indicator measurableSet_Ici).comp
      (measurable_const.div measurable_id))

private theorem cuspStepTail_energy (a : ℕ → ℝ) :
    (fun x : ℝ => ‖cuspStepTail a x‖ ^ 2 / x ^ 2) =
      (Ici (1 : ℝ)).indicator
        (fun x : ℝ => a ⌊x⌋₊ * a ⌊x⌋₊ * (x⁻¹) ^ 2) := by
  funext x
  by_cases hx : x ∈ Ici (1 : ℝ)
  · simp only [cuspStepTail, indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, div_eq_mul_inv, inv_pow, sq]
  · simp [cuspStepTail, indicator_of_notMem hx]

private theorem cuspStepHead_integrable {a : ℕ → ℝ}
    (ha : Summable (fun n : ℕ => a (n + 1) ^ 2 /
      (((n : ℝ) + 1) * ((n : ℝ) + 2)))) :
    MemLp (cuspStepHead a) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  rw [memLp_two_iff_integrable_sq_norm (measurable_cuspStepHead a).aestronglyMeasurable]
  change IntegrableOn (fun u => ‖cuspStepTail a (1 / u)‖ ^ 2) (Ioi (0 : ℝ))
  rw [pm_integrable_normSq_reciprocal_iff, cuspStepTail_energy]
  have hi := (integrableOn_stepEnergy_iff_summable a).mpr ha
  have hi' : IntegrableOn (fun x : ℝ => a ⌊x⌋₊ * a ⌊x⌋₊ * (x⁻¹) ^ 2) (Ici 1) :=
    integrableOn_Ici_iff_integrableOn_Ioi.mpr hi
  exact ((integrable_indicator_iff measurableSet_Ici).mpr hi').mono_measure
    Measure.restrict_le_self

private theorem cuspStepHead_energy {a : ℕ → ℝ}
    (ha : Summable (fun n : ℕ => a (n + 1) ^ 2 /
      (((n : ℝ) + 1) * ((n : ℝ) + 2)))) :
    (∫ u in Ioi (0 : ℝ), ‖cuspStepHead a u‖ ^ 2) =
      ∑' n : ℕ, a (n + 1) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  change (∫ u in Ioi (0 : ℝ), ‖cuspStepTail a (1 / u)‖ ^ 2) = _
  rw [pm_integral_normSq_reciprocal, cuspStepTail_energy,
    setIntegral_indicator measurableSet_Ici,
    inter_eq_right.mpr (show Ici (1 : ℝ) ⊆ Ioi 0 from fun x hx => lt_of_lt_of_le zero_lt_one hx),
    integral_Ici_eq_integral_Ioi]
  have hi := (integrableOn_stepEnergy_iff_summable a).mpr ha
  have hu : IntegrableOn (fun x : ℝ => a ⌊x⌋₊ * a ⌊x⌋₊ * (x⁻¹) ^ 2)
      (⋃ n : ℕ, tailCell n) := by simpa only [iUnion_tailCell] using hi
  have hh := hasSum_integral_iUnion measurableSet_tailCell pairwise_disjoint_tailCell hu
  simp_rw [integral_tailCell_stepGramIntegrand] at hh
  rw [iUnion_tailCell] at hh
  simpa only [sq] using hh.tsum_eq.symm

/-- The literal residual on the reciprocal unit interval. -/
def pmPowerDampedResidualHead (ε : ℝ) : ℝ → ℂ :=
  cuspStepHead (fun n => pmPowerDampedCenteredDivisorPrefix ε n - 1)

private theorem dualResidual_eq_range (ε : ℝ) (T : ℕ) :
    pmPowerDampedDualResidual ε T =
      ∑ n ∈ range T, (pmPowerDampedCenteredDivisorPrefix ε (n + 1) - 1) ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  unfold pmPowerDampedDualResidual
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, sum_Icc_succ_top (by omega), ih]
    norm_num [Nat.cast_add, Nat.cast_one, add_assoc]

private theorem residualHead_of_budget {ε C : ℝ}
    (hC : ∀ T : ℕ, pmPowerDampedDualResidual ε T ≤ C) :
    MemLp (pmPowerDampedResidualHead ε) 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      (∫ u in Ioi (0 : ℝ), ‖pmPowerDampedResidualHead ε u‖ ^ 2) ≤ C := by
  have hn (n : ℕ) : 0 ≤ (pmPowerDampedCenteredDivisorPrefix ε (n + 1) - 1) ^ 2 /
      (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by positivity
  have hs : Summable (fun n : ℕ => (pmPowerDampedCenteredDivisorPrefix ε (n + 1) - 1) ^ 2 /
      (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
    apply summable_of_sum_range_le hn
    intro T
    simpa only [dualResidual_eq_range] using hC T
  refine ⟨cuspStepHead_integrable hs, ?_⟩
  rw [pmPowerDampedResidualHead, cuspStepHead_energy hs]
  exact le_of_tendsto hs.hasSum.tendsto_sum_nat (Eventually.of_forall fun T => by
    simpa only [dualResidual_eq_range] using hC T)

private theorem residualHead_eq_centered {ε : ℝ} (hε : 0 < ε) {u : ℝ} (hu : 0 < u) :
    pmPowerDampedResidualHead ε u = pmPowerDampedCenteredSource ε u +
      pmPowerDampedDivisorDensity ε * nymanGen 1 u -
        (if u ≤ 1 then (1 : ℂ) else 0) := by
  have hfract := pmPowerDampedDivisorRemainder_eq_centered_prefix hε
    (one_div_pos.mpr hu).le
  change pmPowerDampedResidualHead ε u = pmPowerDampedDivisorRemainder ε (1 / u) + _ - _
  rw [hfract]
  simp only [nymanGen, one_mul]
  by_cases hu1 : u ≤ 1
  · rw [if_pos hu1, pmPowerDampedResidualHead, cuspStepHead_eq _ hu hu1]
    push_cast
    ring
  · rw [if_neg hu1, pmPowerDampedResidualHead, cuspStepHead_zero _ (lt_of_not_ge hu1),
      Nat.floor_eq_zero.mpr ((div_lt_one hu).mpr (lt_of_not_ge hu1))]
    simp [pmPowerDampedCenteredDivisorPrefix]

private theorem residualHead_dyadic {ε : ℝ} (hε : 0 < ε) {u : ℝ} (hu : 0 < u) :
    pmPowerDampedResidualHead ε u - 2 * pmPowerDampedResidualHead ε (2 * u) =
      pmPowerDampedFermiSource ε u + pmPowerDampedDivisorDensity ε * fermiNymanGen 1 u -
        pmSupportedDyadicHaar u := by
  rw [residualHead_eq_centered hε hu, residualHead_eq_centered hε (by positivity),
    pmPowerDampedFermiSource_eq_centered_difference ε hu,
    pmSupportedDyadicHaar_eq_cutoffs hu]
  have hc : (if (2 : ℝ) * u ≤ 1 then (1 : ℂ) else 0) =
      (if u ≤ 1 / 2 then (1 : ℂ) else 0) := by
    congr 1
    constructor <;> intro h <;> linarith
  rw [hc]
  simp only [fermiNymanGen, nymanGen, one_mul, mul_one, mul_assoc]
  ring

end
end GaloisForLFunctions.BezoutValuationIncidence
